#pragma once
#include "lir.h"

typedef struct {
  u32 set;
  u32 len;
} GprSet;

// Graph represented as a adjacency matrix (M(i,j) = 1 if there is an edge
// between i and j), stored as a bitfield of the right-upper half (without the
// diagonal).
// Each row is a memory location (see above field).
typedef PgAdjacencyMatrix InterferenceGraph;

typedef struct {
  Register return_value;
  RegisterSlice caller_saved;
  RegisterSlice callee_saved;
  RegisterSlice calling_convention;
  Register syscall_num;
  RegisterSlice syscall_calling_convention;
  Register syscall_ret;
  Register stack_pointer;
  Register base_pointer;
} Architecture;

typedef enum {
  ASM_SECTION_FLAG_NONE = 0,
  ASM_SECTION_FLAG_GLOBAL = 1 << 0,
} AsmCodeSectionFlag;

typedef struct {
  PgString name;
  AsmCodeSectionFlag flags;
  PgAnyDyn instructions;
} AsmCodeSection;
PG_SLICE(AsmCodeSection) AsmCodeSectionSlice;
PG_DYN(AsmCodeSection) AsmCodeSectionDyn;

typedef enum {
  ASM_CONSTANT_KIND_NONE,
  ASM_CONSTANT_KIND_U64,
  ASM_CONSTANT_KIND_BYTES,
} AsmConstantKind;

typedef struct {
  PgString name;
  u64 address_absolute;
  AsmConstantKind kind;
  union {
    u64 n64;
    PgString bytes;
  };
} AsmConstant;
PG_SLICE(AsmConstant) AsmConstantSlice;
PG_DYN(AsmConstant) AsmConstantDyn;

typedef struct {
  AsmCodeSectionDyn text;
  AsmConstantDyn rodata;
  u64 vm_start;
  LabelAddressDyn label_addresses;
  LabelAddressDyn jumps_to_backpatch;

  PgString file_path;
} AsmProgram;

typedef struct AsmEmitter AsmEmitter;

#define ASM_EMITTER_FIELDS                                                     \
  void (*emit_program)(AsmEmitter * asm_emitter,                               \
                       LirInstructionSlice lir_instructions, bool verbose,     \
                       PgAllocator *allocator);                                \
  Pgu8Slice (*encode_program_text)(AsmEmitter * asm_emitter,                   \
                                   PgAllocator * allocator);                   \
  void (*print_program)(AsmEmitter asm_emitter);                               \
  Register (*map_constraint_to_register)(                                      \
      AsmEmitter * asm_emitter, LirVirtualRegisterConstraint constraint);      \
  void (*print_register)(Register reg);                                        \
                                                                               \
  IrMetadataDyn metadata;                                                      \
  u32 stack_base_pointer_offset;                                               \
  u32 stack_base_pointer_max_offset;                                           \
  InterferenceGraph interference_graph;                                        \
  LirEmitter *lir_emitter;                                                     \
  u32 gprs_count;                                                              \
  AsmProgram program;

struct AsmEmitter {
  ASM_EMITTER_FIELDS
};

static void asm_gpr_set_add(GprSet *set, u32 val) {
  PG_ASSERT(set->len > 0);
  PG_ASSERT(val < set->len);
  set->set |= 1 << val;
}

[[nodiscard]]
static Register asm_gpr_pop_first_unset(GprSet *set) {
  PG_ASSERT(set->len > 0);

  u32 first_set_bit = (u32)__builtin_ffs((int)~set->set);

  if (first_set_bit > set->len) {
    return (Register){0};
  }

  if (0 != first_set_bit) {
    asm_gpr_set_add(set, first_set_bit - 1);
  }

  return (Register){.value = first_set_bit};
}

static void asm_print_interference_graph(InterferenceGraph graph,
                                         IrMetadataDyn metadata) {

  printf("nodes_count=%lu\n", graph.nodes_count);

  for (u64 row = 0; row < graph.nodes_count; row++) {
    for (u64 col = 0; col < row; col++) {
      bool edge = pg_adjacency_matrix_has_edge(graph, row, col);
      if (!edge) {
        continue;
      }

      IrMetadata a_meta = PG_SLICE_AT(metadata, row);
      IrMetadata b_meta = PG_SLICE_AT(metadata, col);
      ir_print_var(a_meta);
      printf(" -> ");
      ir_print_var(b_meta);
      printf("\n");
    }
  }
}

static void asm_sanity_check_interference_graph(InterferenceGraph graph,
                                                IrMetadataDyn metadata,
                                                bool colored) {
  PG_ASSERT(metadata.len != 0);
  PG_ASSERT(metadata.len == graph.nodes_count);

  if (1 == graph.nodes_count) {
    return;
  }

  if (colored) {
    for (u64 i = 1; i < metadata.len; i++) {
      MemoryLocation mem_loc = PG_SLICE_AT(metadata, i).memory_location;
      switch (mem_loc.kind) {
      case MEMORY_LOCATION_KIND_STATUS_REGISTER:
      case MEMORY_LOCATION_KIND_REGISTER:
        PG_ASSERT(mem_loc.reg.value);
        break;
      case MEMORY_LOCATION_KIND_STACK:
        PG_ASSERT(mem_loc.base_pointer_offset != 0);
        break;
      case MEMORY_LOCATION_KIND_NONE:
      default:
        PG_ASSERT(0);
      }
    }
  }

  // TODO: more checks.
}

[[nodiscard]]
static InterferenceGraph asm_build_interference_graph(IrMetadataDyn metadata,
                                                      PgAllocator *allocator) {
  InterferenceGraph graph = {0};

  if (1 == metadata.len) {
    return graph;
  }

  graph = pg_adjacency_matrix_make(metadata.len, allocator);
  PG_ASSERT(metadata.len == graph.nodes_count);

  for (u64 i = 0; i < metadata.len; i++) {
    IrMetadata meta = PG_SLICE_AT(metadata, i);
#if 0
    PG_ASSERT(!meta.tombstone);
#endif
    PG_ASSERT(meta.lifetime_start.value <= meta.lifetime_end.value);
    PG_ASSERT(i == 0 || meta.virtual_register.value);

    // Interferes with no one (unused).
    if (meta.lifetime_start.value == meta.lifetime_end.value) {
      continue;
    }

    for (u64 j = i + 1; j < metadata.len; j++) {
      IrMetadata it = PG_SLICE_AT(metadata, j);
      PG_ASSERT(it.lifetime_start.value <= it.lifetime_end.value);
#if 0
      PG_ASSERT(!it.tombstone);
#endif

      PG_ASSERT(meta.virtual_register.value != it.virtual_register.value);

      // Interferes with no one (unused).
      if (it.lifetime_start.value == it.lifetime_end.value) {
        continue;
      }

      // `it` strictly before `meta`.
      if (it.lifetime_end.value < meta.lifetime_start.value) {
        continue;
      }

      // `it` strictly after `meta`.
      if (meta.lifetime_end.value < it.lifetime_start.value) {
        continue;
      }

      // Interferes: add an edge between the two nodes.

      pg_adjacency_matrix_add_edge(&graph, j, i);
    }
  }

  return graph;
}

[[nodiscard]]
static u32 asm_reserve_stack_slot(AsmEmitter *emitter, u32 slot_size) {
  emitter->stack_base_pointer_offset += slot_size;
  emitter->stack_base_pointer_max_offset =
      PG_MAX(emitter->stack_base_pointer_max_offset,
             emitter->stack_base_pointer_offset);

  PG_ASSERT(emitter->stack_base_pointer_offset > 0);
  return emitter->stack_base_pointer_offset;
}

[[nodiscard]]
static bool asm_must_spill(AsmEmitter emitter, InterferenceNodeIndex node_idx,
                           u64 neighbors_count) {
  bool virt_reg_addressable = PG_SLICE_AT(emitter.metadata, node_idx.value)
                                  .virtual_register.addressable;

  bool needs_spill =
      neighbors_count >= emitter.gprs_count || virt_reg_addressable;

  return needs_spill;
}

static void asm_spill_node(AsmEmitter *emitter,
                           InterferenceNodeIndex node_idx) {

  MemoryLocation *mem_loc =
      &PG_SLICE_AT(emitter->metadata, node_idx.value).memory_location;
  PG_ASSERT(MEMORY_LOCATION_KIND_NONE == mem_loc->kind);

  mem_loc->kind = MEMORY_LOCATION_KIND_STACK;
  u32 rbp_offset =
      asm_reserve_stack_slot((AsmEmitter *)emitter, sizeof(u64) /*FIXME*/);
  mem_loc->base_pointer_offset = (i32)rbp_offset;
}

// TODO: Better strategy to pick which virtual registers to spill.
// For now we simply spill them all if they have more neighbors than there are
// GPRs, on a 'first encounter' basis.
static void
asm_color_spill_remaining_nodes_in_graph(AsmEmitter *emitter,
                                         InterferenceNodeIndexDyn *stack,
                                         PgString nodes_tombstones_bitfield) {
  for (u64 row = 0; row < emitter->interference_graph.nodes_count; row++) {
    if (pg_bitfield_get(nodes_tombstones_bitfield, row)) {
      continue;
    }

    u64 neighbors_count =
        pg_adjacency_matrix_count_neighbors(emitter->interference_graph, row);

    pg_adjacency_matrix_remove_node(&emitter->interference_graph, row);
    pg_bitfield_set(nodes_tombstones_bitfield, row, true);

    InterferenceNodeIndex node_idx = {(u32)row};
    if (!asm_must_spill(*emitter, node_idx, neighbors_count)) {
      PG_ASSERT(stack->len < emitter->interference_graph.nodes_count);
      *PG_DYN_PUSH_WITHIN_CAPACITY(stack) = node_idx;
      continue;
    }

    // Need to spill.
    asm_spill_node(emitter, node_idx);
  }
}

static Register asm_get_free_register(GprSet regs) {
  // TODO: Smarter free register selection.
  // E.g. favor caller-saved registers, etc.
  Register res = asm_gpr_pop_first_unset(&regs);
  PG_ASSERT(res.value && "todo: spill");
  return res;
}

static void asm_color_do_pre_coloring(AsmEmitter *emitter,
                                      PgString tombstones_bitfield) {
  // Dummy.
  pg_bitfield_set(tombstones_bitfield, 0, true);

  for (u64 row = 0; row < emitter->interference_graph.nodes_count; row++) {
    InterferenceNodeIndex node_idx = {(u32)row};
    IrMetadata *meta = PG_SLICE_AT_PTR(&emitter->metadata, node_idx.value);
    switch (meta->virtual_register.constraint) {
    case LIR_VIRT_REG_CONSTRAINT_NONE:
      break;
    case LIR_VIRT_REG_CONSTRAINT_CONDITION_FLAGS:
      meta->memory_location.kind = MEMORY_LOCATION_KIND_STATUS_REGISTER;
      meta->memory_location.reg = emitter->map_constraint_to_register(
          emitter, meta->virtual_register.constraint);
      pg_adjacency_matrix_remove_node(&emitter->interference_graph,
                                      node_idx.value);
      pg_bitfield_set(tombstones_bitfield, row, true);
      break;

    case LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM:
    case LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET:
    case LIR_VIRT_REG_CONSTRAINT_SYSCALL0:
    case LIR_VIRT_REG_CONSTRAINT_SYSCALL1:
    case LIR_VIRT_REG_CONSTRAINT_SYSCALL2:
    case LIR_VIRT_REG_CONSTRAINT_SYSCALL3:
    case LIR_VIRT_REG_CONSTRAINT_SYSCALL4:
    case LIR_VIRT_REG_CONSTRAINT_SYSCALL5:
      meta->memory_location.kind = MEMORY_LOCATION_KIND_REGISTER;
      meta->memory_location.reg = emitter->map_constraint_to_register(
          emitter, meta->virtual_register.constraint);
      pg_adjacency_matrix_remove_node(&emitter->interference_graph,
                                      node_idx.value);
      pg_bitfield_set(tombstones_bitfield, row, true);
      break;
    default:
      PG_ASSERT(0);
    }
  }
}

[[nodiscard]] static Register
asm_color_assign_register(InterferenceGraph *graph,
                          InterferenceNodeIndex node_idx, u32 gprs_count,
                          IrMetadataDyn metadata) {
  GprSet neighbor_colors = {
      .len = gprs_count,
      .set = 0,
  };

  PgAdjacencyMatrixNeighborIterator it =
      pg_adjacency_matrix_make_neighbor_iterator(*graph, node_idx.value);

  PgAdjacencyMatrixNeighbor neighbor = {0};
  do {
    neighbor = pg_adjacency_matrix_neighbor_iterator_next(&it);
    if (!neighbor.has_value) {
      break;
    }

    PG_ASSERT(node_idx.value != neighbor.node);

    MemoryLocation neighbor_mem_loc =
        PG_SLICE_AT(metadata, neighbor.node).memory_location;
    // If a neighbor already has an assigned register, add it to the set.
    {
      if (MEMORY_LOCATION_KIND_REGISTER == neighbor_mem_loc.kind) {
        PG_ASSERT(neighbor_mem_loc.reg.value);
        // PG_ASSERT(neighbor_mem_loc.reg.value <=
        //           PG_SLICE_LAST(amd64_register_allocator_gprs_slice).value);
        asm_gpr_set_add(&neighbor_colors, neighbor_mem_loc.reg.value - 1);
      }
    }
  } while (neighbor.has_value);

  Register res = asm_get_free_register(neighbor_colors);
  PG_ASSERT(res.value);

  // Update memory location.

  {
    MemoryLocation *mem_loc =
        &PG_SLICE_AT(metadata, node_idx.value).memory_location;
    PG_ASSERT(MEMORY_LOCATION_KIND_NONE == mem_loc->kind);
    mem_loc->kind = MEMORY_LOCATION_KIND_REGISTER;
    mem_loc->reg = res;
  }
  return res;
}

// Assign a color (i.e. unique physical register) to each node in the graph
// so that no two adjacent nodes have the same color.
// Meaning that if two variables interfere, they are assigned a different
// physical register.
// It uses Chatain's algorithm which is a bit conservative but also relatively
// simple.
// TODO: Consider using George's algorithm which is more optimistic to assign
// registers.
// TODO: Consider coalescing (see literature).
static void asm_color_interference_graph(AsmEmitter *emitter, bool verbose,
                                         PgAllocator *allocator) {
  if (0 == emitter->interference_graph.nodes_count) {
    return;
  }
  PgString node_tombstones_bitfield = pg_string_make(
      pg_div_ceil(emitter->interference_graph.nodes_count, 8), allocator);

  if (verbose) {
    printf("\n------------ Adjacency matrix of interference graph before "
           "pre-coloring"
           "------------\n\n");
    pg_adjacency_matrix_print(emitter->interference_graph);
  }
  asm_color_do_pre_coloring(emitter, node_tombstones_bitfield);
  if (verbose) {
    printf("\n------------ Adjacency matrix of interference graph after "
           "pre-coloring"
           "------------\n\n");
    pg_adjacency_matrix_print(emitter->interference_graph);
  }

  InterferenceNodeIndexDyn stack = {0};
  PG_DYN_ENSURE_CAP(&stack, emitter->interference_graph.nodes_count, allocator);

  PgAdjacencyMatrix graph_clone =
      pg_adjacency_matrix_clone(emitter->interference_graph, allocator);

  for (u64 row = 0; row < emitter->interference_graph.nodes_count; row++) {
    if (pg_bitfield_get(node_tombstones_bitfield, row)) {
      continue;
    }

    u64 neighbors_count =
        pg_adjacency_matrix_count_neighbors(emitter->interference_graph, row);

    InterferenceNodeIndex node_idx = {(u32)row};

    if (!asm_must_spill(*emitter, node_idx, neighbors_count)) {
      PG_ASSERT(stack.len < emitter->interference_graph.nodes_count);

      *PG_DYN_PUSH_WITHIN_CAPACITY(&stack) = node_idx;

      pg_adjacency_matrix_remove_node(&emitter->interference_graph, row);
      pg_bitfield_set(node_tombstones_bitfield, row, true);
    }
  }
  PG_ASSERT(stack.len <= emitter->interference_graph.nodes_count);

  asm_color_spill_remaining_nodes_in_graph(emitter, &stack,
                                           node_tombstones_bitfield);

  PG_ASSERT(stack.len <= emitter->interference_graph.nodes_count);

  u64 stack_len = stack.len;
  for (u64 _i = 0; _i < stack_len; _i++) {
    if (0 == stack.len) {
      break;
    }

    // Pop the first node from the stack.
    InterferenceNodeIndex node_idx = PG_SLICE_LAST(stack);
    stack.len -= 1;

    // Add the node back to the graph.
    {
      pg_bitfield_set(node_tombstones_bitfield, node_idx.value, false);

      PgAdjacencyMatrixNeighborIterator it =
          pg_adjacency_matrix_make_neighbor_iterator(graph_clone,
                                                     node_idx.value);

      PgAdjacencyMatrixNeighbor neighbor = {0};
      do {
        neighbor = pg_adjacency_matrix_neighbor_iterator_next(&it);
        if (!neighbor.has_value) {
          break;
        }
        PG_ASSERT(node_idx.value != neighbor.node);

        // The node was originally connected in the original graph to its
        // neighbor. When re-adding the node to the graph, we only connect it
        // to non-tombstoned neighbors.
        if (pg_bitfield_get(node_tombstones_bitfield, neighbor.node)) {
          continue;
        }

        pg_adjacency_matrix_add_edge(&emitter->interference_graph, neighbor.row,
                                     neighbor.col);
      } while (neighbor.has_value);

      LirVirtualRegisterConstraint constraint =
          PG_SLICE_AT(emitter->metadata, node_idx.value)
              .virtual_register.constraint;
      PG_ASSERT(LIR_VIRT_REG_CONSTRAINT_NONE == constraint);

      Register reg =
          asm_color_assign_register(&emitter->interference_graph, node_idx,
                                    emitter->gprs_count, emitter->metadata);
      PG_ASSERT(reg.value);

      if (verbose) {
        printf("asm: assigned register: ");
        ir_emitter_print_meta(PG_SLICE_AT(emitter->metadata, node_idx.value));
        printf(" -> ");
        emitter->print_register(reg);
        printf("\n");
      }
    }
  }

  // Sanity checks:
  // - if two nodes interferred (had an edge) in the original graph,
  //   then their assigned registers MUST be different.
  // - if a virtual register is addressable, then it MUST be on the stack
  for (u64 row = 0; row < graph_clone.nodes_count; row++) {
    PgAdjacencyMatrixNeighborIterator it =
        pg_adjacency_matrix_make_neighbor_iterator(graph_clone, row);

    MemoryLocation node_mem_loc =
        PG_SLICE_AT(emitter->metadata, row).memory_location;
    // Interference check.
    {
      PgAdjacencyMatrixNeighbor neighbor = {0};
      do {
        neighbor = pg_adjacency_matrix_neighbor_iterator_next(&it);
        if (!neighbor.has_value) {
          break;
        }
        PG_ASSERT(row != neighbor.node);

        MemoryLocation neighbor_mem_loc =
            PG_SLICE_AT(emitter->metadata, neighbor.node).memory_location;

        if (MEMORY_LOCATION_KIND_REGISTER == node_mem_loc.kind &&
            MEMORY_LOCATION_KIND_REGISTER == neighbor_mem_loc.kind) {
          PG_ASSERT(node_mem_loc.reg.value != neighbor_mem_loc.reg.value);
        }

      } while (neighbor.has_value);
    }

    // Addressable check.
    {
      bool addressable =
          PG_SLICE_AT(emitter->metadata, row).virtual_register.addressable;
      if (addressable) {
        PG_ASSERT(MEMORY_LOCATION_KIND_STACK == node_mem_loc.kind);
      }
    }
  }
}
