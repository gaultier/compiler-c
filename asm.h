#pragma once
#include "lir.h"

typedef struct {
  u32 value;
} Register;
PG_SLICE(Register) RegisterSlice;
PG_DYN(Register) RegisterDyn;

typedef struct {
  u32 set;
  u32 len;
} GprSet;

typedef enum {
  MEMORY_LOCATION_KIND_NONE,
  MEMORY_LOCATION_KIND_REGISTER,
  MEMORY_LOCATION_KIND_STACK,
  MEMORY_LOCATION_KIND_STATUS_REGISTER,
#if 0
  MEMORY_LOCATION_KIND_MEMORY,
#endif
} MemoryLocationKind;

typedef struct {
  MemoryLocationKind kind;
  union {
    Register reg;
    i32 base_pointer_offset;
#if 0
     u64 memory_address;
#endif
  };
  VirtualRegisterIndex virt_reg_idx;
  InterferenceNodeIndex node_idx;
  IrVar var;
} MemoryLocation;
PG_SLICE(MemoryLocation) MemoryLocationSlice;
PG_DYN(MemoryLocation) MemoryLocationDyn;

typedef struct {
  u32 value;
} MemoryLocationIndex;

typedef struct {
  MemoryLocationDyn memory_locations;
  // Graph represented as a adjacency matrix (M(i,j) = 1 if there is an edge
  // between i and j), stored as a bitfield of the right-upper half (without the
  // diagonal).
  PgAdjacencyMatrix matrix;
} InterferenceGraph;

// On all relevant targets (amd64, aarch64, riscv), syscalls take up to 6
// register arguments.
static const u64 asm_syscall_args_count = 6;

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
                                                                               \
  u32 stack_base_pointer_offset;                                               \
  u32 stack_base_pointer_max_offset;                                           \
  InterferenceGraph interference_graph;                                        \
  LirEmitter *lir_emitter;                                                     \
  u32 gprs_count;                                                              \
  AsmProgram program;

struct AsmEmitter {
  ASM_EMITTER_FIELDS
};

[[nodiscard]]
static MemoryLocationIndex memory_locations_find_by_virtual_register_index(
    MemoryLocationDyn memory_locations, VirtualRegisterIndex virt_reg_idx) {
  for (u64 i = 0; i < memory_locations.len; i++) {
    MemoryLocation mem_loc = PG_SLICE_AT(memory_locations, i);

    if (mem_loc.virt_reg_idx.value == virt_reg_idx.value) {
      return (MemoryLocationIndex){(u32)i};
    }
  }
  return (MemoryLocationIndex){-1U};
}

[[nodiscard]]
static MemoryLocationIndex
memory_locations_find_by_node_index(MemoryLocationDyn memory_locations,
                                    InterferenceNodeIndex node_idx) {
  for (u64 i = 0; i < memory_locations.len; i++) {
    MemoryLocation mem_loc = PG_SLICE_AT(memory_locations, i);

    if (mem_loc.node_idx.value == node_idx.value) {
      return (MemoryLocationIndex){(u32)i};
    }
  }
  return (MemoryLocationIndex){-1U};
}

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
                                         IrVarLifetimeDyn lifetimes) {

  for (u64 row = 0; row < graph.matrix.nodes_count; row++) {
    for (u64 col = 0; col < row; col++) {
      bool edge = pg_adjacency_matrix_has_edge(graph.matrix, row, col);
      if (!edge) {
        continue;
      }

      IrVar a_var = PG_SLICE_AT(lifetimes, row).var;
      IrVar b_var = PG_SLICE_AT(lifetimes, col).var;
      ir_print_var(a_var);
      printf(" -> ");
      ir_print_var(b_var);
      printf("\n");
    }
  }
}

static void asm_sanity_check_interference_graph(InterferenceGraph graph,
                                                bool colored) {
  PG_ASSERT(graph.memory_locations.len <= graph.matrix.nodes_count);
  if (colored) {
    PG_ASSERT(graph.memory_locations.len == graph.matrix.nodes_count);
  }
  PG_ASSERT(graph.matrix.bitfield_len <= graph.matrix.bitfield.len);

  if (0 == graph.matrix.nodes_count) {
    return;
  }

  if (colored) {
    for (u64 i = 0; i < graph.memory_locations.len; i++) {
      MemoryLocation mem_loc = PG_SLICE_AT(graph.memory_locations, i);
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
static InterferenceGraph
asm_build_var_interference_graph(IrVarLifetimeDyn lifetimes,
                                 PgAllocator *allocator) {
  InterferenceGraph graph = {0};

  if (0 == lifetimes.len) {
    return graph;
  }

  graph.matrix = pg_adjacency_matrix_make(lifetimes.len, allocator);
  PG_DYN_ENSURE_CAP(&graph.memory_locations, graph.matrix.nodes_count,
                    allocator);

  for (u64 i = 0; i < lifetimes.len; i++) {
    IrVarLifetime lifetime = PG_SLICE_AT(lifetimes, i);
    PG_ASSERT(!lifetime.tombstone);
    PG_ASSERT(lifetime.start.value <= lifetime.end.value);
    PG_ASSERT(lifetime.var.id.value);

    for (u64 j = i + 1; j < lifetimes.len; j++) {
      IrVarLifetime it = PG_SLICE_AT(lifetimes, j);
      PG_ASSERT(it.start.value <= it.end.value);
      PG_ASSERT(!it.tombstone);

      PG_ASSERT(lifetime.var.id.value != it.var.id.value);

      // `it` strictly before `lifetime`.
      if (it.end.value < lifetime.start.value) {
        continue;
      }

      // `it` strictly after `lifetime`.
      if (lifetime.end.value < it.start.value) {
        continue;
      }

      // Interferes: add an edge between the two nodes.

      pg_adjacency_matrix_add_edge(&graph.matrix, j, i);
    }

    *PG_DYN_PUSH_WITHIN_CAPACITY(&graph.memory_locations) = (MemoryLocation){
        .kind = MEMORY_LOCATION_KIND_NONE,
        .node_idx = {(u32)i},
    };
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

static MemoryLocation *
asm_get_memory_location_from_node_idx(AsmEmitter *emitter,
                                      InterferenceNodeIndex node_idx) {
  MemoryLocationIndex mem_loc_idx = memory_locations_find_by_node_index(
      emitter->interference_graph.memory_locations, node_idx);
  PG_ASSERT(-1U != mem_loc_idx.value);
  MemoryLocation *mem_loc = PG_SLICE_AT_PTR(
      &emitter->interference_graph.memory_locations, mem_loc_idx.value);
  return mem_loc;
}

static VirtualRegister
asm_get_virtual_register_from_node_idx(AsmEmitter emitter,
                                       InterferenceNodeIndex node_idx) {
  VirtualRegisterIndex virt_reg_idx =
      asm_get_memory_location_from_node_idx(&emitter, node_idx)->virt_reg_idx;
  VirtualRegister virt_reg =
      PG_SLICE_AT(emitter.lir_emitter->virtual_registers, virt_reg_idx.value);

  return virt_reg;
}

[[nodiscard]]
static bool asm_must_spill(AsmEmitter emitter, InterferenceNodeIndex node_idx,
                           u64 neighbors_count) {
  bool virt_reg_addressable =
      asm_get_virtual_register_from_node_idx(emitter, node_idx).addressable;

  bool needs_spill =
      neighbors_count >= emitter.gprs_count || virt_reg_addressable;

  return needs_spill;
}

static void asm_spill_node(AsmEmitter *emitter,
                           InterferenceNodeIndex node_idx) {

  MemoryLocation *mem_loc =
      asm_get_memory_location_from_node_idx(emitter, node_idx);
  PG_ASSERT(MEMORY_LOCATION_KIND_NONE == mem_loc->kind);
  PG_ASSERT(node_idx.value == mem_loc->node_idx.value);

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
  for (u64 row = 0; row < emitter->interference_graph.matrix.nodes_count;
       row++) {
    if (pg_bitfield_get(nodes_tombstones_bitfield, row)) {
      continue;
    }

    u64 neighbors_count = pg_adjacency_matrix_count_neighbors(
        emitter->interference_graph.matrix, row);

    pg_adjacency_matrix_remove_node(&emitter->interference_graph.matrix, row);
    pg_bitfield_set(nodes_tombstones_bitfield, row, true);

    InterferenceNodeIndex node_idx = {(u32)row};
    if (!asm_must_spill(*emitter, node_idx, neighbors_count)) {
      PG_ASSERT(stack->len < emitter->interference_graph.matrix.nodes_count);
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
  for (u64 row = 0; row < emitter->interference_graph.matrix.nodes_count;
       row++) {
    InterferenceNodeIndex node_idx = {(u32)row};
    MemoryLocation *mem_loc =
        asm_get_memory_location_from_node_idx((AsmEmitter *)emitter, node_idx);
    VirtualRegister virt_reg = PG_SLICE_AT(
        emitter->lir_emitter->virtual_registers, mem_loc->virt_reg_idx.value);
    switch (virt_reg.constraint) {
    case LIR_VIRT_REG_CONSTRAINT_NONE:
      break;
    case LIR_VIRT_REG_CONSTRAINT_CONDITION_FLAGS:
      mem_loc->kind = MEMORY_LOCATION_KIND_STATUS_REGISTER;
      mem_loc->reg =
          emitter->map_constraint_to_register(emitter, virt_reg.constraint);
      pg_adjacency_matrix_remove_node(&emitter->interference_graph.matrix,
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
                          InterferenceNodeIndex node_idx, u32 gprs_count) {
  GprSet neighbor_colors = {
      .len = gprs_count,
      .set = 0,
  };

  PgAdjacencyMatrixNeighborIterator it =
      pg_adjacency_matrix_make_neighbor_iterator(graph->matrix, node_idx.value);

  PgAdjacencyMatrixNeighbor neighbor = {0};
  do {
    neighbor = pg_adjacency_matrix_neighbor_iterator_next(&it);
    if (!neighbor.has_value) {
      break;
    }

    PG_ASSERT(node_idx.value != neighbor.node);

    MemoryLocationIndex neighbor_mem_loc_idx =
        memory_locations_find_by_node_index(
            graph->memory_locations,
            (InterferenceNodeIndex){(u32)neighbor.node});
    PG_ASSERT(-1U != neighbor_mem_loc_idx.value);

    // If a neighbor already has an assigned register, add it to the set.
    {
      MemoryLocation neighbor_mem_loc =
          PG_SLICE_AT(graph->memory_locations, neighbor_mem_loc_idx.value);
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

  MemoryLocationIndex mem_loc_idx =
      memory_locations_find_by_node_index(graph->memory_locations, node_idx);
  PG_ASSERT(-1U != mem_loc_idx.value);
  {
    MemoryLocation *mem_loc =
        PG_SLICE_AT_PTR(&graph->memory_locations, mem_loc_idx.value);
    PG_ASSERT(MEMORY_LOCATION_KIND_NONE == mem_loc->kind);
    PG_ASSERT(node_idx.value == mem_loc->node_idx.value);

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
  if (0 == emitter->interference_graph.matrix.nodes_count) {
    return;
  }
  PgString node_tombstones_bitfield = pg_string_make(
      pg_div_ceil(emitter->interference_graph.matrix.nodes_count, 8),
      allocator);

  if (verbose) {
    printf("\n------------ Adjacency matrix of interference graph before "
           "pre-coloring"
           "------------\n\n");
    pg_adjacency_matrix_print(emitter->interference_graph.matrix);
    asm_color_do_pre_coloring(emitter, node_tombstones_bitfield);

    printf("\n------------ Adjacency matrix of interference graph after "
           "pre-coloring"
           "------------\n\n");
    pg_adjacency_matrix_print(emitter->interference_graph.matrix);
  }

  InterferenceNodeIndexDyn stack = {0};
  PG_DYN_ENSURE_CAP(&stack, emitter->interference_graph.matrix.nodes_count,
                    allocator);

  PgAdjacencyMatrix graph_clone =
      pg_adjacency_matrix_clone(emitter->interference_graph.matrix, allocator);

  for (u64 row = 0; row < emitter->interference_graph.matrix.nodes_count;
       row++) {
    if (pg_bitfield_get(node_tombstones_bitfield, row)) {
      continue;
    }

    u64 neighbors_count = pg_adjacency_matrix_count_neighbors(
        emitter->interference_graph.matrix, row);

    InterferenceNodeIndex node_idx = {(u32)row};

    if (!asm_must_spill(*emitter, node_idx, neighbors_count)) {
      PG_ASSERT(stack.len < emitter->interference_graph.matrix.nodes_count);

      *PG_DYN_PUSH_WITHIN_CAPACITY(&stack) = node_idx;

      pg_adjacency_matrix_remove_node(&emitter->interference_graph.matrix, row);
      pg_bitfield_set(node_tombstones_bitfield, row, true);
    }
  }
  PG_ASSERT(stack.len <= emitter->interference_graph.matrix.nodes_count);

  asm_color_spill_remaining_nodes_in_graph(emitter, &stack,
                                           node_tombstones_bitfield);

  PG_ASSERT(stack.len <= emitter->interference_graph.matrix.nodes_count);

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

        pg_adjacency_matrix_add_edge(&emitter->interference_graph.matrix,
                                     neighbor.row, neighbor.col);
      } while (neighbor.has_value);

      LirVirtualRegisterConstraint constraint =
          PG_SLICE_AT(emitter->lir_emitter->virtual_registers, node_idx.value)
              .constraint;
      PG_ASSERT(LIR_VIRT_REG_CONSTRAINT_NONE == constraint);

      Register reg = asm_color_assign_register(&emitter->interference_graph,
                                               node_idx, emitter->gprs_count);
      PG_ASSERT(reg.value);
    }
  }

  // Sanity checks:
  // - if two nodes interferred (had an edge) in the original graph,
  //   then their assigned registers MUST be different.
  // - if a virtual register is addressable, then it MUST be on the stack
  for (u64 row = 0; row < graph_clone.nodes_count; row++) {
    PgAdjacencyMatrixNeighborIterator it =
        pg_adjacency_matrix_make_neighbor_iterator(graph_clone, row);

    InterferenceNodeIndex node_idx = {(u32)row};
    MemoryLocationIndex node_mem_loc_idx = memory_locations_find_by_node_index(
        emitter->interference_graph.memory_locations, node_idx);
    PG_ASSERT(-1U != node_mem_loc_idx.value);
    MemoryLocation node_mem_loc = PG_SLICE_AT(
        emitter->interference_graph.memory_locations, node_mem_loc_idx.value);

    // Interference check.
    {
      PgAdjacencyMatrixNeighbor neighbor = {0};
      do {
        neighbor = pg_adjacency_matrix_neighbor_iterator_next(&it);
        if (!neighbor.has_value) {
          break;
        }
        PG_ASSERT(row != neighbor.node);

        InterferenceNodeIndex neighbor_idx = {(u32)neighbor.node};
        MemoryLocationIndex neighbor_mem_loc_idx =
            memory_locations_find_by_node_index(
                emitter->interference_graph.memory_locations, neighbor_idx);
        PG_ASSERT(-1U != neighbor_mem_loc_idx.value);
        MemoryLocation neighbor_mem_loc =
            PG_SLICE_AT(emitter->interference_graph.memory_locations,
                        neighbor_mem_loc_idx.value);

        if (MEMORY_LOCATION_KIND_REGISTER == node_mem_loc.kind &&
            MEMORY_LOCATION_KIND_REGISTER == neighbor_mem_loc.kind) {
          PG_ASSERT(node_mem_loc.reg.value != neighbor_mem_loc.reg.value);
        }

      } while (neighbor.has_value);
    }

    // Addressable check.
    {
      bool addressable = PG_SLICE_AT(emitter->lir_emitter->virtual_registers,
                                     node_mem_loc.virt_reg_idx.value)
                             .addressable;
      if (addressable) {
        PG_ASSERT(MEMORY_LOCATION_KIND_STACK == node_mem_loc.kind);
      }
    }
  }
}
