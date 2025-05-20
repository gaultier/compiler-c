#pragma once
#include "ast.h"
#include "register_alloc.h"

typedef struct {
  u32 indices_occupied_bitfield;
  RegisterSlice registers;
} GprSet;

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
  RegisterSlice gprs;
} Architecture;

typedef struct {
  PgString name;
  AstNodeFlag flags;
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
  } u;
} AsmConstant;
PG_SLICE(AsmConstant) AsmConstantSlice;
PG_DYN(AsmConstant) AsmConstantDyn;

typedef struct {
  Label label;
  u64 code_address;
} LabelAddress;
PG_DYN(LabelAddress) LabelAddressDyn;

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
  AsmCodeSection (*emit_fn_definition)(AsmEmitter * asm_emitter,               \
                                       FnDefinition fn_def, bool verbose,      \
                                       PgAllocator *allocator);                \
  Pgu8Slice (*encode_program_text)(AsmEmitter * asm_emitter,                   \
                                   PgAllocator * allocator);                   \
  void (*print_program)(AsmEmitter asm_emitter);                               \
  Register (*map_constraint_to_register)(                                      \
      AsmEmitter * asm_emitter, VirtualRegisterConstraint constraint);         \
  void (*print_register)(Register reg);                                        \
                                                                               \
  Architecture arch;                                                           \
  AstNodeDyn nodes;                                                            \
  AsmProgram program;

struct AsmEmitter {
  ASM_EMITTER_FIELDS
};

static void asm_gpr_set_add_idx(GprSet *set, u32 idx) {
  PG_ASSERT(set->registers.len > 0);
  PG_ASSERT(idx < set->registers.len);
  PG_ASSERT(pg_div_ceil(idx, 8) <= sizeof(set->indices_occupied_bitfield));
  set->indices_occupied_bitfield |= 1 << idx;
}

static void asm_gpr_set_add(GprSet *set, Register elem) {
  Register reg = {0};
  for (u32 i = 0; i < set->registers.len; i++) {
    reg = PG_SLICE_AT(set->registers, i);
    if (reg.value == elem.value) {
      asm_gpr_set_add_idx(set, i);
      return;
    }
  }
  PG_ASSERT(0);
}

[[nodiscard]]
static u32 asm_gpr_pop_first_unset_idx(GprSet *set) {
  PG_ASSERT(set->registers.len > 0);

  u32 first_set_bit = (u32)__builtin_ffs((int)~set->indices_occupied_bitfield);
  PG_ASSERT(first_set_bit);
  // `__builtin_ffs` returns a 1-indexed result.
  first_set_bit -= 1;

  PG_ASSERT(first_set_bit < set->registers.len);

  asm_gpr_set_add_idx(set, first_set_bit);

  return first_set_bit;
}

[[nodiscard]]
static Register asm_gpr_pop_first_unset(GprSet *set) {
  return PG_SLICE_AT(set->registers, asm_gpr_pop_first_unset_idx(set));
}

static void asm_sanity_check_interference_graph(InterferenceGraph graph,
                                                MetadataDyn metadata,
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
        PG_ASSERT(mem_loc.u.reg.value);
        break;
      case MEMORY_LOCATION_KIND_STACK:
        PG_ASSERT(mem_loc.u.base_pointer_offset != 0);
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
static u32 asm_reserve_stack_slot(u32 *stack_base_pointer_offset,
                                  u32 *stack_base_pointer_max_offset,
                                  u32 slot_size) {
  *stack_base_pointer_offset += slot_size;
  *stack_base_pointer_max_offset =
      PG_MAX(*stack_base_pointer_max_offset, *stack_base_pointer_offset);

  PG_ASSERT(*stack_base_pointer_offset > 0);
  return *stack_base_pointer_offset;
}

[[nodiscard]]
static bool asm_must_spill(AsmEmitter emitter, MetadataDyn metadata,
                           InterferenceNodeIndex node_idx,
                           u64 neighbors_count) {
  bool virt_reg_addressable =
      PG_SLICE_AT(metadata, node_idx.value).virtual_register.addressable;

  bool needs_spill =
      neighbors_count >= emitter.arch.gprs.len || virt_reg_addressable;

  return needs_spill;
}

static void asm_spill_node(MetadataDyn metadata, FnDefinition *fn_def,
                           InterferenceNodeIndex node_idx) {

  MemoryLocation *mem_loc =
      &PG_SLICE_AT(metadata, node_idx.value).memory_location;
  PG_ASSERT(MEMORY_LOCATION_KIND_NONE == mem_loc->kind);

  mem_loc->kind = MEMORY_LOCATION_KIND_STACK;
  u32 rbp_offset = asm_reserve_stack_slot(
      &fn_def->stack_base_pointer_offset,
      &fn_def->stack_base_pointer_offset_max, sizeof(u64) /*FIXME*/);
  mem_loc->u.base_pointer_offset = (i32)rbp_offset;
}

// TODO: Better strategy to pick which virtual registers to spill.
// For now we simply spill them all if they have more neighbors than there are
// GPRs, on a 'first encounter' basis.
static void asm_color_spill_remaining_nodes_in_graph(
    AsmEmitter *emitter, FnDefinition *fn_def, InterferenceNodeIndexDyn *stack,
    PgString nodes_tombstones_bitfield) {
  for (u64 row = 0; row < fn_def->interference_graph.nodes_count; row++) {
    if (pg_bitfield_get(nodes_tombstones_bitfield, row)) {
      continue;
    }

    u64 neighbors_count =
        pg_adjacency_matrix_count_neighbors(fn_def->interference_graph, row);

    pg_adjacency_matrix_remove_node(&fn_def->interference_graph, row);
    pg_bitfield_set(nodes_tombstones_bitfield, row, true);

    InterferenceNodeIndex node_idx = {(u32)row};
    if (!asm_must_spill(*emitter, fn_def->metadata, node_idx,
                        neighbors_count)) {
      PG_ASSERT(stack->len < fn_def->interference_graph.nodes_count);
      *PG_DYN_PUSH_WITHIN_CAPACITY(stack) = node_idx;
      continue;
    }

    // Need to spill.
    asm_spill_node(fn_def->metadata, fn_def, node_idx);
  }
}

static Register asm_get_free_register(GprSet *gpr_set) {
  // TODO: Smarter free register selection.
  // E.g. favor caller-saved registers, etc.
  return asm_gpr_pop_first_unset(gpr_set);
}

static void asm_color_do_precoloring(AsmEmitter *emitter, FnDefinition *fn_def,
                                     PgString tombstones_bitfield,
                                     GprSet *gprs_precolored_set,
                                     bool verbose) {
  // Dummy.
  pg_bitfield_set(tombstones_bitfield, 0, true);

  for (u64 row = 0; row < fn_def->interference_graph.nodes_count; row++) {
    InterferenceNodeIndex node_idx = {(u32)row};
    Metadata *meta = PG_SLICE_AT_PTR(&fn_def->metadata, node_idx.value);
    switch (meta->virtual_register.constraint) {
    case VREG_CONSTRAINT_NONE:
      break;
    case VREG_CONSTRAINT_CONDITION_FLAGS:
      meta->memory_location.kind = MEMORY_LOCATION_KIND_STATUS_REGISTER;
      meta->memory_location.u.reg = emitter->map_constraint_to_register(
          emitter, meta->virtual_register.constraint);
      pg_adjacency_matrix_remove_node(&fn_def->interference_graph,
                                      node_idx.value);
      pg_bitfield_set(tombstones_bitfield, row, true);
      break;

    case VREG_CONSTRAINT_SYSCALL_NUM:
    case VREG_CONSTRAINT_SYSCALL_RET:
    case VREG_CONSTRAINT_SYSCALL0:
    case VREG_CONSTRAINT_SYSCALL1:
    case VREG_CONSTRAINT_SYSCALL2:
    case VREG_CONSTRAINT_SYSCALL3:
    case VREG_CONSTRAINT_SYSCALL4:
    case VREG_CONSTRAINT_SYSCALL5:
      meta->memory_location.kind = MEMORY_LOCATION_KIND_REGISTER;
      meta->memory_location.u.reg = emitter->map_constraint_to_register(
          emitter, meta->virtual_register.constraint);
      pg_adjacency_matrix_remove_node(&fn_def->interference_graph,
                                      node_idx.value);
      pg_bitfield_set(tombstones_bitfield, row, true);
#if 0
      PG_ASSERT(!asm_gpr_set_has(*set, meta->memory_location.reg.value));
#endif
      asm_gpr_set_add(gprs_precolored_set, meta->memory_location.u.reg);

      if (verbose) {
        printf("asm: precoloring assigned register: ");
        metadata_print_meta(PG_SLICE_AT(fn_def->metadata, node_idx.value));
        printf(" -> ");
        emitter->print_register(meta->memory_location.u.reg);
        printf("\n");
      }
      break;
    default:
      PG_ASSERT(0);
    }
  }
}

[[nodiscard]] static Register
asm_color_assign_register(InterferenceGraph graph_clone,
                          InterferenceNodeIndex node_idx,
                          GprSet gprs_precolored, MetadataDyn metadata) {
  GprSet neighbor_colors = gprs_precolored;

  PgAdjacencyMatrixNeighborIterator it =
      pg_adjacency_matrix_make_neighbor_iterator(graph_clone, node_idx.value);

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
    if (MEMORY_LOCATION_KIND_REGISTER == neighbor_mem_loc.kind) {
      PG_ASSERT(neighbor_mem_loc.u.reg.value);
      asm_gpr_set_add(&neighbor_colors, neighbor_mem_loc.u.reg);
    }
  } while (neighbor.has_value);

  Register res = asm_get_free_register(&neighbor_colors);
  PG_ASSERT(res.value);

  // Update memory location.

  {
    MemoryLocation *mem_loc =
        &PG_SLICE_AT(metadata, node_idx.value).memory_location;
    PG_ASSERT(MEMORY_LOCATION_KIND_NONE == mem_loc->kind);
    mem_loc->kind = MEMORY_LOCATION_KIND_REGISTER;
    mem_loc->u.reg = res;
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
static void asm_color_interference_graph(AsmEmitter *emitter,
                                         FnDefinition *fn_def, AstNodeDyn nodes,
                                         bool verbose, PgAllocator *allocator) {
  if (0 == fn_def->interference_graph.nodes_count) {
    return;
  }
  PgString node_tombstones_bitfield = pg_string_make(
      pg_div_ceil(fn_def->interference_graph.nodes_count, 8), allocator);

  PgAdjacencyMatrix graph_clone =
      pg_adjacency_matrix_clone(fn_def->interference_graph, allocator);

  if (verbose) {
    PgString fn_name = ast_fn_name(*fn_def, nodes);
    printf("\n------------ Adjacency matrix of interference graph before "
           "pre-coloring %.*s"
           "------------\n\n",
           (i32)fn_name.len, fn_name.data);
    pg_adjacency_matrix_print(fn_def->interference_graph);
  }
  GprSet gprs_precolored = {
      .indices_occupied_bitfield = 0,
      .registers = emitter->arch.gprs,
  };
  asm_color_do_precoloring(emitter, fn_def, node_tombstones_bitfield,
                           &gprs_precolored, verbose);
  if (verbose) {
    PgString fn_name = ast_fn_name(*fn_def, nodes);
    printf("\n------------ Adjacency matrix of interference graph after "
           "pre-coloring %.*s"
           "------------\n\n",
           (i32)fn_name.len, fn_name.data);
    for (u64 i = 0; i < fn_def->interference_graph.nodes_count; i++) {
      bool removed = pg_bitfield_get(node_tombstones_bitfield, i);
      printf("%s%lu%s ", removed ? "\x1B[9m" : "", i, removed ? "\x1B[0m" : "");
    }
    printf("\n");
    pg_adjacency_matrix_print(fn_def->interference_graph);
  }

  InterferenceNodeIndexDyn stack = {0};
  PG_DYN_ENSURE_CAP(&stack, fn_def->interference_graph.nodes_count, allocator);

  for (u64 row = 0; row < fn_def->interference_graph.nodes_count; row++) {
    if (pg_bitfield_get(node_tombstones_bitfield, row)) {
      continue;
    }

    u64 neighbors_count =
        pg_adjacency_matrix_count_neighbors(fn_def->interference_graph, row);

    InterferenceNodeIndex node_idx = {(u32)row};

    if (!asm_must_spill(*emitter, fn_def->metadata, node_idx,
                        neighbors_count)) {
      PG_ASSERT(stack.len < fn_def->interference_graph.nodes_count);

      *PG_DYN_PUSH_WITHIN_CAPACITY(&stack) = node_idx;

      pg_adjacency_matrix_remove_node(&fn_def->interference_graph, row);
      pg_bitfield_set(node_tombstones_bitfield, row, true);
    }
  }
  PG_ASSERT(stack.len <= fn_def->interference_graph.nodes_count);

  asm_color_spill_remaining_nodes_in_graph(emitter, fn_def, &stack,
                                           node_tombstones_bitfield);

  PG_ASSERT(stack.len <= fn_def->interference_graph.nodes_count);

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

        pg_adjacency_matrix_add_edge(&fn_def->interference_graph, neighbor.row,
                                     neighbor.col);
      } while (neighbor.has_value);

      VirtualRegisterConstraint constraint =
          PG_SLICE_AT(fn_def->metadata, node_idx.value)
              .virtual_register.constraint;
      PG_ASSERT(VREG_CONSTRAINT_NONE == constraint);

      Register reg = asm_color_assign_register(
          graph_clone, node_idx, gprs_precolored, fn_def->metadata);
      PG_ASSERT(reg.value);

      if (verbose) {
        printf("asm: coloring assigned register: ");
        metadata_print_meta(PG_SLICE_AT(fn_def->metadata, node_idx.value));
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
        PG_SLICE_AT(fn_def->metadata, row).memory_location;
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
            PG_SLICE_AT(fn_def->metadata, neighbor.node).memory_location;

        if (MEMORY_LOCATION_KIND_REGISTER == node_mem_loc.kind &&
            MEMORY_LOCATION_KIND_REGISTER == neighbor_mem_loc.kind) {
          PG_ASSERT(node_mem_loc.u.reg.value != neighbor_mem_loc.u.reg.value);
        }

      } while (neighbor.has_value);
    }

    // Addressable check.
    {
      bool addressable =
          PG_SLICE_AT(fn_def->metadata, row).virtual_register.addressable;
      if (addressable) {
        PG_ASSERT(MEMORY_LOCATION_KIND_STACK == node_mem_loc.kind);
      }
    }
  }
}

static void asm_emit(AsmEmitter *asm_emitter, FnDefinitionDyn fn_defs,
                     AstNodeDyn nodes, bool verbose, PgAllocator *allocator) {

  (void)asm_emitter;

  for (u32 i = 0; i < fn_defs.len; i++) {
    FnDefinition fn_def = PG_SLICE_AT(fn_defs, i);
    AstNode fn_node = PG_SLICE_AT(nodes, fn_def.node_start.value);

    fn_def.interference_graph =
        reg_build_interference_graph(fn_def.metadata, allocator);
    if (verbose) {
      printf("\n------------ Interference graph %.*s ------------\n",
             (i32)fn_node.u.identifier.len, fn_node.u.identifier.data);
      reg_print_interference_graph(fn_def.interference_graph, fn_def.metadata);
    }

    asm_sanity_check_interference_graph(fn_def.interference_graph,
                                        fn_def.metadata, false);
    asm_color_interference_graph(asm_emitter, &fn_def, nodes, verbose,
                                 allocator);
    asm_sanity_check_interference_graph(fn_def.interference_graph,
                                        fn_def.metadata, true);

    // TODO: Codegen.
    AsmCodeSection section = asm_emitter->emit_fn_definition(
        asm_emitter, fn_def, verbose, allocator);
    *PG_DYN_PUSH(&asm_emitter->program.text, allocator) = section;
  }
}
