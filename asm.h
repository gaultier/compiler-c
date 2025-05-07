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
  PgAnySlice instructions;
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
  AsmCodeSectionSlice text;
  AsmConstantSlice rodata;
  u64 vm_start;
  LabelAddressDyn label_addresses;
  LabelAddressDyn jumps_to_backpatch;

  PgString file_name;
} AsmProgram;

typedef struct AsmEmitter AsmEmitter;

#define ASM_EMITTER_FIELDS                                                     \
  void (*emit_prolog)(AsmEmitter * asm_emitter, PgAllocator * allocator);      \
  void (*emit_epilog)(AsmEmitter * asm_emitter, PgAllocator * allocator);      \
  void (*emit_lirs_to_asm)(AsmEmitter * asm_emitter,                           \
                           LirInstructionSlice lir_instructions, bool verbose, \
                           PgAllocator *allocator);                            \
  PgString (*encode_code)(AsmProgram * program, PgAllocator * allocator);      \
  void (*print_instructions)(AsmEmitter * asm_emitter);                        \
  void (*sanity_check_instructions)(AsmEmitter * asm_emitter);                 \
  PgAnySlice (*get_instructions_slice)(AsmEmitter * asm_emitter);              \
                                                                               \
  u32 stack_base_pointer_offset;                                               \
  u32 stack_base_pointer_max_offset;                                           \
  InterferenceGraph interference_graph;                                        \
  LirEmitter *lir_emitter;

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
