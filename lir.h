#pragma once
#include "ir.h"
#include "submodules/cstd/lib.c"

typedef struct {
  u32 value;
} Register;
PG_SLICE(Register) RegisterSlice;
PG_DYN(Register) RegisterDyn;

typedef struct {
  u32 set;
  u32 len;
} GprSet;

typedef struct {
  Register return_value;
  RegisterSlice call_preserved;
  RegisterSlice calling_convention;
  Register syscall_num;
  RegisterSlice syscall_calling_convention;
  Register syscall_ret;
  Register stack_pointer;
  Register base_pointer;
} Architecture;

#if 0
typedef enum {
  MEMORY_LOCATION_KIND_NONE,
  MEMORY_LOCATION_KIND_REGISTER,
  MEMORY_LOCATION_KIND_STACK,
  MEMORY_LOCATION_KIND_MEMORY,
} MemoryLocationKind;
#endif

// On all relevant targets (amd64, aarch64, riscv), syscalls take up to 6
// register arguments.
static const u64 lir_syscall_args_count = 6;

typedef enum {
  LIR_VIRT_REG_CONSTRAINT_NONE,
  LIR_VIRT_REG_CONSTRAINT_BASE_POINTER,
#if 0
  LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL0,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL1,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL2,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL3,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL4,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL5,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET,
#endif
} LirVirtualRegisterConstraint;

typedef struct {
  u32 value;
  LirVirtualRegisterConstraint constraint;
  bool addressable;
#if 0
   bool spilled;
#endif
} VirtualRegister;
PG_SLICE(VirtualRegister) VirtualRegisterSlice;
PG_DYN(VirtualRegister) VirtualRegisterDyn;

#if 0
typedef struct {
  MemoryLocationKind kind;
  union {
    VirtualRegister reg;
    i32 base_pointer_offset;
    u64 memory_address;
  };
} MemoryLocation;
PG_SLICE(MemoryLocation) MemoryLocationSlice;
PG_DYN(MemoryLocation) MemoryLocationDyn;
#endif

typedef struct {
  IrLabelId label;
  u64 address_text;
} LabelAddress;
PG_SLICE(LabelAddress) LabelAddressSlice;
PG_DYN(LabelAddress) LabelAddressDyn;

typedef enum {
  LIR_INSTRUCTION_KIND_NONE,
  LIR_INSTRUCTION_KIND_ADD,
  LIR_INSTRUCTION_KIND_SUB,
  LIR_INSTRUCTION_KIND_MOV,
  LIR_INSTRUCTION_KIND_LOAD_FROM_MEMORY,
  LIR_INSTRUCTION_KIND_JUMP_IF_EQ,
  LIR_INSTRUCTION_KIND_JUMP,
  LIR_INSTRUCTION_KIND_LABEL,
  LIR_INSTRUCTION_KIND_CMP,
#if 0
  LIR_INSTRUCTION_KIND_SYSCALL,
#endif
} LirInstructionKind;

typedef enum {
  LIR_OPERAND_KIND_NONE,
  LIR_OPERAND_KIND_VIRTUAL_REGISTER,
  LIR_OPERAND_KIND_IMMEDIATE,
  LIR_OPERAND_KIND_LABEL,
} LirOperandKind;

typedef struct {
  u32 value;
} VirtualRegisterIndex;

typedef struct {
  LirOperandKind kind;
  union {
    VirtualRegisterIndex virt_reg_idx;
    u64 immediate;
    IrLabelId label;
  };
} LirOperand;
PG_SLICE(LirOperand) LirOperandSlice;
PG_DYN(LirOperand) LirOperandDyn;

#if 0
typedef struct {
  MemoryLocationDyn locations;
  IrVar var;
} VarToMemoryLocation;
PG_DYN(VarToMemoryLocation) VarToMemoryLocationDyn;
#endif

typedef struct {
  LirInstructionKind kind;
  LirOperandDyn operands;
  Origin origin;
} LirInstruction;
PG_SLICE(LirInstruction) LirInstructionSlice;
PG_DYN(LirInstruction) LirInstructionDyn;

typedef struct {
  u32 value;
} InterferenceNodeIndex;
PG_SLICE(InterferenceNodeIndex) InterferenceNodeIndexSlice;
PG_DYN(InterferenceNodeIndex) InterferenceNodeIndexDyn;

typedef struct {
  VirtualRegister virt_reg_idx;
  Register reg;
} VirtualRegisterRegister;
PG_DYN(VirtualRegisterRegister) VirtualRegisterRegisterDyn;

typedef struct {
  VirtualRegisterRegisterDyn virt_reg_reg;
  // Graph represented as a adjacency matrix (M(i,j) = 1 if there is an edge
  // between i and j), stored as a bitfield of the right-upper half (without the
  // diagonal).
  PgAdjacencyMatrix matrix;
} InterferenceGraph;

typedef struct {
  IrVar var;
  VirtualRegisterIndex virt_reg_idx;
} VarVirtualRegister;
PG_SLICE(VarVirtualRegister) VarVirtualRegisterSlice;
PG_DYN(VarVirtualRegister) VarVirtualRegisterDyn;

typedef struct {
  u32 value;
} VarVirtualRegisterIndex;

typedef struct {
  LirInstructionDyn instructions;
  VirtualRegisterDyn virtual_registers;
  VarVirtualRegisterDyn var_virtual_registers;

  InterferenceGraph interference_graph;
  u64 lifetimes_count;
} LirEmitter;

static void lir_gpr_set_add(GprSet *set, u32 val) {
  PG_ASSERT(set->len > 0);
  PG_ASSERT(val < set->len);
  set->set |= 1 << val;
}

static void lir_gpr_set_remove(GprSet *set, u32 val) {
  PG_ASSERT(set->len > 0);
  PG_ASSERT(val < set->len);
  set->set &= ~(1 << val);
}

[[nodiscard]]
static bool lir_gpr_is_set(GprSet set, u32 i) {
  PG_ASSERT(set.len > 0);
  PG_ASSERT(i < set.len);

  return (set.set & (1 << i)) != 0;
}

[[nodiscard]]
static Register lir_gpr_pop_first_unset(GprSet *set) {
  PG_ASSERT(set->len > 0);

  u32 first_set_bit = (u32)__builtin_ffs((int)~set->set);

  if (first_set_bit > set->len) {
    return (Register){0};
  }

  if (0 != first_set_bit) {
    lir_gpr_set_add(set, first_set_bit - 1);
  }

  return (Register){.value = first_set_bit};
}

[[nodiscard]]
static GprSet lir_gpr_set_minus(GprSet a, GprSet b) {
  PG_ASSERT(a.len == b.len);
  PG_ASSERT(a.len > 0);

  // 0 0 => 0
  // 0 1 => 0
  // 1 0 => 1
  // 1 1 => 0
  GprSet res = {
      .len = a.len,
      .set = (a.set & (~b.set)),
  };
  return res;
}

[[nodiscard]]
static char *
lir_register_constraint_to_cstr(LirVirtualRegisterConstraint constraint) {
  switch (constraint) {
  case LIR_VIRT_REG_CONSTRAINT_NONE:
    return "NONE";
  case LIR_VIRT_REG_CONSTRAINT_BASE_POINTER:
    return "BASE_POINTER";
#if 0
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM:
    return "SYSCALL_NUM";
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL0:
    return "SYSCALL0";
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL1:
    return "SYSCALL1";
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL2:
    return "SYSCALL2";
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL3:
    return "SYSCALL3";
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL4:
    return "SYSCALL4";
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL5:
    return "SYSCALL5";
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET:
    return "SYSCALL_RET";
#endif

  default:
    PG_ASSERT(0);
  }
}

static void lir_print_virtual_register(VirtualRegisterIndex virt_reg_idx,
                                       VirtualRegisterDyn virtual_registers) {
  VirtualRegister virt_reg = PG_SLICE_AT(virtual_registers, virt_reg_idx.value);

  printf("v%u{constraint=%s, addressable=%s}", virt_reg.value,
         lir_register_constraint_to_cstr(virt_reg.constraint),
         virt_reg.addressable ? "true" : "false"
#if 0 
       ,  virt_reg.spilled ? "true" : "false"
#endif
  );
}

static void lir_print_var_virtual_registers(LirEmitter emitter) {
  for (u64 i = 0; i < emitter.var_virtual_registers.len; i++) {
    VarVirtualRegister var_virt_reg =
        PG_SLICE_AT(emitter.var_virtual_registers, i);

    ir_print_var(var_virt_reg.var);
    printf(": ");
    lir_print_virtual_register(var_virt_reg.virt_reg_idx,
                               emitter.virtual_registers);
    printf("\n");
  }
}

#if 0
static void lir_print_memory_location(MemoryLocation loc) {
  switch (loc.kind) {
  case MEMORY_LOCATION_KIND_REGISTER:
    lir_print_register(loc.reg);
    break;
  case MEMORY_LOCATION_KIND_STACK: {
    printf("[");
    lir_print_register(
        (VirtualRegister){.constraint = LIR_VIRT_REG_CONSTRAINT_BASE_POINTER});
    i32 offset = loc.base_pointer_offset;
    printf("%" PRIi32, offset);
    printf("]");
  } break;
  case MEMORY_LOCATION_KIND_MEMORY:
    printf("%#lx", loc.memory_address);
    break;
  case MEMORY_LOCATION_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void lir_print_var_to_memory_location(
    VarToMemoryLocationDyn var_to_memory_location) {
  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation var_to_mem_loc = PG_SLICE_AT(var_to_memory_location, i);
    printf("; ");
    ir_print_var(var_to_mem_loc.var);
    printf(": ");
    for (u64 j = 0; j < var_to_mem_loc.locations.len; j++) {
      MemoryLocation loc = PG_SLICE_AT(var_to_mem_loc.locations, j);
      lir_print_memory_location(loc);

      printf(" ");
    }
    printf("\n");
  }
}
#endif

static void lir_print_operand(LirOperand operand,
                              VirtualRegisterDyn virtual_registers) {
  switch (operand.kind) {
  case LIR_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case LIR_OPERAND_KIND_VIRTUAL_REGISTER:
    lir_print_virtual_register(operand.virt_reg_idx, virtual_registers);
    break;
  case LIR_OPERAND_KIND_IMMEDIATE:
    printf("%" PRIu64, operand.immediate);
    break;
  case LIR_OPERAND_KIND_LABEL:
    printf(".%" PRIu32, operand.label.value);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void lir_emitter_print_instructions(LirEmitter emitter) {
  for (u64 i = 0; i < emitter.instructions.len; i++) {
    LirInstruction ins = PG_SLICE_AT(emitter.instructions, i);
    printf("[%" PRIu64 "]\n", i);

    origin_print(ins.origin);
    printf(": ");

    switch (ins.kind) {
    case LIR_INSTRUCTION_KIND_ADD:
      printf("add ");
      break;
    case LIR_INSTRUCTION_KIND_SUB:
      printf("sub ");
      break;
    case LIR_INSTRUCTION_KIND_MOV:
      printf("mov ");
      break;
#if 0
    case LIR_INSTRUCTION_KIND_SYSCALL:
      printf("syscall ");
      break;
#endif
    case LIR_INSTRUCTION_KIND_LOAD_FROM_MEMORY:
      printf("lea ");
      break;
    case LIR_INSTRUCTION_KIND_JUMP_IF_EQ:
      printf("je ");
      break;
    case LIR_INSTRUCTION_KIND_JUMP:
      printf("jmp ");
      break;
    case LIR_INSTRUCTION_KIND_LABEL:
      break;
    case LIR_INSTRUCTION_KIND_CMP:
      printf("cmp ");
      break;
    case LIR_INSTRUCTION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }

    for (u64 j = 0; j < ins.operands.len; j++) {
      LirOperand op = PG_SLICE_AT(ins.operands, j);
      lir_print_operand(op, emitter.virtual_registers);

      if (j + 1 < ins.operands.len) {
        printf(", ");
      }
    }
    printf("\n");
  }
}

#if 0
[[nodiscard]] static bool lir_memory_location_eq(MemoryLocation a,
                                                 MemoryLocation b) {
  if (a.kind != b.kind) {
    return false;
  }

  switch (a.kind) {
  case MEMORY_LOCATION_KIND_REGISTER:
    return a.reg.value == b.reg.value;
  case MEMORY_LOCATION_KIND_STACK:
    return a.base_pointer_offset == b.base_pointer_offset;
  case MEMORY_LOCATION_KIND_MEMORY:
    return a.memory_address == b.memory_address;
  case MEMORY_LOCATION_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}
#endif

[[nodiscard]]
static VarVirtualRegisterIndex var_virtual_registers_find_by_virt_reg_idx(
    VarVirtualRegisterDyn var_virtual_registers, VirtualRegisterIndex needle) {
  for (u64 i = 0; i < var_virtual_registers.len; i++) {
    VarVirtualRegister var_virt_reg = PG_SLICE_AT(var_virtual_registers, i);
    if (needle.value == var_virt_reg.virt_reg_idx.value) {
      return (VarVirtualRegisterIndex){(u32)i};
    }
  }
  return (VarVirtualRegisterIndex){-1U};
}

[[nodiscard]]
static VarVirtualRegisterIndex
var_virtual_registers_find_by_var(VarVirtualRegisterDyn var_virtual_registers,
                                  IrVar needle) {
  for (u64 i = 0; i < var_virtual_registers.len; i++) {
    VarVirtualRegister var_virt_reg = PG_SLICE_AT(var_virtual_registers, i);
    if (needle.id.value == var_virt_reg.var.id.value) {
      return (VarVirtualRegisterIndex){(u32)i};
    }
  }
  return (VarVirtualRegisterIndex){-1U};
}

static void lir_print_interference_graph(InterferenceGraph graph) {
  for (u64 i = 0; i < graph.matrix.nodes_count; i++) {
    for (u64 j = i + 1; j < graph.matrix.nodes_count; j++) {
      printf("%c ",
             pg_adjacency_matrix_has_edge(graph.matrix, i, j) ? '0' : '1');
    }
    printf("\n");
  }
}

#if 0
static void lir_sanity_check_interference_graph(InterferenceNodeSlice nodes,
                                                bool colored) {
  (void)nodes;
  (void)colored;
  for (u64 i = 0; i < nodes.len; i++) {
    InterferenceNode node = PG_SLICE_AT(nodes, i);
    if (colored) {
      // Technically, `virt_reg` is assigned in the LIR phase, before coloring.
      PG_ASSERT(-1U != node.virt_reg_idx.value);

      PG_ASSERT(node.reg.value || node.base_stack_pointer_offset);
    }

    for (u64 j = 0; j < node.neighbors.len; j++) {
      InterferenceNodeIndex neighbor_idx = PG_SLICE_AT(node.neighbors, j);
      PG_ASSERT(-1U != neighbor_idx.value);
      InterferenceNode neighbor = PG_SLICE_AT(nodes, neighbor_idx.value);
      PG_ASSERT(neighbor.var.id.value);
      PG_ASSERT(neighbor.neighbors.len < nodes.len);
      PG_ASSERT(node.var.id.value != neighbor.var.id.value);
      if (-1U != node.virt_reg_idx.value &&
          -1U != neighbor.virt_reg_idx.value) {
        PG_ASSERT(node.virt_reg_idx.value != neighbor.virt_reg_idx.value);
      }

#if 0
      if (colored) {
        VirtualRegister node_virt_reg =
            PG_SLICE_AT(virtual_registers, node.virt_reg_idx.value);
        VirtualRegister neighbor_virt_reg =
            PG_SLICE_AT(virtual_registers, neighbor.virt_reg_idx.value);

        if (!(LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET == node_virt_reg.constraint ||
              LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET ==
                  neighbor_virt_reg.constraint)) {
          if (node.reg.value != 0 && neighbor.reg.value != 0) {
            PG_ASSERT(node.reg.value != neighbor.reg.value);
          }
        }
      }
#endif
    }
  }
}
#endif

[[nodiscard]]
static InterferenceGraph
lir_build_var_interference_graph(IrVarLifetimeDyn lifetimes,
                                 PgAllocator *allocator) {
  InterferenceGraph graph = {0};

  if (0 == lifetimes.len) {
    return graph;
  }

  graph.matrix = pg_adjacency_matrix_make(lifetimes.len, allocator);

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

      pg_adjacency_matrix_add_edge(&graph.matrix, i, j);
    }
  }

  return graph;
}

#if 0
[[nodiscard]]
static MemoryLocationDyn *
lir_memory_location_find_var(VarToMemoryLocationDyn var_to_memory_location,
                             IrVar var) {
  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation *elem = PG_SLICE_AT_PTR(&var_to_memory_location, i);
    if (elem->var.id.value == var.id.value) {
      return &elem->locations;
    }
  }

  return nullptr;
}

static MemoryLocation *
lir_memory_location_add(VarToMemoryLocationDyn *var_to_memory_location,
                        IrVar var, MemoryLocation mem_loc,
                        PgAllocator *allocator) {
  MemoryLocationDyn *locations =
      lir_memory_location_find_var(*var_to_memory_location, var);

  if (!locations) {
    *PG_DYN_PUSH(var_to_memory_location, allocator) =
        (VarToMemoryLocation){.var = var};
    locations = &PG_SLICE_LAST_PTR(var_to_memory_location)->locations;
  }

  PG_ASSERT(locations);

  *PG_DYN_PUSH(locations, allocator) = mem_loc;

  return PG_DYN_LAST_PTR(locations);
}
#endif

[[nodiscard]]
static VirtualRegisterIndex
lir_make_virtual_register(LirEmitter *emitter,
                          LirVirtualRegisterConstraint constraint,
                          PgAllocator *allocator) {

  VirtualRegister virt_reg = {
      .value = 1 + (u32)emitter->virtual_registers.len,
      .constraint = constraint,
  };
  *PG_DYN_PUSH(&emitter->virtual_registers, allocator) = virt_reg;
  VirtualRegisterIndex res = {(u32)(emitter->virtual_registers.len - 1)};

  return res;
}

static VirtualRegisterIndex
lir_reserve_virt_reg_for_var(LirEmitter *emitter, IrVar var,
                             LirVirtualRegisterConstraint constraint,
                             PgAllocator *allocator) {
  VirtualRegisterIndex virt_reg_idx =
      lir_make_virtual_register(emitter, constraint, allocator);

  *PG_DYN_PUSH(&emitter->var_virtual_registers, allocator) =
      (VarVirtualRegister){
          .var = var,
          .virt_reg_idx = virt_reg_idx,
      };

  return virt_reg_idx;
}

#if 0
static void lir_memory_location_empty_register(
    VarToMemoryLocationDyn var_to_memory_location, VirtualRegister virt_reg) {
  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation *var_mem_loc =
        PG_SLICE_AT_PTR(&var_to_memory_location, i);

    for (u64 j = 0; j < var_mem_loc->locations.len; j++) {
      MemoryLocation *loc = PG_SLICE_AT_PTR(&var_mem_loc->locations, j);
      if (MEMORY_LOCATION_KIND_REGISTER == loc->kind &&
          virt_reg.value == loc->reg.value) {
        PG_DYN_SWAP_REMOVE(&var_mem_loc->locations, j);
        return;
      }
    }
  }
}

[[nodiscard]]
static MemoryLocation *lir_memory_location_find_var_on_stack(
    VarToMemoryLocationDyn var_to_memory_location, IrVar var) {
  MemoryLocationDyn *locations =
      lir_memory_location_find_var(var_to_memory_location, var);

  if (!locations) {
    return nullptr;
  }

  for (u64 i = 0; i < locations->len; i++) {
    MemoryLocation *loc = PG_SLICE_AT_PTR(locations, i);
    if (MEMORY_LOCATION_KIND_STACK == loc->kind) {
      return loc;
    }
  }
  return nullptr;
}

[[nodiscard]]
static MemoryLocation *lir_memory_location_find_var_in_virt_reg(
    VarToMemoryLocationDyn var_to_memory_location, IrVar var) {
  MemoryLocationDyn *locations =
      lir_memory_location_find_var(var_to_memory_location, var);

  if (!locations) {
    return nullptr;
  }

  for (u64 i = 0; i < locations->len; i++) {
    MemoryLocation *loc = PG_SLICE_AT_PTR(locations, i);
    if (MEMORY_LOCATION_KIND_REGISTER == loc->kind) {
      PG_ASSERT(loc->reg.value != 0);
      return loc;
    }
  }
  return nullptr;
}

[[nodiscard]]
static VarToMemoryLocation *
lir_memory_location_find_virt_reg(VarToMemoryLocationDyn var_to_memory_location,
                                  VirtualRegister virt_reg) {
  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation *var_mem_loc =
        PG_SLICE_AT_PTR(&var_to_memory_location, i);

    for (u64 j = 0; j < var_mem_loc->locations.len; j++) {
      MemoryLocation *loc = PG_SLICE_AT_PTR(&var_mem_loc->locations, j);
      if (MEMORY_LOCATION_KIND_REGISTER == loc->kind &&
          virt_reg.value == loc->reg.value) {
        return var_mem_loc;
      }
    }
  }
  return nullptr;
}

static void lir_memory_location_record_var_copy(
    VarToMemoryLocationDyn *var_to_memory_location, IrVar var,
    MemoryLocation loc_new, PgAllocator *allocator) {
  MemoryLocationDyn *locations =
      lir_memory_location_find_var(*var_to_memory_location, var);
  PG_ASSERT(locations);

  for (u64 i = 0; i < locations->len; i++) {
    MemoryLocation *loc = PG_SLICE_AT_PTR(locations, i);
    if (lir_memory_location_eq(*loc, loc_new)) {
      *loc = loc_new;
      return;
    }
  }

  *PG_DYN_PUSH(locations, allocator) = loc_new;
}

[[nodiscard]]
static LirOperand lir_memory_location_to_operand(MemoryLocation mem_loc) {
  LirOperand operand = {0};

  if (MEMORY_LOCATION_KIND_REGISTER == mem_loc.kind) {
    operand.kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER;
    operand.virt_reg = mem_loc.reg;
  } else if (MEMORY_LOCATION_KIND_STACK == mem_loc.kind) {
    operand.kind = LIR_OPERAND_KIND_EFFECTIVE_ADDRESS;
    operand.effective_address.base =
        (VirtualRegister){.constraint = LIR_VIRT_REG_CONSTRAINT_BASE_POINTER};
    operand.effective_address.displacement = (i32)mem_loc.base_pointer_offset;
  } else {
    PG_ASSERT(0);
  }

  return operand;
}

static void lir_emit_copy_var_to_register(LirEmitter *emitter, IrVar var,
                                          MemoryLocation src,
                                          VirtualRegister dst, Origin origin,
                                          PgAllocator *allocator) {
  {
    VarToMemoryLocation *var_mem_loc_reg =
        lir_memory_location_find_virt_reg(emitter->var_to_memory_location, dst);
    // No-op?
    if (var_mem_loc_reg && var_mem_loc_reg->var.id.value == var.id.value) {
      return;
    }
  }

  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
      .var_to_memory_location_frozen =
          lir_memory_location_clone(emitter->var_to_memory_location, allocator),
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand lhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .virt_reg = dst,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;

  LirOperand rhs = lir_memory_location_to_operand(src);
  PG_ASSERT(LIR_OPERAND_KIND_EFFECTIVE_ADDRESS == rhs.kind);
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

  MemoryLocation dst_mem_loc = {
      .kind = MEMORY_LOCATION_KIND_REGISTER,
      .reg = dst,
  };
  lir_memory_location_record_var_copy(&emitter->var_to_memory_location, var,
                                      dst_mem_loc, allocator);
}

static void lir_emit_lea_to_register(LirEmitter *emitter, IrVar var,
                                     MemoryLocation src, VirtualRegister dst,
                                     Origin origin, PgAllocator *allocator) {

  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_LOAD_EFFECTIVE_ADDRESS,
      .origin = origin,
      .var_to_memory_location_frozen =
          lir_memory_location_clone(emitter->var_to_memory_location, allocator),
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand lhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .virt_reg = dst,
  };

  LirOperand rhs = lir_memory_location_to_operand(src);
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

  MemoryLocation mem_loc_dst = {
      .kind = MEMORY_LOCATION_KIND_REGISTER,
      .reg = dst,
  };
  lir_memory_location_record_var_copy(&emitter->var_to_memory_location, var,
                                      mem_loc_dst, allocator);
}
#endif

static void lir_emit_copy_virt_reg_to_virt_reg(LirEmitter *emitter,
                                               VirtualRegisterIndex src_idx,
                                               VirtualRegisterIndex dst_idx,
                                               Origin origin,
                                               PgAllocator *allocator) {
  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand rhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .virt_reg_idx = src_idx,
  };

  LirOperand lhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .virt_reg_idx = dst_idx,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
}

static void lir_emit_copy_immediate_to_virt_reg(LirEmitter *emitter,
                                                IrOperand src,
                                                VirtualRegisterIndex dst_idx,
                                                Origin origin,
                                                PgAllocator *allocator) {
  // TODO: Expand when more immediate types are available.
  PG_ASSERT(IR_OPERAND_KIND_U64 == src.kind);

  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand lhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .virt_reg_idx = dst_idx,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;

  LirOperand rhs = {
      .kind = LIR_OPERAND_KIND_IMMEDIATE,
      .immediate = src.n64,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
}

static void lir_emit_instruction(LirEmitter *emitter, IrInstruction ir_ins,
                                 PgAllocator *allocator) {
  PG_ASSERT(!ir_ins.tombstone);

  switch (ir_ins.kind) {
  case IR_INSTRUCTION_KIND_ADD: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.res_var.id.value);

    IrOperand lhs_ir_val = PG_SLICE_AT(ir_ins.operands, 0);

    VirtualRegisterIndex res_virt_reg_idx = lir_reserve_virt_reg_for_var(
        emitter, ir_ins.res_var, LIR_VIRT_REG_CONSTRAINT_NONE, allocator);
    PG_ASSERT(-1U != res_virt_reg_idx.value);

    if (IR_OPERAND_KIND_VAR == lhs_ir_val.kind) {
      VarVirtualRegisterIndex lhs_var_virt_reg_idx =
          var_virtual_registers_find_by_var(emitter->var_virtual_registers,
                                            lhs_ir_val.var);
      PG_ASSERT(-1U != lhs_var_virt_reg_idx.value);
      VarVirtualRegister lhs_var_virt_reg = PG_SLICE_AT(
          emitter->var_virtual_registers, lhs_var_virt_reg_idx.value);

      lir_emit_copy_virt_reg_to_virt_reg(emitter, lhs_var_virt_reg.virt_reg_idx,
                                         res_virt_reg_idx, ir_ins.origin,
                                         allocator);
    } else if (IR_OPERAND_KIND_U64 == lhs_ir_val.kind) {
      lir_emit_copy_immediate_to_virt_reg(emitter, lhs_ir_val, res_virt_reg_idx,
                                          ir_ins.origin, allocator);
    }
    // We now need to add rhs to it.

    IrOperand rhs_ir_val = PG_SLICE_AT(ir_ins.operands, 1);
    PG_ASSERT(IR_OPERAND_KIND_VAR == rhs_ir_val.kind ||
              IR_OPERAND_KIND_U64 == rhs_ir_val.kind);

    LirOperand rhs_op = {0};
    // If both lhs and rhs are vars on the stack, we need to load rhs into an
    // intermediate register. We cannot copy one stack slot to another stack
    // slot directly.
    if (IR_OPERAND_KIND_VAR == rhs_ir_val.kind) {
      VarVirtualRegisterIndex rhs_var_virt_reg_idx =
          var_virtual_registers_find_by_var(emitter->var_virtual_registers,
                                            rhs_ir_val.var);
      PG_ASSERT(-1U != rhs_var_virt_reg_idx.value);
      VarVirtualRegister rhs_var_virt_reg = PG_SLICE_AT(
          emitter->var_virtual_registers, rhs_var_virt_reg_idx.value);

      rhs_op.kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER;
      rhs_op.virt_reg_idx = rhs_var_virt_reg.virt_reg_idx;
    } else if (IR_OPERAND_KIND_U64 == rhs_ir_val.kind) {
      rhs_op.kind = LIR_OPERAND_KIND_IMMEDIATE;
      rhs_op.immediate = rhs_ir_val.n64;
    }

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_ADD,
        .origin = ir_ins.origin,
    };
    PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

    LirOperand lhs_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .virt_reg_idx = res_virt_reg_idx,
    };
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs_op;

    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs_op;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

  } break;
  case IR_INSTRUCTION_KIND_LOAD: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.res_var.id.value);

    IrOperand src_ir_val = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_VAR == src_ir_val.kind ||
              IR_OPERAND_KIND_U64 == src_ir_val.kind);

    VirtualRegisterIndex res_virt_reg_idx = lir_reserve_virt_reg_for_var(
        emitter, ir_ins.res_var, LIR_VIRT_REG_CONSTRAINT_NONE, allocator);
    PG_ASSERT(-1U != res_virt_reg_idx.value);

    if (IR_OPERAND_KIND_U64 == src_ir_val.kind) {
      lir_emit_copy_immediate_to_virt_reg(emitter, src_ir_val, res_virt_reg_idx,
                                          ir_ins.origin, allocator);
    } else if (IR_OPERAND_KIND_VAR == src_ir_val.kind) {
      VarVirtualRegisterIndex src_var_virt_reg_idx =
          var_virtual_registers_find_by_var(emitter->var_virtual_registers,
                                            src_ir_val.var);
      PG_ASSERT(-1U != src_var_virt_reg_idx.value);
      VarVirtualRegister src_var_virt_reg = PG_SLICE_AT(
          emitter->var_virtual_registers, src_var_virt_reg_idx.value);

      lir_emit_copy_virt_reg_to_virt_reg(emitter, src_var_virt_reg.virt_reg_idx,
                                         res_virt_reg_idx, ir_ins.origin,
                                         allocator);
    }

  } break;
#if 0
  case IR_INSTRUCTION_KIND_SYSCALL: {
    PG_ASSERT(ir_ins.operands.len <=
              1 /* syscall num */ + lir_syscall_args_count);
    PG_ASSERT(ir_ins.operands.len > 0);

    for (u64 j = 0; j < ir_ins.operands.len; j++) {
      IrOperand val = PG_SLICE_AT(ir_ins.operands, j);
      LirVirtualRegisterConstraint virt_reg_constraint =
          (0 == j)
              ? LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM
              : (LirVirtualRegisterConstraint)(LIR_VIRT_REG_CONSTRAINT_SYSCALL0 +
                                               j - 1);
      VirtualRegisterIndex virt_reg_idx = lir_make_virtual_register(
          emitter, virt_reg_constraint, 0, true, allocator);

      if (IR_OPERAND_KIND_U64 == val.kind) {
        lir_emit_copy_immediate_to_virt_reg(emitter, val, virt_reg_idx,
                                            ir_ins.origin, allocator);
      } else if (IR_OPERAND_KIND_VAR == val.kind) {
        VarVirtualRegisterIndex src_var_virt_reg_idx =
            var_virtual_registers_find_by_var(emitter->var_virtual_registers,
                                              val.var);
        PG_ASSERT(-1U != src_var_virt_reg_idx.value);
        VarVirtualRegister src_var_virt_reg = PG_SLICE_AT(
            emitter->var_virtual_registers, src_var_virt_reg_idx.value);

        lir_emit_copy_virt_reg_to_virt_reg(
            emitter, src_var_virt_reg.virt_reg_idx, virt_reg_idx, ir_ins.origin,
            allocator);
      } else {
        PG_ASSERT(0);
      }
    }

    LirInstruction lir_ins = {
        .kind = LIR_INSTRUCTION_KIND_SYSCALL,
        .origin = ir_ins.origin,
    };
    *PG_DYN_PUSH(&emitter->instructions, allocator) = lir_ins;

    if (ir_ins.res_var.id.value) {
      VirtualRegisterIndex res_virt_reg_idx = lir_reserve_virt_reg_for_var(
          emitter, ir_ins.res_var, LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET,
          allocator);
      PG_ASSERT(res_virt_reg_idx.value != 0);
      InterferenceNodeIndex node_idx = lir_interference_nodes_find_by_var(
          PG_DYN_SLICE(InterferenceNodeSlice, emitter->interference_nodes),
          ir_ins.res_var);
      PG_ASSERT(-1U != node_idx.value);
      PG_SLICE_AT_PTR(&emitter->interference_nodes, node_idx.value)
          ->virt_reg_idx = res_virt_reg_idx;
    }
  } break;
#endif
  case IR_INSTRUCTION_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.res_var.id.value);

    IrOperand lhs_ir_op = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_VAR == lhs_ir_op.kind);

    VirtualRegisterIndex res_virt_reg_idx = lir_reserve_virt_reg_for_var(
        emitter, ir_ins.res_var, LIR_VIRT_REG_CONSTRAINT_NONE, allocator);
    PG_ASSERT(res_virt_reg_idx.value != 0);

    VarVirtualRegisterIndex src_var_virt_reg_idx =
        var_virtual_registers_find_by_var(emitter->var_virtual_registers,
                                          lhs_ir_op.var);
    PG_ASSERT(-1U != src_var_virt_reg_idx.value);

    VarVirtualRegister src_var_virt_reg =
        PG_SLICE_AT(emitter->var_virtual_registers, src_var_virt_reg_idx.value);

    PG_SLICE_AT_PTR(&emitter->virtual_registers,
                    src_var_virt_reg.virt_reg_idx.value)
        ->addressable = true;

    PG_ASSERT(src_var_virt_reg_idx.value != res_virt_reg_idx.value);

    LirInstruction lir_ins = {
        .kind = LIR_INSTRUCTION_KIND_LOAD_FROM_MEMORY,
        .origin = ir_ins.origin,
    };
    LirOperand lhs_lir_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .virt_reg_idx = res_virt_reg_idx,
    };
    LirOperand rhs_lir_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .virt_reg_idx = src_var_virt_reg.virt_reg_idx,
    };
    *PG_DYN_PUSH(&lir_ins.operands, allocator) = lhs_lir_op;
    *PG_DYN_PUSH(&lir_ins.operands, allocator) = rhs_lir_op;
    *PG_DYN_PUSH(&emitter->instructions, allocator) = lir_ins;
  } break;
  case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.res_var.id.value);

    IrOperand cond = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_VAR == cond.kind);

    IrOperand branch_else = PG_SLICE_AT(ir_ins.operands, 1);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == branch_else.kind);

#if 0
    {
      LirInstruction ins_cmp = {
          .kind = LIR_INSTRUCTION_KIND_CMP,
          .origin = ir_ins.origin,
          .var_to_memory_location_frozen = lir_memory_location_clone(
              emitter->var_to_memory_location, allocator),
      };

      MemoryLocation *cond_mem_loc = lir_memory_location_find_var_on_stack(
          emitter->var_to_memory_location, cond.var);
      PG_ASSERT(cond_mem_loc);
      LirOperand lhs = lir_memory_location_to_operand(*cond_mem_loc);
      *PG_DYN_PUSH(&ins_cmp.operands, allocator) = lhs;
      LirOperand rhs = {
          .kind = LIR_OPERAND_KIND_IMMEDIATE,
          .immediate = 0,
      };
      *PG_DYN_PUSH(&ins_cmp.operands, allocator) = rhs;

      *PG_DYN_PUSH(&emitter->instructions, allocator) = ins_cmp;
    }
    {
      LirInstruction ins_je = {
          .kind = LIR_INSTRUCTION_KIND_JUMP_IF_EQ,
          .origin = ir_ins.origin,
          .var_to_memory_location_frozen = lir_memory_location_clone(
              emitter->var_to_memory_location, allocator),
      };

      LirOperand ins_je_op = {
          .kind = LIR_OPERAND_KIND_LABEL,
          .label = branch_else.label,
      };
      *PG_DYN_PUSH(&ins_je.operands, allocator) = ins_je_op;

      *PG_DYN_PUSH(&emitter->instructions, allocator) = ins_je;
    }
#endif
  } break;
  case IR_INSTRUCTION_KIND_JUMP: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.res_var.id.value);

    IrOperand label = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == label.kind);

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_JUMP,
        .origin = ir_ins.origin,
    };

    LirOperand lir_op = {
        .kind = LIR_OPERAND_KIND_LABEL,
        .label = label.label,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = lir_op;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
  } break;
  case IR_INSTRUCTION_KIND_LABEL: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.res_var.id.value);

    IrOperand label = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == label.kind);

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_LABEL,
        .origin = ir_ins.origin,
    };

    LirOperand lir_op = {
        .kind = LIR_OPERAND_KIND_LABEL,
        .label = label.label,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = lir_op;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
  } break;

  case IR_INSTRUCTION_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void lir_emit_instructions(LirEmitter *emitter,
                                  IrInstructionSlice instructions,
                                  PgAllocator *allocator) {
  for (u64 i = 0; i < instructions.len; i++) {
    lir_emit_instruction(emitter, PG_SLICE_AT(instructions, i), allocator);
  }
}
