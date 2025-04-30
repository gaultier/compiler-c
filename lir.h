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
  LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL0,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL1,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL2,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL3,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL4,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL5,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET,
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
  LIR_INSTRUCTION_KIND_SYSCALL,
  LIR_INSTRUCTION_KIND_LOAD_FROM_MEMORY,
  LIR_INSTRUCTION_KIND_JUMP_IF_EQ,
  LIR_INSTRUCTION_KIND_JUMP,
  LIR_INSTRUCTION_KIND_LABEL,
  LIR_INSTRUCTION_KIND_CMP,
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

// Form an interference graph of variable.
// Edge between two nodes: they cannot share the same register.
typedef struct {
  VirtualRegister a, b;
} LirVarInterferenceEdge;
PG_SLICE(LirVarInterferenceEdge) LirVarInterferenceEdgeSlice;
PG_DYN(LirVarInterferenceEdge) LirVarInterferenceEdgeDyn;

typedef struct LirVarInterferenceNode LirVarInterferenceNode;
PG_SLICE(LirVarInterferenceNode) LirVarInterferenceNodeSlice;
PG_DYN(LirVarInterferenceNode) LirVarInterferenceNodeDyn;

typedef struct {
  u32 value;
} LirVarInterferenceNodeIndex;
PG_SLICE(LirVarInterferenceNodeIndex) LirVarInterferenceNodeIndexSlice;
PG_DYN(LirVarInterferenceNodeIndex) LirVarInterferenceNodeIndexDyn;

struct LirVarInterferenceNode {
  IrVar var;
  Register reg; // Assigned with graph coloring in the target specific layer.
  u32 base_stack_pointer_offset; // Assigned with graph color in the target
                                 // specific layer in case of spilling.
  VirtualRegisterIndex virt_reg_idx;
  LirVarInterferenceNodeIndexDyn neighbors;
};

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

  LirVarInterferenceNodeDyn interference_nodes;
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
    case LIR_INSTRUCTION_KIND_SYSCALL:
      printf("syscall ");
      break;
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

[[nodiscard]] static LirVarInterferenceNodeIndex
lir_interference_nodes_find_by_var(LirVarInterferenceNodeSlice nodes,
                                   IrVar var) {
  for (u64 i = 0; i < nodes.len; i++) {
    LirVarInterferenceNode node = PG_SLICE_AT(nodes, i);
    if (node.var.id.value == var.id.value) {
      return (LirVarInterferenceNodeIndex){(u32)i};
    }
  }
  return (LirVarInterferenceNodeIndex){-1U};
}

[[nodiscard]] static LirVarInterferenceNodeIndex
lir_interference_node_indices_find_by_var(
    LirVarInterferenceNodeIndexSlice node_indices,
    LirVarInterferenceNodeSlice nodes, IrVar var) {
  for (u64 i = 0; i < node_indices.len; i++) {
    LirVarInterferenceNodeIndex idx = PG_SLICE_AT(node_indices, i);
    PG_ASSERT(-1U != idx.value);
    LirVarInterferenceNode node = PG_SLICE_AT(nodes, idx.value);
    if (node.var.id.value == var.id.value) {
      return (LirVarInterferenceNodeIndex){(u32)i};
    }
  }
  return (LirVarInterferenceNodeIndex){-1U};
}

[[nodiscard]]
static LirVarInterferenceNodeIndex
lir_interference_graph_add_node(LirVarInterferenceNodeDyn *nodes,
                                u64 worst_case_neighbors_count,
                                PgAllocator *allocator) {
  LirVarInterferenceNode node_new = {0};
  PG_DYN_ENSURE_CAP(
      &node_new.neighbors,
      PG_CLAMP(0, worst_case_neighbors_count - 1, worst_case_neighbors_count),
      allocator);
  *PG_DYN_PUSH(nodes, allocator) = node_new;

  return (LirVarInterferenceNodeIndex){(u32)(nodes->len - 1)};
}

static void lir_interference_graph_add_edge(LirVarInterferenceNodeDyn *nodes,
                                            LirVarInterferenceNodeIndex idx_a,
                                            IrVar var_a, IrVar var_b,
                                            u64 worst_case_neighbors_count,
                                            PgAllocator *allocator) {
  PG_ASSERT(-1U != idx_a.value);
  PG_ASSERT(var_b.id.value);
  PG_ASSERT(worst_case_neighbors_count > 0);

  LirVarInterferenceNodeIndex idx_b = lir_interference_nodes_find_by_var(
      PG_DYN_SLICE(LirVarInterferenceNodeSlice, *nodes), var_b);

  if (-1U == idx_b.value) {
    idx_b = lir_interference_graph_add_node(nodes, worst_case_neighbors_count,
                                            allocator);
  }

  PG_ASSERT(-1U != idx_b.value);
  LirVarInterferenceNode *node_b = PG_SLICE_AT_PTR(nodes, idx_b.value);
  node_b->var = var_b;
  LirVarInterferenceNode *node_a = PG_SLICE_AT_PTR(nodes, idx_a.value);

  {

    bool found =
        -1U !=
        lir_interference_node_indices_find_by_var(
            PG_DYN_SLICE(LirVarInterferenceNodeIndexSlice, node_a->neighbors),
            PG_DYN_SLICE(LirVarInterferenceNodeSlice, *nodes), var_b)
            .value;
    if (!found) {
      *PG_DYN_PUSH_WITHIN_CAPACITY(&node_a->neighbors) = idx_b;
    }
  }
  {
    bool found =
        -1U !=
        lir_interference_node_indices_find_by_var(
            PG_DYN_SLICE(LirVarInterferenceNodeIndexSlice, node_b->neighbors),
            PG_DYN_SLICE(LirVarInterferenceNodeSlice, *nodes), var_a)
            .value;
    if (!found) {
      *PG_DYN_PUSH_WITHIN_CAPACITY(&node_b->neighbors) = idx_a;
    }
  }
}

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

static void lir_print_interference_nodes(LirVarInterferenceNodeSlice nodes,
                                         VirtualRegisterDyn virtual_registers) {
  for (u64 i = 0; i < nodes.len; i++) {
    LirVarInterferenceNode node = PG_SLICE_AT(nodes, i);
    ir_print_var(node.var);
    printf(" virt_reg=");

    PG_ASSERT(-1U != node.virt_reg_idx.value);

    if (node.virt_reg_idx.value < virtual_registers.len) {
      lir_print_virtual_register(node.virt_reg_idx, virtual_registers);
    }
    printf(" reg=%u base_stack_pointer_offset=%u (%lu): ", node.reg.value,
           node.base_stack_pointer_offset, node.neighbors.len);

    for (u64 j = 0; j < node.neighbors.len; j++) {
      LirVarInterferenceNodeIndex neighbor_idx = PG_SLICE_AT(node.neighbors, j);
      PG_ASSERT(-1U != neighbor_idx.value);
      LirVarInterferenceNode neighbor = PG_SLICE_AT(nodes, neighbor_idx.value);
      PG_ASSERT(neighbor.var.id.value);

      ir_print_var(neighbor.var);
      printf("%s", j + 1 < node.neighbors.len ? ", " : "");
    }
    printf("\n");
  }
}

static void
lir_sanity_check_interference_graph(LirVarInterferenceNodeSlice nodes,
                                    bool colored) {
  for (u64 i = 0; i < nodes.len; i++) {
    LirVarInterferenceNode node = PG_SLICE_AT(nodes, i);
    if (colored) {
      // Technically, `virt_reg` is assigned in the LIR phase, before coloring.
      PG_ASSERT(-1U != node.virt_reg_idx.value);

      PG_ASSERT(node.reg.value || node.base_stack_pointer_offset);
    }

    for (u64 j = 0; j < node.neighbors.len; j++) {
      LirVarInterferenceNodeIndex neighbor_idx = PG_SLICE_AT(node.neighbors, j);
      PG_ASSERT(-1U != neighbor_idx.value);
      LirVarInterferenceNode neighbor = PG_SLICE_AT(nodes, neighbor_idx.value);
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

[[nodiscard]]
static LirVarInterferenceNodeDyn
lir_build_var_interference_graph(IrVarLifetimeDyn lifetimes,
                                 PgAllocator *allocator) {
  LirVarInterferenceNodeDyn nodes = {0};

  if (0 == lifetimes.len) {
    return nodes;
  }

  PG_DYN_ENSURE_CAP(&nodes, lifetimes.len * 2, allocator);

  for (u64 i = 0; i < lifetimes.len; i++) {
    IrVarLifetime lifetime = PG_SLICE_AT(lifetimes, i);
    PG_ASSERT(!lifetime.tombstone);
    PG_ASSERT(lifetime.start.value <= lifetime.end.value);
    PG_ASSERT(lifetime.var.id.value);

    LirVarInterferenceNodeIndex node_idx = lir_interference_nodes_find_by_var(
        PG_DYN_SLICE(LirVarInterferenceNodeSlice, nodes), lifetime.var);
    if (-1U == node_idx.value) {
      node_idx =
          lir_interference_graph_add_node(&nodes, lifetimes.len - 1, allocator);
    }
    PG_SLICE_AT_PTR(&nodes, node_idx.value)->var = lifetime.var;

    for (u64 j = 0; j < lifetimes.len; j++) {
      IrVarLifetime it = PG_SLICE_AT(lifetimes, j);
      PG_ASSERT(it.start.value <= it.end.value);
      PG_ASSERT(!it.tombstone);

      // Skip self.
      if (lifetime.var.id.value == it.var.id.value) {
        continue;
      }

      // `it` strictly before `lifetime`.
      if (it.end.value < lifetime.start.value) {
        continue;
      }

      // `it` strictly after `lifetime`.
      if (lifetime.end.value < it.start.value) {
        continue;
      }

      // Interferes: add an edge between the two nodes.
      lir_interference_graph_add_edge(&nodes, node_idx, lifetime.var, it.var,
                                      lifetimes.len, allocator);
    }
  }

  PG_ASSERT(nodes.len == lifetimes.len);

  return nodes;
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
                          u64 worst_case_neighbors_count, bool create_new_node,
                          PgAllocator *allocator) {

  VirtualRegister virt_reg = {
      .value = 1 + (u32)emitter->virtual_registers.len,
      .constraint = constraint,
  };
  *PG_DYN_PUSH(&emitter->virtual_registers, allocator) = virt_reg;
  VirtualRegisterIndex res = {(u32)(emitter->virtual_registers.len - 1)};

  if (create_new_node) {
    LirVarInterferenceNodeIndex node_idx = lir_interference_graph_add_node(
        &emitter->interference_nodes, worst_case_neighbors_count, allocator);
    PG_ASSERT(-1U != node_idx.value);
    PG_SLICE_AT_PTR(&emitter->interference_nodes, node_idx.value)
        ->virt_reg_idx = res;
  }

  return res;
}

static VirtualRegisterIndex
lir_reserve_virt_reg_for_var(LirEmitter *emitter, IrVar var,
                             LirVirtualRegisterConstraint constraint,
                             PgAllocator *allocator) {
  LirVarInterferenceNodeIndex node_idx = lir_interference_nodes_find_by_var(
      PG_DYN_SLICE(LirVarInterferenceNodeSlice, emitter->interference_nodes),
      var);
  PG_ASSERT(-1U != node_idx.value);
  LirVarInterferenceNode *node =
      PG_SLICE_AT_PTR(&emitter->interference_nodes, node_idx.value);
  PG_ASSERT(-1U != node->virt_reg_idx.value);
  VirtualRegister virt_reg =
      PG_SLICE_AT(emitter->virtual_registers, node->virt_reg_idx.value);
  PG_ASSERT(LIR_VIRT_REG_CONSTRAINT_NONE == virt_reg.constraint);

  node->virt_reg_idx = lir_make_virtual_register(
      emitter, constraint, emitter->lifetimes_count, false, allocator);

  return node->virt_reg_idx;
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
    PG_ASSERT(res_virt_reg_idx.value != 0);

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
        PG_ASSERT(src_var_virt_reg_idx.value);
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
      LirVarInterferenceNodeIndex node_idx = lir_interference_nodes_find_by_var(
          PG_DYN_SLICE(LirVarInterferenceNodeSlice,
                       emitter->interference_nodes),
          ir_ins.res_var);
      PG_ASSERT(-1U != node_idx.value);
      PG_SLICE_AT_PTR(&emitter->interference_nodes, node_idx.value)
          ->virt_reg_idx = res_virt_reg_idx;
    }
  } break;
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
