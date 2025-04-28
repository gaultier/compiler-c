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

typedef enum {
  MEMORY_LOCATION_KIND_NONE,
  MEMORY_LOCATION_KIND_REGISTER,
  MEMORY_LOCATION_KIND_STACK,
  MEMORY_LOCATION_KIND_MEMORY,
} MemoryLocationKind;

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
  u64 value;
  LirVirtualRegisterConstraint constraint;
} VirtualRegister;
PG_SLICE(VirtualRegister) VirtualRegisterSlice;
PG_DYN(VirtualRegister) VirtualRegisterDyn;

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
  LIR_INSTRUCTION_KIND_LOAD_EFFECTIVE_ADDRESS,
  LIR_INSTRUCTION_KIND_JUMP_IF_EQ,
  LIR_INSTRUCTION_KIND_JUMP,
  LIR_INSTRUCTION_KIND_LABEL,
  LIR_INSTRUCTION_KIND_CMP,
} LirInstructionKind;

typedef enum {
  LIR_OPERAND_KIND_NONE,
  LIR_OPERAND_KIND_REGISTER,
  LIR_OPERAND_KIND_IMMEDIATE,
  LIR_OPERAND_KIND_EFFECTIVE_ADDRESS,
  LIR_OPERAND_KIND_LABEL,
} LirOperandKind;

typedef struct {
  VirtualRegister base;
  VirtualRegister index;
  u8 scale;
  i32 displacement;
} LirEffectiveAddress;

typedef struct {
  LirOperandKind kind;
  union {
    VirtualRegister reg;
    u64 immediate;
    LirEffectiveAddress effective_address;
    IrLabelId label;
  };
} LirOperand;
PG_SLICE(LirOperand) LirOperandSlice;
PG_DYN(LirOperand) LirOperandDyn;

typedef struct {
  MemoryLocationDyn locations;
  IrVar var;
} VarToMemoryLocation;

PG_DYN(VarToMemoryLocation) VarToMemoryLocationDyn;
typedef struct {
  LirInstructionKind kind;
  LirOperandDyn operands;
  Origin origin;
  VarToMemoryLocationDyn var_to_memory_location_frozen;
} LirInstruction;
PG_SLICE(LirInstruction) LirInstructionSlice;
PG_DYN(LirInstruction) LirInstructionDyn;

// Form an interference graph of variable.
// Edge between two nodes: they cannot share the same register.
typedef struct {
  IrVar a, b;
} LirVarInterferenceEdge;
PG_SLICE(LirVarInterferenceEdge) LirVarInterferenceEdgeSlice;
PG_DYN(LirVarInterferenceEdge) LirVarInterferenceEdgeDyn;

typedef struct LirVarInterferenceNode LirVarInterferenceNode;
PG_SLICE(LirVarInterferenceNode) LirVarInterferenceNodeSlice;
PG_SLICE(LirVarInterferenceNode *) LirVarInterferenceNodePtrSlice;
PG_DYN(LirVarInterferenceNode) LirVarInterferenceNodeDyn;
PG_DYN(LirVarInterferenceNode *) LirVarInterferenceNodePtrDyn;

struct LirVarInterferenceNode {
  IrVar var;
  Register reg; // Assigned with graph coloring in the target specific layer.
  LirVarInterferenceNodePtrDyn neighbors;
};

typedef struct {
  LirInstructionDyn instructions;
  VarToMemoryLocationDyn var_to_memory_location;
  // Relative to base stack pointer.
  u32 stack_offset;
  // Relative to base stack pointer.
  u32 stack_max_offset;
  VirtualRegister virtual_reg;
  IrVarLifetimeDyn var_lifetimes;
} LirEmitter;

static const VirtualRegister lir_virt_reg_base_stack_pointer = {
    .value = 1,
    .constraint = LIR_VIRT_REG_CONSTRAINT_BASE_POINTER,
};

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

static void lir_print_register(VirtualRegister reg) {
  if (reg.value == lir_virt_reg_base_stack_pointer.value) {
    printf("v_bsp");
  } else {
    printf("v%lu(%s)", reg.value,
           lir_register_constraint_to_cstr(reg.constraint));
  }
}

static void lir_print_memory_location(MemoryLocation loc) {
  switch (loc.kind) {
  case MEMORY_LOCATION_KIND_REGISTER:
    lir_print_register(loc.reg);
    break;
  case MEMORY_LOCATION_KIND_STACK: {
    printf("[");
    lir_print_register(lir_virt_reg_base_stack_pointer);
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

static void lir_print_operand(LirOperand operand) {
  switch (operand.kind) {
  case LIR_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case LIR_OPERAND_KIND_REGISTER:
    lir_print_register(operand.reg);
    break;
  case LIR_OPERAND_KIND_IMMEDIATE:
    printf("%" PRIu64, operand.immediate);
    break;
  case LIR_OPERAND_KIND_EFFECTIVE_ADDRESS:
    printf("[");
    lir_print_register(operand.effective_address.base);
    if (operand.effective_address.index.value) {
      printf(" + ");
      lir_print_register(operand.effective_address.index);
      printf(" * %" PRIu8 " ", operand.effective_address.scale);
    }
    printf("%s%" PRIi32 "]",
           operand.effective_address.displacement >= 0 ? "+" : "",
           operand.effective_address.displacement);
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

    lir_print_var_to_memory_location(ins.var_to_memory_location_frozen);

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
    case LIR_INSTRUCTION_KIND_LOAD_EFFECTIVE_ADDRESS:
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
      lir_print_operand(op);

      if (j + 1 < ins.operands.len) {
        printf(", ");
      }
    }
    printf("\n");
  }
}

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

[[nodiscard]] static LirVarInterferenceNode **
lir_interference_nodes_find_by_var(LirVarInterferenceNodePtrDyn nodes,
                                   IrVar var) {
  for (u64 i = 0; i < nodes.len; i++) {
    LirVarInterferenceNode **node = PG_SLICE_AT_PTR(&nodes, i);
    if ((*node)->var.id.value == var.id.value) {
      return node;
    }
  }
  return nullptr;
}

static void lir_interference_graph_add_edge(LirVarInterferenceNodePtrDyn *nodes,
                                            IrVar var_a, IrVar var_b,
                                            u64 vars_count,
                                            PgAllocator *allocator) {
  PG_ASSERT(vars_count > 0);

  LirVarInterferenceNode **node_a =
      lir_interference_nodes_find_by_var(*nodes, var_a);
  LirVarInterferenceNode **node_b =
      lir_interference_nodes_find_by_var(*nodes, var_b);

  if (!node_a) {
    LirVarInterferenceNode *node_new =
        pg_alloc(allocator, sizeof(LirVarInterferenceNode),
                 _Alignof(LirVarInterferenceNode), 1);
    node_new->var = var_a;
    PG_DYN_ENSURE_CAP(&node_new->neighbors, vars_count - 1, allocator);
    *PG_DYN_PUSH_WITHIN_CAPACITY(nodes) = node_new;

    node_a = PG_SLICE_LAST_PTR(nodes);
  }

  if (!node_b) {
    LirVarInterferenceNode *node_new =
        pg_alloc(allocator, sizeof(LirVarInterferenceNode),
                 _Alignof(LirVarInterferenceNode), 1);
    node_new->var = var_b;

    PG_DYN_ENSURE_CAP(&node_new->neighbors, vars_count - 1, allocator);
    *PG_DYN_PUSH_WITHIN_CAPACITY(nodes) = node_new;

    node_b = PG_SLICE_LAST_PTR(nodes);
  }

  PG_ASSERT(node_a && node_b);

  *PG_DYN_PUSH_WITHIN_CAPACITY(&(*node_a)->neighbors) = *node_b;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&(*node_b)->neighbors) = *node_a;
}

static void
lir_print_interference_edges(LirVarInterferenceEdgeDyn interference_edges) {
  for (u64 i = 0; i < interference_edges.len; i++) {
    LirVarInterferenceEdge edge = PG_SLICE_AT(interference_edges, i);
    PG_ASSERT(edge.a.id.value);
    PG_ASSERT(edge.b.id.value);
    PG_ASSERT(edge.a.id.value != edge.b.id.value);

    ir_print_var(edge.a);
    printf(" -> ");
    ir_print_var(edge.b);
    printf("\n");
  }
}

static void lir_print_interference_graph(LirVarInterferenceNodePtrSlice nodes) {
  for (u64 i = 0; i < nodes.len; i++) {
    LirVarInterferenceNode *node = PG_SLICE_AT(nodes, i);
    PG_ASSERT(node);
    PG_ASSERT(node->var.id.value);
    PG_ASSERT(node->neighbors.len > 0);

    ir_print_var(node->var);
    printf(" reg=%u (%lu): ", node->reg.value, node->neighbors.len);

    for (u64 j = 0; j < node->neighbors.len; j++) {
      LirVarInterferenceNode *neighbor = PG_SLICE_AT(node->neighbors, j);
      PG_ASSERT(neighbor);
      PG_ASSERT(neighbor->var.id.value);
      PG_ASSERT(neighbor->neighbors.len > 0);
      PG_ASSERT(neighbor->var.id.value);
      PG_ASSERT(neighbor->neighbors.len > 0);

      ir_print_var(neighbor->var);
      printf("%s", j + 1 < node->neighbors.len ? ", " : "");
    }
    printf("\n");
  }
}

static void
lir_sanity_check_interference_graph(LirVarInterferenceNodePtrSlice nodes,
                                    bool colored) {
  for (u64 i = 0; i < nodes.len; i++) {
    LirVarInterferenceNode *node = PG_SLICE_AT(nodes, i);
    PG_ASSERT(node);
    PG_ASSERT(node->var.id.value);
    PG_ASSERT(node->neighbors.len > 0);

    for (u64 j = 0; j < node->neighbors.len; j++) {
      LirVarInterferenceNode *neighbor = PG_SLICE_AT(node->neighbors, j);
      PG_ASSERT(neighbor);
      PG_ASSERT(neighbor != node);
      PG_ASSERT(neighbor->var.id.value);
      PG_ASSERT(neighbor->neighbors.len > 0);
      PG_ASSERT(node->var.id.value != neighbor->var.id.value);

      if (colored) {
        PG_ASSERT(node->reg.value != neighbor->reg.value);
      }
    }
  }
}

[[nodiscard]]
static LirVarInterferenceNodePtrDyn
lir_build_var_interference_graph(IrVarLifetimeDyn lifetimes, bool verbose,
                                 PgAllocator *allocator) {
  LirVarInterferenceEdgeDyn edges = {0};
  LirVarInterferenceNodePtrDyn nodes = {0};

  if (0 == lifetimes.len) {
    return nodes;
  }

  PG_DYN_ENSURE_CAP(&edges, lifetimes.len * (lifetimes.len - 1) / 2, allocator);
  PG_DYN_ENSURE_CAP(&nodes, lifetimes.len, allocator);

  for (u64 i = 0; i < lifetimes.len; i++) {
    IrVarLifetime lifetime = PG_SLICE_AT(lifetimes, i);
    PG_ASSERT(!lifetime.tombstone);
    PG_ASSERT(lifetime.start.value <= lifetime.end.value);

    for (u64 j = i + 1; j < lifetimes.len; j++) {
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
      LirVarInterferenceEdge edge = {
          .a = lifetime.var,
          .b = it.var,
      };
      *PG_DYN_PUSH_WITHIN_CAPACITY(&edges) = edge;

      lir_interference_graph_add_edge(&nodes, edge.a, edge.b, lifetimes.len,
                                      allocator);
    }
  }

  if (verbose) {
    printf("\n------------ Interference edges ------------\n");
    lir_print_interference_edges(edges);
  }

  return nodes;
}

[[nodiscard]] static VarToMemoryLocationDyn
lir_memory_location_clone(VarToMemoryLocationDyn var_to_memory_location,
                          PgAllocator *allocator) {
  VarToMemoryLocationDyn res = {0};
  if (0 == var_to_memory_location.len) {
    return res;
  }

  PG_DYN_ENSURE_CAP(&res, var_to_memory_location.len, allocator);
  res.len = var_to_memory_location.len;

  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation var_mem_loc_src =
        PG_SLICE_AT(var_to_memory_location, i);
    VarToMemoryLocation *var_mem_loc_dst = PG_SLICE_AT_PTR(&res, i);
    PG_DYN_ENSURE_CAP(&var_mem_loc_dst->locations,
                      var_mem_loc_src.locations.len, allocator);

    PG_DYN_CLONE(&var_mem_loc_dst->locations, var_mem_loc_src.locations,
                 allocator);
    var_mem_loc_dst->var = var_mem_loc_src.var;
  }
  return res;
}

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

static void
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
}

static i32 lir_reserve_stack_slot_for_var(LirEmitter *emitter, IrVar var,
                                          PgAllocator *allocator) {
  u32 size = sizeof(u64); // FIXME
  emitter->stack_offset += size;
  i32 res = -(i32)emitter->stack_offset;

  MemoryLocation mem_loc_stack = {
      .kind = MEMORY_LOCATION_KIND_STACK,
      .base_pointer_offset = res,
  };
  lir_memory_location_add(&emitter->var_to_memory_location, var, mem_loc_stack,
                          allocator);

  return res;
}

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
static VarToMemoryLocation *
lir_memory_location_find_register(VarToMemoryLocationDyn var_to_memory_location,
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

static void lir_memory_location_expire_vars_in_register_at_lifetime_end(
    LirEmitter *emitter, IrId ir_id, bool verbose) {
  for (u64 i = 0; i < emitter->var_to_memory_location.len; i++) {
    VarToMemoryLocation var_mem_loc =
        PG_SLICE_AT(emitter->var_to_memory_location, i);

    IrVarLifetime *lifetime = ir_find_var_lifetime_by_var_id(
        emitter->var_lifetimes, var_mem_loc.var.id);
    PG_ASSERT(lifetime);
    PG_ASSERT(lifetime->start.value <= lifetime->end.value);

    bool expired = lifetime->end.value < ir_id.value;

    if (!expired) {
      continue;
    }

    for (u64 j = 0; j < var_mem_loc.locations.len; j++) {
      MemoryLocation loc = PG_SLICE_AT(var_mem_loc.locations, j);
      if (MEMORY_LOCATION_KIND_REGISTER != loc.kind) {
        continue;
      }

      lir_memory_location_empty_register(emitter->var_to_memory_location,
                                         loc.reg);
      if (verbose) {
        printf("[D001] [%u] expired: ", ir_id.value);
        lir_print_register(loc.reg);
        printf(" %u\n", var_mem_loc.var.id.value);
        printf("\n");
      }
    }
  }
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
    operand.kind = LIR_OPERAND_KIND_REGISTER;
    operand.reg = mem_loc.reg;
  } else if (MEMORY_LOCATION_KIND_STACK == mem_loc.kind) {
    operand.kind = LIR_OPERAND_KIND_EFFECTIVE_ADDRESS;
    operand.effective_address.base = lir_virt_reg_base_stack_pointer;
    operand.effective_address.displacement = (i32)mem_loc.base_pointer_offset;
  } else {
    PG_ASSERT(0);
  }

  return operand;
}

[[nodiscard]]
static VirtualRegister
lir_make_virtual_register(LirEmitter *emitter,
                          LirVirtualRegisterConstraint constraint) {
  VirtualRegister res = emitter->virtual_reg;

  if (LIR_VIRT_REG_CONSTRAINT_BASE_POINTER == constraint) {
    return lir_virt_reg_base_stack_pointer;
  }

  emitter->virtual_reg.value += 1;
  res.constraint = constraint;
  return res;
}

static void lir_emit_copy_var_to_register(LirEmitter *emitter, IrVar var,
                                          MemoryLocation src,
                                          VirtualRegister dst, Origin origin,
                                          PgAllocator *allocator) {
  {
    VarToMemoryLocation *var_mem_loc_reg =
        lir_memory_location_find_register(emitter->var_to_memory_location, dst);
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
      .kind = LIR_OPERAND_KIND_REGISTER,
      .reg = dst,
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
      .kind = LIR_OPERAND_KIND_REGISTER,
      .reg = dst,
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

static void
lir_emit_copy_register_to_var_mem_loc(LirEmitter *emitter, IrVar var_dst,
                                      VirtualRegister src, MemoryLocation dst,
                                      Origin origin, PgAllocator *allocator) {
  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
      .var_to_memory_location_frozen =
          lir_memory_location_clone(emitter->var_to_memory_location, allocator),
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand rhs = {
      .kind = LIR_OPERAND_KIND_REGISTER,
      .reg = src,
  };

  LirOperand lhs = lir_memory_location_to_operand(dst);
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

  lir_memory_location_record_var_copy(&emitter->var_to_memory_location, var_dst,
                                      dst, allocator);
}

static void lir_emit_copy_immediate_to(LirEmitter *emitter, IrValue val,
                                       MemoryLocation dst, Origin origin,
                                       PgAllocator *allocator) {
  PG_ASSERT(IR_VALUE_KIND_U64 == val.kind);

  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
      .var_to_memory_location_frozen =
          lir_memory_location_clone(emitter->var_to_memory_location, allocator),
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand lhs = lir_memory_location_to_operand(dst);
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;

  LirOperand rhs = {
      .kind = LIR_OPERAND_KIND_IMMEDIATE,
      .immediate = val.n64,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
}

static void lir_emit_instruction(LirEmitter *emitter, IrInstruction ir_ins,
                                 bool verbose, PgAllocator *allocator) {
  lir_memory_location_expire_vars_in_register_at_lifetime_end(
      emitter, ir_ins.id, verbose);

  PG_ASSERT(!ir_ins.tombstone);

  // TODO(IMPROVEMENT): for now we store all local variables on the stack.
  if (ir_ins.var.id.value) {
    lir_reserve_stack_slot_for_var(emitter, ir_ins.var, allocator);
  }

  switch (ir_ins.kind) {
  case IR_INSTRUCTION_KIND_ADD: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.var.id.value);

    IrValue lhs_ir_val = PG_SLICE_AT(ir_ins.operands, 0);

    MemoryLocation *res_mem_loc = lir_memory_location_find_var_on_stack(
        emitter->var_to_memory_location, ir_ins.var);
    PG_ASSERT(res_mem_loc);

    // Copy lhs into a register and then into the stack slot of the result
    // var.
    if (IR_VALUE_KIND_VAR == lhs_ir_val.kind) {
      MemoryLocation *lhs_mem_loc = lir_memory_location_find_var_on_stack(
          emitter->var_to_memory_location, lhs_ir_val.var);
      PG_ASSERT(lhs_mem_loc);

      VirtualRegister reg =
          lir_make_virtual_register(emitter, LIR_VIRT_REG_CONSTRAINT_NONE);
      lir_emit_copy_var_to_register(emitter, lhs_ir_val.var, *lhs_mem_loc, reg,
                                    ir_ins.origin, allocator);

      lir_emit_copy_register_to_var_mem_loc(
          emitter, ir_ins.var, reg, *res_mem_loc, ir_ins.origin, allocator);
    } else if (IR_VALUE_KIND_U64 == lhs_ir_val.kind) {
      lir_emit_copy_immediate_to(emitter, lhs_ir_val, *res_mem_loc,
                                 ir_ins.origin, allocator);
    }
    // Now the result stack slot contains lhs. We now need to add rhs to it.

    IrValue rhs_ir_val = PG_SLICE_AT(ir_ins.operands, 1);
    PG_ASSERT(IR_VALUE_KIND_VAR == rhs_ir_val.kind ||
              IR_VALUE_KIND_U64 == rhs_ir_val.kind);

    LirOperand rhs_op = {0};
    // If both lhs and rhs are vars on the stack, we need to load rhs into an
    // intermediate register. We cannot copy one stack slot to another stack
    // slot directly.
    if (IR_VALUE_KIND_VAR == rhs_ir_val.kind) {
      MemoryLocation *rhs_mem_loc = lir_memory_location_find_var_on_stack(
          emitter->var_to_memory_location, rhs_ir_val.var);
      PG_ASSERT(rhs_mem_loc);

      VirtualRegister reg =
          lir_make_virtual_register(emitter, LIR_VIRT_REG_CONSTRAINT_NONE);
      lir_emit_copy_var_to_register(emitter, rhs_ir_val.var, *rhs_mem_loc, reg,
                                    ir_ins.origin, allocator);

      rhs_op.kind = LIR_OPERAND_KIND_REGISTER;
      rhs_op.reg = reg;
    } else if (IR_VALUE_KIND_U64 == rhs_ir_val.kind) {
      rhs_op.kind = LIR_OPERAND_KIND_IMMEDIATE;
      rhs_op.immediate = rhs_ir_val.n64;
    }

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_ADD,
        .origin = ir_ins.origin,
        .var_to_memory_location_frozen = lir_memory_location_clone(
            emitter->var_to_memory_location, allocator),
    };
    PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

    LirOperand lhs_op = lir_memory_location_to_operand(*res_mem_loc);
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs_op;

    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs_op;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

  } break;
  case IR_INSTRUCTION_KIND_LOAD: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.var.id.value);

    IrValue src_ir_val = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == src_ir_val.kind ||
              IR_VALUE_KIND_U64 == src_ir_val.kind);

    MemoryLocation *dst_mem_loc = lir_memory_location_find_var_on_stack(
        emitter->var_to_memory_location, ir_ins.var);

    if (IR_VALUE_KIND_U64 == src_ir_val.kind) {
      lir_emit_copy_immediate_to(emitter, src_ir_val, *dst_mem_loc,
                                 ir_ins.origin, allocator);
    } else if (IR_VALUE_KIND_VAR == src_ir_val.kind) {
      MemoryLocation *rhs_mem_loc = lir_memory_location_find_var_on_stack(
          emitter->var_to_memory_location, src_ir_val.var);
      PG_ASSERT(rhs_mem_loc);

      VirtualRegister reg =
          lir_make_virtual_register(emitter, LIR_VIRT_REG_CONSTRAINT_NONE);
      lir_emit_copy_var_to_register(emitter, src_ir_val.var, *rhs_mem_loc, reg,
                                    ir_ins.origin, allocator);
      lir_emit_copy_register_to_var_mem_loc(
          emitter, ir_ins.var, reg, *dst_mem_loc, ir_ins.origin, allocator);
    }

  } break;
  case IR_INSTRUCTION_KIND_SYSCALL: {
    PG_ASSERT(ir_ins.operands.len <=
              1 /* syscall num */ + lir_syscall_args_count);
    PG_ASSERT(ir_ins.operands.len > 0);

    VirtualRegister virt_reg0 = {0};
    for (u64 j = 0; j < ir_ins.operands.len; j++) {
      IrValue val = PG_SLICE_AT(ir_ins.operands, j);
      LirVirtualRegisterConstraint virt_reg_constraint =
          (0 == j)
              ? LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM
              : (LirVirtualRegisterConstraint)(LIR_VIRT_REG_CONSTRAINT_SYSCALL0 +
                                               j - 1);
      VirtualRegister reg =
          lir_make_virtual_register(emitter, virt_reg_constraint);
      if (0 == j) {
        virt_reg0 = reg;
      }

      if (IR_VALUE_KIND_U64 == val.kind) {
        MemoryLocation mem_loc_reg = {
            .kind = MEMORY_LOCATION_KIND_REGISTER,
            .reg = reg,
        };
        lir_emit_copy_immediate_to(emitter, val, mem_loc_reg, ir_ins.origin,
                                   allocator);
      } else if (IR_VALUE_KIND_VAR == val.kind) {
        MemoryLocation *op_mem_loc = lir_memory_location_find_var_on_stack(
            emitter->var_to_memory_location, val.var);
        PG_ASSERT(op_mem_loc);
        lir_emit_copy_var_to_register(emitter, val.var, *op_mem_loc, reg,
                                      ir_ins.origin, allocator);

      } else {
        PG_ASSERT(0);
      }
    }

    LirInstruction lir_ins = {
        .kind = LIR_INSTRUCTION_KIND_SYSCALL,
        .origin = ir_ins.origin,
        .var_to_memory_location_frozen = lir_memory_location_clone(
            emitter->var_to_memory_location, allocator),
    };
    *PG_DYN_PUSH(&emitter->instructions, allocator) = lir_ins;

    lir_memory_location_empty_register(emitter->var_to_memory_location,
                                       virt_reg0);

    if (ir_ins.var.id.value) {
      MemoryLocation *mem_loc_dst = lir_memory_location_find_var_on_stack(
          emitter->var_to_memory_location, ir_ins.var);
      PG_ASSERT(mem_loc_dst);
      lir_emit_copy_register_to_var_mem_loc(emitter, ir_ins.var, virt_reg0,
                                            *mem_loc_dst, ir_ins.origin,
                                            allocator);
    }

  } break;
  case IR_INSTRUCTION_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.var.id.value);

    IrValue src_ir_val = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == src_ir_val.kind);
    MemoryLocation *src_mem_loc = lir_memory_location_find_var_on_stack(
        emitter->var_to_memory_location, src_ir_val.var);
    PG_ASSERT(src_mem_loc);

    VirtualRegister reg =
        lir_make_virtual_register(emitter, LIR_VIRT_REG_CONSTRAINT_NONE);
    lir_emit_lea_to_register(emitter, ir_ins.var, *src_mem_loc, reg,
                             ir_ins.origin, allocator);

    MemoryLocation *dst_mem_loc = lir_memory_location_find_var_on_stack(
        emitter->var_to_memory_location, ir_ins.var);
    PG_ASSERT(dst_mem_loc);
    lir_emit_copy_register_to_var_mem_loc(
        emitter, ir_ins.var, reg, *dst_mem_loc, ir_ins.origin, allocator);
  } break;
  case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.var.id.value);

    IrValue cond = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == cond.kind);

    IrValue branch_else = PG_SLICE_AT(ir_ins.operands, 1);
    PG_ASSERT(IR_VALUE_KIND_LABEL == branch_else.kind);

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
  } break;
  case IR_INSTRUCTION_KIND_JUMP: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.var.id.value);

    IrValue label = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_LABEL == label.kind);

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_JUMP,
        .origin = ir_ins.origin,
        .var_to_memory_location_frozen = lir_memory_location_clone(
            emitter->var_to_memory_location, allocator),
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
    PG_ASSERT(0 == ir_ins.var.id.value);

    IrValue label = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_LABEL == label.kind);

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_LABEL,
        .origin = ir_ins.origin,
        .var_to_memory_location_frozen = lir_memory_location_clone(
            emitter->var_to_memory_location, allocator),
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
                                  IrInstructionSlice instructions, bool verbose,
                                  PgAllocator *allocator) {
  for (u64 i = 0; i < instructions.len; i++) {
    lir_emit_instruction(emitter, PG_SLICE_AT(instructions, i), verbose,
                         allocator);
  }
}
