#pragma once
#include "ir.h"
#include "submodules/cstd/lib.c"

typedef struct {
  u64 value;
} Register;
PG_SLICE(Register) RegisterSlice;
PG_DYN(Register) RegisterDyn;

typedef struct {
  Register return_value;
  RegisterSlice call_preserved;
  RegisterSlice calling_convention;
  RegisterSlice syscall_calling_convention;
  Register stack_pointer;
  Register base_pointer;
} Architecture;

typedef enum {
  MEMORY_LOCATION_KIND_NONE,
  MEMORY_LOCATION_KIND_REGISTER,
  MEMORY_LOCATION_KIND_STACK,
  MEMORY_LOCATION_KIND_MEMORY,
} MemoryLocationKind;

typedef struct {
  u64 value;
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
  LIR_KIND_NONE,
  LIR_KIND_ADD,
  LIR_KIND_SUB,
  LIR_KIND_MOV,
  LIR_KIND_SYSCALL,
  LIR_KIND_LOAD_EFFECTIVE_ADDRESS,
  LIR_KIND_JUMP_IF_EQ,
  LIR_KIND_JUMP,
  LIR_KIND_LABEL,
  LIR_KIND_CMP,
} LirKind;

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
  LirKind kind;
  LirOperandDyn operands;
  Origin origin;
  VarToMemoryLocationDyn var_to_memory_location_frozen;
} LirInstruction;
PG_SLICE(LirInstruction) LirInstructionSlice;
PG_DYN(LirInstruction) LirInstructionDyn;

typedef struct {
  LirInstructionDyn instructions;
  VarToMemoryLocationDyn var_to_memory_location;
  // Relative to base stack pointer.
  u32 stack_offset;
  // Relative to base stack pointer.
  u32 stack_max_offset;
  VirtualRegister virtual_reg;
} LirEmitter;

static const VirtualRegister lir_base_stack_pointer = {1};

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

#if 0
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
static MemoryLocation *amd64_memory_location_find_var_in_register_any(
    VarToMemoryLocationDyn var_to_memory_location, IrVar var) {
  MemoryLocationDyn *locations =
      amd64_memory_location_find_var(var_to_memory_location, var);
  if (!locations) {
    return nullptr;
  }

  for (u64 i = 0; i < locations->len; i++) {
    MemoryLocation *loc = PG_SLICE_AT_PTR(locations, i);
    if (MEMORY_LOCATION_KIND_REGISTER == loc->kind) {
      return loc;
    }
  }
  return nullptr;
}

[[nodiscard]]
static VarToMemoryLocation *amd64_memory_location_find_register(
    VarToMemoryLocationDyn var_to_memory_location, Register reg) {
  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation *var_mem_loc =
        PG_SLICE_AT_PTR(&var_to_memory_location, i);

    for (u64 j = 0; j < var_mem_loc->locations.len; j++) {
      MemoryLocation loc = PG_SLICE_AT(var_mem_loc->locations, j);
      if (MEMORY_LOCATION_KIND_REGISTER == loc.kind &&
          reg.value == loc.reg.value) {
        return var_mem_loc;
      }
    }
  }
  return nullptr;
}
#endif

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
    operand.effective_address.base = lir_base_stack_pointer;
    operand.effective_address.displacement = (i32)mem_loc.base_pointer_offset;
  } else {
    PG_ASSERT(0);
  }

  return operand;
}

[[nodiscard]]
static VirtualRegister lir_make_virtual_register(LirEmitter *emitter) {
  VirtualRegister res = emitter->virtual_reg;
  emitter->virtual_reg.value += 1;
  return res;
}

static void lir_emit_copy_var_to_register(LirEmitter *emitter, IrVar var,
                                          MemoryLocation src,
                                          VirtualRegister dst, Origin origin,
                                          PgAllocator *allocator) {

  LirInstruction ins = {
      .kind = LIR_KIND_MOV,
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

static void lir_emit_copy_register_to(LirEmitter *emitter, IrVar var,
                                      VirtualRegister src, MemoryLocation dst,
                                      Origin origin, PgAllocator *allocator) {
  LirInstruction ins = {
      .kind = LIR_KIND_MOV,
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

  lir_memory_location_record_var_copy(&emitter->var_to_memory_location, var,
                                      dst, allocator);
}

static void lir_emit_copy_immediate_to(LirEmitter *emitter, IrValue val,
                                       MemoryLocation dst, Origin origin,
                                       PgAllocator *allocator) {

  PG_ASSERT(IR_VALUE_KIND_U64 == val.kind);

  LirInstruction ins = {
      .kind = LIR_KIND_MOV,
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

static void lir_emit(LirEmitter *emitter, IrSlice irs, PgAllocator *allocator) {
  for (u64 i = 0; i < irs.len; i++) {
    Ir ir = PG_SLICE_AT(irs, i);

    // IMPROVEMENT: for now we store all local variables on the stack.
    if (ir.var.id.value) {
      lir_reserve_stack_slot_for_var(emitter, ir.var, allocator);
    }

    switch (ir.kind) {
    case IR_KIND_ADD: {
      PG_ASSERT(2 == ir.operands.len);
      PG_ASSERT(ir.var.id.value);

      IrValue lhs_ir_val = PG_SLICE_AT(ir.operands, 0);
      PG_ASSERT(IR_VALUE_KIND_VAR == lhs_ir_val.kind);

      MemoryLocation *res_mem_loc = lir_memory_location_find_var_on_stack(
          emitter->var_to_memory_location, ir.var);
      PG_ASSERT(res_mem_loc);

      // Copy lhs into a register and then into the stack slot of the result
      // var.
      {
        MemoryLocation *lhs_mem_loc = lir_memory_location_find_var_on_stack(
            emitter->var_to_memory_location, lhs_ir_val.var);
        PG_ASSERT(lhs_mem_loc);

        VirtualRegister reg = lir_make_virtual_register(emitter);
        lir_emit_copy_var_to_register(emitter, lhs_ir_val.var, *lhs_mem_loc,
                                      reg, ir.origin, allocator);

        lir_emit_copy_register_to(emitter, ir.var, reg, *res_mem_loc, ir.origin,
                                  allocator);
      }
      // Now the result stack slot contains lhs. We now need to add rhs to it.

      IrValue rhs_ir_val = PG_SLICE_AT(ir.operands, 1);
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

        VirtualRegister reg = lir_make_virtual_register(emitter);
        lir_emit_copy_var_to_register(emitter, rhs_ir_val.var, *rhs_mem_loc,
                                      reg, ir.origin, allocator);

        rhs_op.kind = LIR_OPERAND_KIND_REGISTER;
        rhs_op.reg = reg;
      } else if (IR_VALUE_KIND_U64 == rhs_ir_val.kind) {
        rhs_op.kind = LIR_OPERAND_KIND_IMMEDIATE;
        rhs_op.immediate = rhs_ir_val.n64;
      }

      LirInstruction ins = {
          .kind = LIR_KIND_ADD,
          .origin = ir.origin,
          .var_to_memory_location_frozen = lir_memory_location_clone(
              emitter->var_to_memory_location, allocator),
      };
      PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

      MemoryLocation *lhs_mem_loc = lir_memory_location_find_var_on_stack(
          emitter->var_to_memory_location, lhs_ir_val.var);
      PG_ASSERT(lhs_mem_loc);
      LirOperand lhs_op = lir_memory_location_to_operand(*lhs_mem_loc);
      *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs_op;

      *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs_op;

      *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

    } break;
    case IR_KIND_LOAD: {
      PG_ASSERT(1 == ir.operands.len);
      PG_ASSERT(ir.var.id.value);

      IrValue rhs_ir_val = PG_SLICE_AT(ir.operands, 0);
      PG_ASSERT(IR_VALUE_KIND_VAR == rhs_ir_val.kind ||
                IR_VALUE_KIND_U64 == rhs_ir_val.kind);

      MemoryLocation *dst_mem_loc = lir_memory_location_find_var_on_stack(
          emitter->var_to_memory_location, ir.var);

      if (IR_VALUE_KIND_U64 == rhs_ir_val.kind) {
        lir_emit_copy_immediate_to(emitter, rhs_ir_val, *dst_mem_loc, ir.origin,
                                   allocator);
      } else if (IR_VALUE_KIND_VAR == rhs_ir_val.kind) {
        MemoryLocation *rhs_mem_loc = lir_memory_location_find_var_on_stack(
            emitter->var_to_memory_location, rhs_ir_val.var);
        PG_ASSERT(rhs_mem_loc);

        VirtualRegister reg = lir_make_virtual_register(emitter);
        lir_emit_copy_var_to_register(emitter, rhs_ir_val.var, *rhs_mem_loc,
                                      reg, ir.origin, allocator);
      }

    } break;
    case IR_KIND_SYSCALL:
    case IR_KIND_ADDRESS_OF: {
    } break;
    case IR_KIND_JUMP_IF_FALSE:
    case IR_KIND_JUMP:
    case IR_KIND_LABEL:
      break;

    case IR_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }
}

static void lir_print_register(VirtualRegister reg) {
  if (reg.value > lir_base_stack_pointer.value) {
    printf("reg%lu", reg.value);
  } else {
    printf("rbp");
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
      switch (loc.kind) {
      case MEMORY_LOCATION_KIND_REGISTER:
        lir_print_register(loc.reg);
        break;
      case MEMORY_LOCATION_KIND_STACK: {
        printf("[");
        lir_print_register(lir_base_stack_pointer);
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

static void lir_emitter_print_lirs(LirEmitter emitter) {
  for (u64 i = 0; i < emitter.instructions.len; i++) {
    LirInstruction lir = PG_SLICE_AT(emitter.instructions, i);
    printf("[%" PRIu64 "]\n", i);

    lir_print_var_to_memory_location(lir.var_to_memory_location_frozen);

    origin_print(lir.origin);
    printf(": ");

    switch (lir.kind) {
    case LIR_KIND_ADD:
      printf("add ");
      break;
    case LIR_KIND_SUB:
      printf("sub ");
      break;
    case LIR_KIND_MOV:
      printf("mov ");
      break;
    case LIR_KIND_SYSCALL:
      printf("syscall ");
      break;
    case LIR_KIND_LOAD_EFFECTIVE_ADDRESS:
      printf("lea ");
      break;
    case LIR_KIND_JUMP_IF_EQ:
      printf("je ");
      break;
    case LIR_KIND_JUMP:
      printf("jmp ");
      break;
    case LIR_KIND_LABEL:
      PG_ASSERT(0 && "todo");
    case LIR_KIND_CMP:
      printf("cmp ");
      break;
    case LIR_KIND_NONE:
    default:
      PG_ASSERT(0);
    }

    for (u64 j = 0; j < lir.operands.len; j++) {
      LirOperand op = PG_SLICE_AT(lir.operands, j);
      lir_print_operand(op);

      if (j + 1 < lir.operands.len) {
        printf(", ");
      }
    }
    printf("\n");
  }
}
