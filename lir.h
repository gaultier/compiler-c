#pragma once
#include "ir.h"
#include "submodules/cstd/lib.c"

typedef enum {
  LIR_VIRT_REG_CONSTRAINT_NONE,
  LIR_VIRT_REG_CONSTRAINT_CONDITION_FLAGS,
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
} VirtualRegister;
PG_SLICE(VirtualRegister) VirtualRegisterSlice;
PG_DYN(VirtualRegister) VirtualRegisterDyn;

typedef struct {
  u32 value;
} VirtualRegisterIndex;

typedef struct {
  u32 value;
} InterferenceNodeIndex;
PG_SLICE(InterferenceNodeIndex) InterferenceNodeIndexSlice;
PG_DYN(InterferenceNodeIndex) InterferenceNodeIndexDyn;

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
  LIR_INSTRUCTION_KIND_JUMP_IF_EQ,
  LIR_INSTRUCTION_KIND_JUMP,
  LIR_INSTRUCTION_KIND_LABEL,
  LIR_INSTRUCTION_KIND_CMP,
  LIR_INSTRUCTION_KIND_ADDRESS_OF,
  LIR_INSTRUCTION_KIND_COMPARISON,
  LIR_INSTRUCTION_KIND_SYSCALL,
} LirInstructionKind;

typedef enum {
  LIR_OPERAND_KIND_NONE,
  LIR_OPERAND_KIND_VIRTUAL_REGISTER,
  LIR_OPERAND_KIND_IMMEDIATE,
  LIR_OPERAND_KIND_LABEL,
} LirOperandKind;

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

typedef struct {
  LirInstructionKind kind;
  LirOperandDyn operands;
  Origin origin;
  LexTokenKind token_kind;
} LirInstruction;
PG_SLICE(LirInstruction) LirInstructionSlice;
PG_DYN(LirInstruction) LirInstructionDyn;

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

  IrVarLifetimeDyn lifetimes;
} LirEmitter;

[[nodiscard]]
static char *
lir_register_constraint_to_cstr(LirVirtualRegisterConstraint constraint) {
  switch (constraint) {
  case LIR_VIRT_REG_CONSTRAINT_NONE:
    return "NONE";
  case LIR_VIRT_REG_CONSTRAINT_CONDITION_FLAGS:
    return "CONDITION_FLAGS";
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
         virt_reg.addressable ? "true" : "false");
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
    printf("[%" PRIu64 "] ", i);

    origin_print(ins.origin);
    printf(": ");

    switch (ins.kind) {
    case LIR_INSTRUCTION_KIND_ADD:
      printf("add ");
      break;
    case LIR_INSTRUCTION_KIND_COMPARISON:
      printf("cmp-%s ",
             LEX_TOKEN_KIND_EQUAL_EQUAL == ins.token_kind ? "==" : "!=");
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
    case LIR_INSTRUCTION_KIND_JUMP_IF_EQ:
      printf("je ");
      break;
    case LIR_INSTRUCTION_KIND_JUMP:
      printf("jmp ");
      break;
    case LIR_INSTRUCTION_KIND_LABEL:
      break;
    case LIR_INSTRUCTION_KIND_ADDRESS_OF:
      printf("address_of ");
      break;
    case LIR_INSTRUCTION_KIND_CMP:
      PG_ASSERT(LEX_TOKEN_KIND_EQUAL_EQUAL == ins.token_kind);
      PG_ASSERT(3 == ins.operands.len);
      printf("cmp%s ",
             LEX_TOKEN_KIND_EQUAL_EQUAL == ins.token_kind ? "==" : "!=");
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

// We pass `IrOperand src` to be open to more immediate kinds in the future.
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

static void lir_emit_copy_to_virt_reg(LirEmitter *emitter, IrOperand src,
                                      VirtualRegisterIndex dst_idx,
                                      Origin origin, PgAllocator *allocator) {
  switch (src.kind) {
  case IR_OPERAND_KIND_U64:
    lir_emit_copy_immediate_to_virt_reg(emitter, src, dst_idx, origin,
                                        allocator);
    break;
  case IR_OPERAND_KIND_VAR: {
    VarVirtualRegisterIndex src_var_virt_reg_idx =
        var_virtual_registers_find_by_var(emitter->var_virtual_registers,
                                          src.var);
    PG_ASSERT(-1U != src_var_virt_reg_idx.value);
    VarVirtualRegister src_var_virt_reg =
        PG_SLICE_AT(emitter->var_virtual_registers, src_var_virt_reg_idx.value);

    lir_emit_copy_virt_reg_to_virt_reg(emitter, src_var_virt_reg.virt_reg_idx,
                                       dst_idx, origin, allocator);
  } break;
  case IR_OPERAND_KIND_LABEL:
  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]]
static LirOperand lir_ir_operand_to_lir_operand(LirEmitter emitter,
                                                IrOperand ir_op) {
  switch (ir_op.kind) {
  case IR_OPERAND_KIND_U64:
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_IMMEDIATE,
        .immediate = ir_op.n64,
    };
  case IR_OPERAND_KIND_VAR: {
    VarVirtualRegisterIndex var_virt_reg_idx =
        var_virtual_registers_find_by_var(emitter.var_virtual_registers,
                                          ir_op.var);
    PG_ASSERT(-1U != var_virt_reg_idx.value);
    VarVirtualRegister var_virt_reg =
        PG_SLICE_AT(emitter.var_virtual_registers, var_virt_reg_idx.value);

    return (LirOperand){
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .virt_reg_idx = var_virt_reg.virt_reg_idx,
    };
  }
  case IR_OPERAND_KIND_LABEL:
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_LABEL,
        .label = ir_op.label,
    };
  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
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

    lir_emit_copy_to_virt_reg(emitter, lhs_ir_val, res_virt_reg_idx,
                              ir_ins.origin, allocator);

    // We now need to add rhs to it.

    IrOperand rhs_ir_val = PG_SLICE_AT(ir_ins.operands, 1);
    PG_ASSERT(IR_OPERAND_KIND_VAR == rhs_ir_val.kind ||
              IR_OPERAND_KIND_U64 == rhs_ir_val.kind);

    LirOperand rhs_op = lir_ir_operand_to_lir_operand(*emitter, rhs_ir_val);
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

    lir_emit_copy_to_virt_reg(emitter, src_ir_val, res_virt_reg_idx,
                              ir_ins.origin, allocator);

  } break;
  case IR_INSTRUCTION_KIND_SYSCALL: {
    // PG_ASSERT(ir_ins.operands.len <=
    //           1 /* syscall num */ + lir_syscall_args_count);
    PG_ASSERT(ir_ins.operands.len > 0);

    for (u64 j = 0; j < ir_ins.operands.len; j++) {
      IrOperand val = PG_SLICE_AT(ir_ins.operands, j);
      LirVirtualRegisterConstraint virt_reg_constraint =
          (0 == j)
              ? LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM
              : (LirVirtualRegisterConstraint)(LIR_VIRT_REG_CONSTRAINT_SYSCALL0 +
                                               j - 1);
      VirtualRegisterIndex virt_reg_idx =
          lir_make_virtual_register(emitter, virt_reg_constraint, allocator);

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

#if 0
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
#endif
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
        .kind = LIR_INSTRUCTION_KIND_ADDRESS_OF,
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

  case IR_INSTRUCTION_KIND_COMPARISON: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.res_var.id.value);

    VirtualRegisterIndex res_virt_reg_idx = lir_reserve_virt_reg_for_var(
        emitter, ir_ins.res_var, LIR_VIRT_REG_CONSTRAINT_CONDITION_FLAGS,
        allocator);
    PG_ASSERT(-1U != res_virt_reg_idx.value);

    IrOperand ir_lhs = PG_SLICE_AT(ir_ins.operands, 0);
    IrOperand ir_rhs = PG_SLICE_AT(ir_ins.operands, 1);

    LirInstruction ins_cmp = {
        .kind = LIR_INSTRUCTION_KIND_CMP,
        .origin = ir_ins.origin,
        .token_kind = ir_ins.token_kind,
    };
    PG_DYN_ENSURE_CAP(&ins_cmp.operands, 3, allocator);

    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_cmp.operands) = (LirOperand){
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .virt_reg_idx = res_virt_reg_idx,
    };
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_cmp.operands) =
        lir_ir_operand_to_lir_operand(*emitter, ir_lhs);
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_cmp.operands) =
        lir_ir_operand_to_lir_operand(*emitter, ir_rhs);
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins_cmp;

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
