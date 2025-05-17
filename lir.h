#pragma once
#include "ir.h"
#include "submodules/cstd/lib.c"

// On all relevant targets (amd64, aarch64, riscv), syscalls take up to 6
// register arguments.
static const u64 max_syscall_args_count = 6;

typedef struct {
  u32 value;
} InterferenceNodeIndex;
PG_SLICE(InterferenceNodeIndex) InterferenceNodeIndexSlice;
PG_DYN(InterferenceNodeIndex) InterferenceNodeIndexDyn;

typedef struct {
  LabelId label_id;
  u64 code_address;
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
  LIR_INSTRUCTION_KIND_LABEL_DEFINITION,
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
  LIR_OPERAND_KIND_LABEL_ID,
} LirOperandKind;

typedef struct {
  LirOperandKind kind;
  union {
    IrMetadataIndex meta_idx;
    u64 immediate;
    LabelId jump_label_id; // LIR_OPERAND_KIND_LABEL_ID.
    Label label;           // LIR_OPERAND_KIND_LABEL.
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
  LirInstructionDyn instructions;
  IrMetadataDyn metadata;
} LirEmitter;

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

static void lir_print_operand(LirOperand op, IrMetadataDyn metadata) {
  switch (op.kind) {
  case LIR_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case LIR_OPERAND_KIND_VIRTUAL_REGISTER:
    IrMetadata meta = PG_SLICE_AT(metadata, op.meta_idx.value);
    ir_emitter_print_meta(meta);
    break;
  case LIR_OPERAND_KIND_IMMEDIATE:
    printf("%" PRIu64, op.immediate);
    break;
  case LIR_OPERAND_KIND_LABEL:
    PG_ASSERT(op.label.id.value);
    PG_ASSERT(op.label.name.value.len);

    printf(".%u-%.*s:\n", op.label.id.value, (i32)op.label.name.value.len,
           op.label.name.value.data);

    break;
  case LIR_OPERAND_KIND_LABEL_ID:
    PG_ASSERT(op.jump_label_id.value);
    printf(".%" PRIu32, op.jump_label_id.value);
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
    case LIR_INSTRUCTION_KIND_LABEL_DEFINITION:
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
      lir_print_operand(op, emitter.metadata);

      if (j + 1 < ins.operands.len) {
        printf(", ");
      }
    }
    printf("\n");
  }
}

static void lir_emit_copy_virt_reg_to_virt_reg(LirEmitter *emitter,
                                               IrMetadataIndex src_idx,
                                               IrMetadataIndex dst_idx,
                                               Origin origin,
                                               PgAllocator *allocator) {
  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand rhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .meta_idx = src_idx,
  };

  LirOperand lhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .meta_idx = dst_idx,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
}

// We pass `IrOperand src` to be open to more immediate kinds in the future.
static void lir_emit_copy_immediate_to_virt_reg(LirEmitter *emitter,
                                                IrOperand src_op,
                                                IrMetadataIndex dst_idx,
                                                Origin origin,
                                                PgAllocator *allocator) {
  // TODO: Expand when more immediate types are available.
  PG_ASSERT(IR_OPERAND_KIND_U64 == src_op.kind);

  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand lhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .meta_idx = dst_idx,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;

  LirOperand rhs = {
      .kind = LIR_OPERAND_KIND_IMMEDIATE,
      .immediate = src_op.n64,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
}

static void lir_emit_copy_to_virt_reg(LirEmitter *emitter, IrOperand src_op,
                                      IrMetadataIndex dst_meta_idx,
                                      Origin origin, PgAllocator *allocator) {
  switch (src_op.kind) {
  case IR_OPERAND_KIND_U64:
    lir_emit_copy_immediate_to_virt_reg(emitter, src_op, dst_meta_idx, origin,
                                        allocator);
    break;
  case IR_OPERAND_KIND_VAR: {
    lir_emit_copy_virt_reg_to_virt_reg(emitter, src_op.meta_idx, dst_meta_idx,
                                       origin, allocator);
  } break;
  case IR_OPERAND_KIND_LABEL:
  case IR_OPERAND_KIND_LABEL_ID:
  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]]
static LirOperand lir_ir_operand_to_lir_operand(IrOperand ir_op) {
  switch (ir_op.kind) {
  case IR_OPERAND_KIND_U64:
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_IMMEDIATE,
        .immediate = ir_op.n64,
    };
  case IR_OPERAND_KIND_VAR: {
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .meta_idx = ir_op.meta_idx,
    };
  }
  case IR_OPERAND_KIND_LABEL:
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_LABEL,
        .label = ir_op.label,
    };
  case IR_OPERAND_KIND_LABEL_ID:
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_LABEL_ID,
        .jump_label_id = ir_op.jump_label_id,
    };
  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void lir_emit_instruction(LirEmitter *emitter, IrInstruction ir_ins,
                                 PgAllocator *allocator) {
#if 0
  PG_ASSERT(!ir_ins.tombstone);
#endif

  switch (ir_ins.kind) {
  case IR_INSTRUCTION_KIND_ADD: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.meta_idx.value);

    IrOperand lhs_ir_val = PG_SLICE_AT(ir_ins.operands, 0);

    lir_emit_copy_to_virt_reg(emitter, lhs_ir_val, ir_ins.meta_idx,
                              ir_ins.origin, allocator);

    // We now need to add rhs to it.

    IrOperand rhs_ir_val = PG_SLICE_AT(ir_ins.operands, 1);
    PG_ASSERT(IR_OPERAND_KIND_VAR == rhs_ir_val.kind ||
              IR_OPERAND_KIND_U64 == rhs_ir_val.kind);

    LirOperand rhs_op = lir_ir_operand_to_lir_operand(rhs_ir_val);
    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_ADD,
        .origin = ir_ins.origin,
    };
    PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

    LirOperand lhs_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .meta_idx = ir_ins.meta_idx,
    };
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs_op;
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs_op;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

  } break;
  case IR_INSTRUCTION_KIND_LOAD: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.meta_idx.value);

    IrOperand src_ir_val = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_VAR == src_ir_val.kind ||
              IR_OPERAND_KIND_U64 == src_ir_val.kind);

    lir_emit_copy_to_virt_reg(emitter, src_ir_val, ir_ins.meta_idx,
                              ir_ins.origin, allocator);

  } break;
  case IR_INSTRUCTION_KIND_SYSCALL: {
    PG_ASSERT(ir_ins.operands.len <=
              1 /* syscall num */ + max_syscall_args_count);
    PG_ASSERT(ir_ins.operands.len > 0);

    for (u64 j = 0; j < ir_ins.operands.len; j++) {
      IrOperand val = PG_SLICE_AT(ir_ins.operands, j);
      LirVirtualRegisterConstraint virt_reg_constraint =
          (0 == j)
              ? LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM
              : (LirVirtualRegisterConstraint)(LIR_VIRT_REG_CONSTRAINT_SYSCALL0 +
                                               j - 1);
      PG_SLICE_AT(emitter->metadata, val.meta_idx.value)
          .virtual_register.constraint = virt_reg_constraint;

#if 0
      if (IR_OPERAND_KIND_U64 == val.kind) {
        lir_emit_copy_immediate_to_virt_reg(emitter, val, meta_idx,
                                            ir_ins.origin, allocator);
      } else if (IR_OPERAND_KIND_VAR == val.kind) {
        VarVirtualRegisterIndex src_var_virt_reg_idx =
            var_virtual_registers_find_by_var(emitter->var_virtual_registers,
                                              val.var);
        PG_ASSERT(-1U != src_var_virt_reg_idx.value);
        VarVirtualRegister src_var_virt_reg = PG_SLICE_AT(
            emitter->var_virtual_registers, src_var_virt_reg_idx.value);

        lir_emit_copy_virt_reg_to_virt_reg(emitter, src_var_virt_reg.meta_idx,
                                           meta_idx, ir_ins.origin, allocator);
      } else {
        PG_ASSERT(0);
      }
#endif
    }

    LirInstruction lir_ins = {
        .kind = LIR_INSTRUCTION_KIND_SYSCALL,
        .origin = ir_ins.origin,
    };
    *PG_DYN_PUSH(&emitter->instructions, allocator) = lir_ins;

  } break;
  case IR_INSTRUCTION_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.meta_idx.value);

    IrOperand lhs_ir_op = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_VAR == lhs_ir_op.kind);

    PG_SLICE_AT(emitter->metadata, ir_ins.meta_idx.value)
        .virtual_register.addressable = true;

    PG_ASSERT(lhs_ir_op.meta_idx.value != ir_ins.meta_idx.value);

    LirInstruction lir_ins = {
        .kind = LIR_INSTRUCTION_KIND_ADDRESS_OF,
        .origin = ir_ins.origin,
    };
    LirOperand lhs_lir_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .meta_idx = ir_ins.meta_idx,
    };
    LirOperand rhs_lir_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .meta_idx = lhs_ir_op.meta_idx,
    };
    *PG_DYN_PUSH(&lir_ins.operands, allocator) = lhs_lir_op;
    *PG_DYN_PUSH(&lir_ins.operands, allocator) = rhs_lir_op;
    *PG_DYN_PUSH(&emitter->instructions, allocator) = lir_ins;
  } break;
  case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.meta_idx.value);

    IrOperand branch_else = PG_SLICE_AT(ir_ins.operands, 1);
    PG_ASSERT(IR_OPERAND_KIND_LABEL_ID == branch_else.kind);

    LirInstruction ins_je = {
        .kind = LIR_INSTRUCTION_KIND_JUMP_IF_EQ,
        .origin = ir_ins.origin,
    };

    LirOperand ins_je_op = {
        .kind = LIR_OPERAND_KIND_LABEL_ID,
        .jump_label_id = branch_else.jump_label_id,
    };
    *PG_DYN_PUSH(&ins_je.operands, allocator) = ins_je_op;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins_je;
  } break;
  case IR_INSTRUCTION_KIND_JUMP: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.meta_idx.value);

    IrOperand op = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL_ID == op.kind);

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_JUMP,
        .origin = ir_ins.origin,
    };

    LirOperand lir_op = {
        .kind = LIR_OPERAND_KIND_LABEL_ID,
        .jump_label_id = op.jump_label_id,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = lir_op;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
  } break;
  case IR_INSTRUCTION_KIND_LABEL_DEFINITION: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.meta_idx.value);

    IrOperand op = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == op.kind);

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_LABEL_DEFINITION,
        .origin = ir_ins.origin,
    };

    LirOperand lir_op = {
        .kind = LIR_OPERAND_KIND_LABEL,
        .label = op.label,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = lir_op;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
  } break;

  case IR_INSTRUCTION_KIND_COMPARISON: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.meta_idx.value);

    PG_SLICE_AT(emitter->metadata, ir_ins.meta_idx.value)
        .virtual_register.constraint = LIR_VIRT_REG_CONSTRAINT_CONDITION_FLAGS;

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
        .meta_idx = ir_ins.meta_idx,
    };
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_cmp.operands) =
        lir_ir_operand_to_lir_operand(ir_lhs);
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_cmp.operands) =
        lir_ir_operand_to_lir_operand(ir_rhs);
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
