#pragma once
#include "asm_common.h"

typedef enum {
  // Register dereference or disp32 - Register.
  AMD64_MODRM_MOD_00 = 0b00,
  // Register dereference + disp8 - Register.
  AMD64_MODRM_MOD_01 = 0b01,
  // Register dereference + disp32 - Register.
  AMD64_MODRM_MOD_10 = 0b10,
  // Register - Register.
  AMD64_MODRM_MOD_11 = 0b11,
} Amd64ModRmMod;

#define AMD64_RAX 1
#define AMD64_RBX 2
#define AMD64_RCX 3
#define AMD64_RDX 4
#define AMD64_RDI 5
#define AMD64_RSI 6
#define AMD64_R8 7
#define AMD64_R9 8
#define AMD64_R12 9
#define AMD64_R13 10
#define AMD64_R14 11
#define AMD64_R15 12
#define AMD64_R10 13
#define AMD64_R11 14
#define AMD64_RSP 15
#define AMD64_RBP 16
#define AMD64_RFLAGS 17

static const Register amd64_register_allocator_gprs[] = {
    {AMD64_RAX},
    {AMD64_RDI},
    {AMD64_RSI},
    {AMD64_RDX},
    {AMD64_RCX},
    {AMD64_R8},
    {AMD64_R9},
    /* Reserved for spilling: AMD64_R10, AMD64_R11.*/
    {AMD64_RBX},
    {AMD64_R12},
    {AMD64_R13},
    {AMD64_R14},
    {AMD64_R15},
};

static const RegisterSlice amd64_register_allocator_gprs_slice = {
    .data = (Register *)amd64_register_allocator_gprs,
    .len = PG_STATIC_ARRAY_LEN(amd64_register_allocator_gprs),
};

static const char *amd64_register_to_string[][8 + 1] = {
    [AMD64_RAX] = {[1] = "al", [2] = "ax", [4] = "eax", [8] = "rax"},
    [AMD64_RBX] = {[1] = "bl", [2] = "bx", [4] = "ebx", [8] = "rbx"},
    [AMD64_RCX] = {[1] = "cl", [2] = "cx", [4] = "ecx", [8] = "rcx"},
    [AMD64_RDX] = {[1] = "dl", [2] = "dx", [4] = "edx", [8] = "rdx"},
    [AMD64_RDI] = {[1] = "dil", [2] = "di", [4] = "edi", [8] = "rdi"},
    [AMD64_RSI] = {[1] = "sil", [2] = "si", [4] = "esi", [8] = "rsi"},
    [AMD64_R8] = {[1] = "r8b", [2] = "r8w", [4] = "r8d", [8] = "r8"},
    [AMD64_R9] = {[1] = "r9b", [2] = "r9w", [4] = "r9d", [8] = "r9"},
    [AMD64_R10] = {[1] = "r10b", [2] = "r10w", [4] = "r10d", [8] = "r10"},
    [AMD64_R11] = {[1] = "r11b", [2] = "r11w", [4] = "r11d", [8] = "r11"},
    [AMD64_R12] = {[1] = "r12b", [2] = "r12w", [4] = "r12d", [8] = "r12"},
    [AMD64_R13] = {[1] = "r13b", [2] = "r13w", [4] = "r13d", [8] = "r13"},
    [AMD64_R14] = {[1] = "r14b", [2] = "r14w", [4] = "r14d", [8] = "r14"},
    [AMD64_R15] = {[1] = "r15b", [2] = "r15w", [4] = "r15d", [8] = "r15"},
    [AMD64_RSP] = {[1] = "spl", [2] = "sp", [4] = "esp", [8] = "rsp"},
    [AMD64_RBP] = {[1] = "bpl", [2] = "bp", [4] = "ebp", [8] = "rbp"},
    [AMD64_RFLAGS] =
        {[1] = "rflags", [2] = "rflags", [4] = "rflags", [8] = "rflags"},
};

static const u8 amd64_register_to_encoded_value[16 + 1] = {
    [AMD64_RAX] = 0b0000, [AMD64_RBX] = 0b0011, [AMD64_RCX] = 0b0001,
    [AMD64_RDX] = 0b0010, [AMD64_RDI] = 0b0111, [AMD64_RSI] = 0b0110,
    [AMD64_R8] = 0b1000,  [AMD64_R9] = 0b1001,  [AMD64_R10] = 0b1010,
    [AMD64_R11] = 0b1011, [AMD64_R12] = 0b1100, [AMD64_R13] = 0b1101,
    [AMD64_R14] = 0b1110, [AMD64_R15] = 0b1111, [AMD64_RSP] = 0b0100,
    [AMD64_RBP] = 0b0101,
};

static const char *amd64_size_to_operand_size_string[8 + 1] = {
    [ASM_OPERAND_SIZE_1] = "byte",
    [ASM_OPERAND_SIZE_2] = "word",
    [ASM_OPERAND_SIZE_4] = "dword",
    [ASM_OPERAND_SIZE_8] = "qword",
};

static const Pgu8Slice amd64_register_to_encoded_value_slice = {
    .data = (u8 *)amd64_register_to_encoded_value,
    .len = PG_STATIC_ARRAY_LEN(amd64_register_to_encoded_value),
};

// TODO: SystemV ABI vs Windows calling convention!
static const Register amd64_callee_saved[] = {
    {AMD64_RBX}, {AMD64_RSP}, {AMD64_RBP}, {AMD64_R12},
    {AMD64_R13}, {AMD64_R14}, {AMD64_R15},
};

static const Register amd64_caller_saved[] = {
    {AMD64_RAX}, {AMD64_RDI}, {AMD64_RDX}, {AMD64_RCX},
    {AMD64_R8},  {AMD64_R9},  {AMD64_R10}, {AMD64_R11},
};

static const Register amd64_spill_registers[] = {{AMD64_R10}, {AMD64_R11}};

static const Register amd64_calling_convention[] = {
    {AMD64_RDI}, {AMD64_RSI}, {AMD64_RDX}, {AMD64_RCX}, {AMD64_R8}, {AMD64_R9},
};

static const Register amd64_syscall_calling_convention[6] = {
    {AMD64_RDI}, {AMD64_RSI}, {AMD64_RDX}, {AMD64_R10}, {AMD64_R8}, {AMD64_R9},
};

static const Architecture amd64_arch = {
    .return_value = {AMD64_RAX},
    .caller_saved =
        {
            .data = (Register *)amd64_caller_saved,
            .len = PG_STATIC_ARRAY_LEN(amd64_caller_saved),
        },
    .callee_saved =
        {
            .data = (Register *)amd64_callee_saved,
            .len = PG_STATIC_ARRAY_LEN(amd64_callee_saved),
        },
    .calling_convention =
        {
            .data = (Register *)amd64_calling_convention,
            .len = PG_STATIC_ARRAY_LEN(amd64_calling_convention),
        },
    .syscall_calling_convention =
        {
            .data = (Register *)amd64_syscall_calling_convention,
            .len = PG_STATIC_ARRAY_LEN(amd64_syscall_calling_convention),
        },
    .syscall_num = {AMD64_RAX},
    .syscall_ret = {AMD64_RAX},
    .stack_pointer = {AMD64_RSP},
    .base_pointer = {AMD64_RBP},
    .gprs = amd64_register_allocator_gprs_slice,
};

[[nodiscard]] static bool amd64_is_reg(Amd64Operand op) {
  return AMD64_OPERAND_KIND_REGISTER == op.kind;
}

[[nodiscard]] static bool amd64_is_mem(Amd64Operand op) {
  return AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == op.kind;
}

[[nodiscard]] static bool amd64_is_imm(Amd64Operand op) {
  return AMD64_OPERAND_KIND_IMMEDIATE == op.kind;
}

[[nodiscard]] static bool amd64_is_reg8(Amd64Operand op) {
  return amd64_is_reg(op) && ASM_OPERAND_SIZE_1 == op.size;
}

[[nodiscard]] static bool amd64_has_displacement(Amd64Operand op) {
  return amd64_is_mem(op) && op.u.effective_address.displacement;
}

static void amd64_print_register(FILE *out, Register reg, AsmOperandSize size) {
  fprintf(out, "%s", amd64_register_to_string[reg.value][size]);
}

// TODO: If any of the callee-saved registers were used by the register
// allocator, emit storing code (push).
static void amd64_emit_prolog(AsmCodeSection *section, PgAllocator *allocator) {
  if (AST_NODE_FLAG_FN_NO_FRAME_POINTERS & section->flags) {
    return;
  }

  Amd64Instruction ins_push = {
      .kind = AMD64_INSTRUCTION_KIND_PUSH,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = {AMD64_RBP},
              .size = ASM_OPERAND_SIZE_8,
          },
  };
  *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_push;

  Amd64Instruction ins_mov = {
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = {AMD64_RBP},
              .size = ASM_OPERAND_SIZE_8,
          },
      .rhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = {AMD64_RSP},
              .size = ASM_OPERAND_SIZE_8,
          },
  };
  *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_mov;
}

// TODO: If any of the callee-saved registers were used by the register
// allocator, emit loading code (pop).
static void amd64_emit_epilog(AsmCodeSection *section, PgAllocator *allocator) {
  if (AST_NODE_FLAG_FN_NO_FRAME_POINTERS & section->flags) {
    return;
  }

  Amd64Instruction ins_pop = {
      .kind = AMD64_INSTRUCTION_KIND_POP,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = {AMD64_RBP},
              .size = ASM_OPERAND_SIZE_8,
          },
  };
  *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_pop;
}

static void amd64_print_operand(FILE *out, Amd64Operand op, bool with_op_size) {
  switch (op.kind) {
  case AMD64_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_OPERAND_KIND_REGISTER:
    amd64_print_register(out, op.u.reg, op.size);
    break;
  case AMD64_OPERAND_KIND_IMMEDIATE:
    fprintf(out, "%" PRIu64, op.u.immediate);
    break;
  case AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS: {
    if (with_op_size) {
      fprintf(out, "%s ptr ", amd64_size_to_operand_size_string[op.size]);
    }
    fprintf(out, "[");
    amd64_print_register(out, op.u.effective_address.base, ASM_OPERAND_SIZE_8);
    if (op.u.effective_address.index.value) {
      fprintf(out, " + ");
      amd64_print_register(out, op.u.effective_address.index,
                           ASM_OPERAND_SIZE_8);
      fprintf(out, " * %" PRIu8 " ", op.u.effective_address.scale);
    }
    fprintf(out, "%s%" PRIi32 "]",
            op.u.effective_address.displacement >= 0 ? "+" : "",
            op.u.effective_address.displacement);
  } break;
  case AMD64_OPERAND_KIND_LABEL:
    PG_ASSERT(op.u.label.value.data);
    PG_ASSERT(op.u.label.value.len);

    fprintf(out, "%.*s", (i32)op.u.label.value.len, op.u.label.value.data);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void amd64_print_instruction(FILE *out, Amd64Instruction ins,
                                    bool with_origin) {
  if (with_origin) {
    origin_print(out, ins.origin);
    fprintf(out, ": ");
  }

  // TODO: Validate operands?
  switch (ins.kind) {
  case AMD64_INSTRUCTION_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_INSTRUCTION_KIND_UD2:
    fprintf(out, "ud2 ");
    break;
  case AMD64_INSTRUCTION_KIND_MOV:
    fprintf(out, "mov ");
    break;
  case AMD64_INSTRUCTION_KIND_ADD:
    fprintf(out, "add ");
    break;
  case AMD64_INSTRUCTION_KIND_SUB:
    fprintf(out, "sub ");
    break;
  case AMD64_INSTRUCTION_KIND_LEA:
    fprintf(out, "lea ");
    break;
  case AMD64_INSTRUCTION_KIND_RET:
    fprintf(out, "ret ");
    break;
  case AMD64_INSTRUCTION_KIND_SYSCALL:
    fprintf(out, "syscall ");
    break;
  case AMD64_INSTRUCTION_KIND_PUSH:
    fprintf(out, "push ");
    break;
  case AMD64_INSTRUCTION_KIND_POP:
    fprintf(out, "pop ");
    break;
  case AMD64_INSTRUCTION_KIND_LABEL_DEFINITION:
    // The operand carries the actual label.
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_EQ:
    PG_ASSERT(AMD64_OPERAND_KIND_LABEL == ins.lhs.kind);
    PG_ASSERT(AMD64_OPERAND_KIND_NONE == ins.rhs.kind);

    fprintf(out, "je ");
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_NOT_EQ:
    PG_ASSERT(AMD64_OPERAND_KIND_LABEL == ins.lhs.kind);
    PG_ASSERT(AMD64_OPERAND_KIND_NONE == ins.rhs.kind);

    fprintf(out, "jne ");
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_ZERO:
    PG_ASSERT(AMD64_OPERAND_KIND_LABEL == ins.lhs.kind);
    PG_ASSERT(AMD64_OPERAND_KIND_NONE == ins.rhs.kind);

    fprintf(out, "jz ");
    break;
  case AMD64_INSTRUCTION_KIND_JMP:
    fprintf(out, "jmp ");
    break;
  case AMD64_INSTRUCTION_KIND_CMP:
    fprintf(out, "cmp ");
    break;
  case AMD64_INSTRUCTION_KIND_SET_IF_EQ:
    fprintf(out, "sete ");
    break;
  default:
    PG_ASSERT(0);
    break;
  }

  bool has_effective_address = (amd64_is_mem(ins.lhs) || amd64_is_mem(ins.rhs));
  if (AMD64_OPERAND_KIND_NONE != ins.lhs.kind) {
    amd64_print_operand(out, ins.lhs, has_effective_address);
  }

  if (AMD64_OPERAND_KIND_NONE != ins.rhs.kind) {
    PG_ASSERT(AMD64_OPERAND_KIND_NONE != ins.lhs.kind);

    fprintf(out, ", ");
    amd64_print_operand(out, ins.rhs, has_effective_address);
  }

  if (AMD64_INSTRUCTION_KIND_LABEL_DEFINITION == ins.kind) {
    fprintf(out, ":");
  }
}

static void amd64_print_instructions(FILE *out,
                                     Amd64InstructionDyn instructions) {
  for (u64 i = 0; i < instructions.len; i++) {
    fprintf(out, "[%" PRIu64 "] ", i);

    Amd64Instruction ins = PG_SLICE_AT(instructions, i);

    amd64_print_instruction(stdout, ins, true);
    fprintf(out, "\n");
  }
}

static void amd64_print_section(FILE *out, AsmCodeSection section) {
  if (AST_NODE_FLAG_GLOBAL & section.flags) {
    fprintf(out, "global ");
    fprintf(out, "%.*s", (i32)section.name.len, section.name.data);
    fprintf(out, ":\n");
  }

  fprintf(out, "%.*s", (i32)section.name.len, section.name.data);
  fprintf(out, ":\n");

  amd64_print_instructions(out, section.u.amd64_instructions);
}

[[nodiscard]]
static u8 amd64_encode_register_value(Register reg) {
  return PG_SLICE_AT(amd64_register_to_encoded_value_slice, reg.value);
}

[[nodiscard]]
static u8 amd64_encode_register_value_3bits(Register reg) {
  return PG_SLICE_AT(amd64_register_to_encoded_value_slice, reg.value) & 0b111;
}

[[nodiscard]]
static bool amd64_is_register_64_bits_only(Register reg) {
  return amd64_encode_register_value(reg) > 0b111;
}

static const u8 AMD64_REX_DEFAULT = 0b0100'0000;
// Enable use of 64 operand size.
static const u8 AMD64_REX_MASK_W = 0b0000'1000;
// Enable use of 64 bits registers in the ModRM(reg) field.
static const u8 AMD64_REX_MASK_R = 0b0000'0100;
// Enable use of 64 bits registers in SIB.
static const u8 AMD64_REX_MASK_X = 0b0000'0010;
// Enable use of 64 bits registers in the ModRM(r/m) field.
static const u8 AMD64_REX_MASK_B = 0b0000'0001;

// No index register.
static const u8 AMD64_SIB_INDEX_NONE = 0b101'000;
// Base is not a register but a u32 displacement value.
static const u8 AMD64_SIB_BASE_DISP32 = 0b101;

static void amd64_encode_instruction_ud2(Pgu8Dyn *sb, PgAllocator *allocator) {
  u8 opcode1 = 0x0f;
  *PG_DYN_PUSH(sb, allocator) = opcode1;
  u8 opcode2 = 0x0b;
  *PG_DYN_PUSH(sb, allocator) = opcode2;
}

static void amd64_encode_16bits_prefix(Pgu8Dyn *sb, Amd64Operand op,
                                       PgAllocator *allocator) {
  if (ASM_OPERAND_SIZE_2 == op.size) {
    *PG_DYN_PUSH(sb, allocator) = 0x66;
  }
}

static void amd64_encode_rex(Pgu8Dyn *sb, bool upper_registers_modrm_reg_field,
                             bool upper_register_modrm_rm_field, bool field_w,
                             PgAllocator *allocator) {
  u8 rex = AMD64_REX_DEFAULT;

  if (upper_registers_modrm_reg_field) {
    rex |= AMD64_REX_MASK_R;
  }
  if (upper_register_modrm_rm_field) {
    rex |= AMD64_REX_MASK_B;
  }
  if (field_w) {
    rex |= AMD64_REX_MASK_W;
  }

  if (AMD64_REX_DEFAULT != rex) {
    *PG_DYN_PUSH(sb, allocator) = rex;
  }
}

#if 0
[[nodiscard]] static bool amd64_is_reg_or_mem8(Amd64Operand op) {
  return amd64_is_reg8(op) || (AMD64_OPERAND_KIND_IMMEDIATE == op.kind &&
                               op.u.immediate <= UINT8_MAX);
}

[[nodiscard]] static bool amd64_is_reg16(Amd64Operand op) {
  return amd64_is_reg(op)&&
         ASM_OPERAND_SIZE_2 == op.size;
}

[[nodiscard]] static bool amd64_is_reg_or_mem16(Amd64Operand op) {
  return amd64_is_reg16(op) || (AMD64_OPERAND_KIND_IMMEDIATE == op.kind &&
                                op.u.immediate <= UINT16_MAX);
}

[[nodiscard]] static bool amd64_is_reg32(Amd64Operand op) {
  return amd64_is_reg(op)&&
         ASM_OPERAND_SIZE_4 == op.size;
}

[[nodiscard]] static bool amd64_is_reg_or_mem32(Amd64Operand op) {
  return amd64_is_reg32(op) || (AMD64_OPERAND_KIND_IMMEDIATE == op.kind &&
                                op.u.immediate <= UINT32_MAX);
}

[[nodiscard]] static bool amd64_is_reg64(Amd64Operand op) {
  return amd64_is_reg(op)&&
         ASM_OPERAND_SIZE_8 == op.size;
}

[[nodiscard]] static bool amd64_is_reg_or_mem64(Amd64Operand op) {
  return amd64_is_reg64(op) || (AMD64_OPERAND_KIND_IMMEDIATE == op.kind &&
                                op.u.immediate <= UINT64_MAX);
}
#endif

[[nodiscard]]
static bool amd64_is_r_slash_m8(Amd64Operand op) {
  return amd64_is_reg8(op) || AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == op.kind;
}

static void amd64_encode_modrm(Pgu8Dyn *sb, Amd64Operand lhs, Amd64Operand rhs,
                               PgAllocator *allocator) {

  PG_ASSERT(amd64_is_reg(rhs));

  Amd64ModRmMod mod = 0;
  u8 reg = amd64_encode_register_value_3bits(rhs.u.reg);
  u8 rm = 0;
  if (amd64_is_reg(lhs)) {
    mod = AMD64_MODRM_MOD_11;
    rm = amd64_encode_register_value_3bits(lhs.u.reg);
  } else if (amd64_is_imm(lhs)) { // disp32
    mod = AMD64_MODRM_MOD_00;
    rm = 0b101;
  } else if (amd64_is_mem(lhs) &&
             lhs.u.effective_address.displacement <= UINT8_MAX) {
    mod = AMD64_MODRM_MOD_01;
    rm = amd64_encode_register_value_3bits(lhs.u.effective_address.base);
  } else if (amd64_is_mem(lhs) && 0 == lhs.u.effective_address.displacement) {
    mod = AMD64_MODRM_MOD_00;
    rm = amd64_encode_register_value_3bits(lhs.u.effective_address.base);
  } else if (amd64_is_mem(lhs)) {
    mod = AMD64_MODRM_MOD_10;
    rm = amd64_encode_register_value_3bits(lhs.u.effective_address.base);
  } else {
    PG_ASSERT(0);
  }

  // Encode.
  {
    PG_ASSERT(reg <= 0b111);
    PG_ASSERT(rm <= 0b111);

    u8 modrm = (u8)(mod << 6) | (u8)(reg << 3) | rm;
    *PG_DYN_PUSH(sb, allocator) = modrm;
  }
}

static void amd64_encode_instruction_mov(Pgu8Dyn *sb, Amd64Instruction ins,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_MOV == ins.kind);

  // MOV r/m8, r8
  // MOV r/m16, r16
  // MOV r/m32, r32
  // MOV r/m64, r64
  if ((amd64_is_reg(ins.lhs) || amd64_is_mem(ins.lhs)) &&
      amd64_is_reg(ins.rhs)) {
    PG_ASSERT(ins.lhs.size == ins.rhs.size);
    PG_ASSERT(0 != ins.lhs.size);

    Register rhs = ins.rhs.u.reg;

    // 16 bits prefix.
    {
      amd64_encode_16bits_prefix(sb, ins.lhs, allocator);
    }

    // Rex.
    {
      bool modrm_reg_field = amd64_is_register_64_bits_only(rhs);
      bool modrm_rm_field = amd64_is_reg(ins.lhs)
                                ? amd64_is_register_64_bits_only(ins.lhs.u.reg)
                                : false;
      bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
      amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, allocator);
    }

    // Opcode.
    {
      u8 opcode = 0x89;
      if (amd64_is_r_slash_m8(ins.lhs)) {
        opcode = 0x88;
      }
      *PG_DYN_PUSH(sb, allocator) = opcode;
    }

    // ModRM.
    {
      amd64_encode_modrm(sb, ins.lhs, ins.rhs, allocator);
    }
    // SIB.
    {
      if (amd64_is_mem(ins.lhs) && amd64_has_displacement(ins.lhs)) {
        PG_ASSERT(0 && "todo");
      }
    }
    return;
  }

#if 0
  // MOV reg64, imm64 | B8 +rq iq | Move an 64-bit immediate value into a 64-bit
  // register.
  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    Register reg = instruction.lhs.u.reg;
    u64 immediate = instruction.rhs.u.immediate;
    amd64_encode_rex(sb, amd64_is_register_64_bits_only(reg), false,
                     immediate > UINT32_MAX, allocator);

    u8 opcode = 0xb8;
    *PG_DYN_PUSH(sb, allocator) =
        opcode + (amd64_encode_register_value(reg) & 0b111);

    if (instruction.rhs.u.immediate <= UINT32_MAX) {
      pg_byte_buffer_append_u32(sb, (u32)immediate, allocator);
    } else {
      pg_byte_buffer_append_u64(sb, immediate, allocator);
    }

    return;
  }

  // MOV reg/mem64, reg64 | 89 /r | Move the contents of a 64-bit register to a
  // 64-bit destination register or memory operand.
  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    Register lhs_reg = instruction.lhs.u.reg;
    Register rhs_reg = instruction.rhs.u.reg;

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.u.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    if (amd64_is_register_64_bits_only(instruction.rhs.u.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;
    amd64_encode_rex(sb, amd64_is_register_64_bits_only(lhs_reg), false,
                     immediate > UINT32_MAX, allocator);

    u8 opcode = 0x89;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm = (0b11 << 6) |
               (u8)((amd64_encode_register_value(instruction.rhs.u.reg) & 0b111)
                    << 3) |
               (u8)(amd64_encode_register_value(instruction.lhs.u.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    return;
  }

  if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    PG_ASSERT(instruction.rhs.kind <= INT32_MAX);

    PG_ASSERT(AMD64_RBP == instruction.lhs.u.effective_address.base.value &&
              "todo");
    PG_ASSERT(0 == instruction.lhs.u.effective_address.index.value && "todo");
    PG_ASSERT(0 == instruction.lhs.u.effective_address.scale && "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.u.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0xc7;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm = (0b10 /* rbp+disp32 */ << 6) |
               (u8)(amd64_encode_register_value(
                        instruction.lhs.u.effective_address.base) &
                    0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(
        sb, (u32)instruction.lhs.u.effective_address.displacement, allocator);
    pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.u.immediate, allocator);

    return;
  }

  if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    PG_ASSERT(instruction.lhs.u.effective_address.base.value == AMD64_RBP &&
              "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(
            instruction.lhs.u.effective_address.base)) {
      rex |= AMD64_REX_MASK_B;
    }
    if (amd64_is_register_64_bits_only(instruction.rhs.u.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x89;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm = (0b10 /* [rbp] + disp32 */ << 6) |
               (u8)((amd64_encode_register_value(instruction.rhs.u.reg) & 0b111)
                    << 3) |
               (u8)(amd64_encode_register_value(
                        instruction.lhs.u.effective_address.base) &
                    0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(
        sb, (u32)instruction.lhs.u.effective_address.displacement, allocator);

    return;
  }

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.rhs.kind) {
    PG_ASSERT(AMD64_RBP == instruction.rhs.u.effective_address.base.value &&
              "todo");
    PG_ASSERT(0 == instruction.rhs.u.effective_address.index.value && "todo");
    PG_ASSERT(0 == instruction.rhs.u.effective_address.scale && "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.u.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    if (amd64_is_register_64_bits_only(
            instruction.rhs.u.effective_address.base)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x8b;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm = (0b10 /* [rbp] + disp32 */ << 6) |
               (u8)((amd64_encode_register_value(instruction.lhs.u.reg) & 0b111)
                    << 3) |
               (u8)(amd64_encode_register_value(
                        instruction.rhs.u.effective_address.base) &
                    0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(
        sb, (u32)instruction.rhs.u.effective_address.displacement, allocator);

    return;
  }
#endif

  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_lea(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_LEA == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind);
  PG_ASSERT(ASM_OPERAND_SIZE_8 == instruction.lhs.size);
  PG_ASSERT(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.rhs.kind);
  PG_ASSERT(0 == instruction.rhs.u.effective_address.index.value && "todo");
  PG_ASSERT(0 == instruction.rhs.u.effective_address.scale && "todo");
  PG_ASSERT(AMD64_RBP == instruction.rhs.u.effective_address.base.value &&
            "todo");

  u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
  if (amd64_is_register_64_bits_only(instruction.lhs.u.reg)) {
    rex |= AMD64_REX_MASK_R;
  }
  if (amd64_is_register_64_bits_only(
          instruction.rhs.u.effective_address.base)) {
    rex |= AMD64_REX_MASK_B;
  }

  *PG_DYN_PUSH(sb, allocator) = rex;

  u8 opcode = 0x8d;
  *PG_DYN_PUSH(sb, allocator) = opcode;

  u8 modrm =
      (0b10 /* [rbp] + disp32 */ << 6) |
      (u8)((amd64_encode_register_value(instruction.lhs.u.reg) & 0b111) << 3) |
      (u8)((amd64_encode_register_value(
                instruction.rhs.u.effective_address.base) &
            0b111));
  *PG_DYN_PUSH(sb, allocator) = modrm;

  pg_byte_buffer_append_u32_within_capacity(
      sb, (u32)instruction.rhs.u.effective_address.displacement);
  return;
}

static void amd64_encode_instruction_ret(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  (void)sb;
  (void)instruction;
  (void)allocator;
}

static void amd64_encode_instruction_add(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_ADD == instruction.kind);

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.u.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    if (amd64_is_register_64_bits_only(instruction.rhs.u.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x03;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) |
               (u8)((amd64_encode_register_value(instruction.lhs.u.reg) & 0b111)
                    << 3) |
               (u8)(amd64_encode_register_value(instruction.rhs.u.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;
    return;
  }

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    PG_ASSERT(instruction.rhs.u.immediate <= INT32_MAX);

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.u.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x81;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm =
        (0b11 << 6) |
        (u8)((amd64_encode_register_value(instruction.lhs.u.reg) & 0b111));
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.u.immediate, allocator);
    return;
  }
  if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    PG_ASSERT(0 == instruction.lhs.u.effective_address.scale && "todo");
    PG_ASSERT(0 == instruction.lhs.u.effective_address.index.value && "todo");
    PG_ASSERT(AMD64_RBP == instruction.lhs.u.effective_address.base.value &&
              "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.rhs.u.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x01;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b10 /* rbp+disp32 */ << 6) |
               (u8)((amd64_encode_register_value(instruction.rhs.u.reg) & 0b111)
                    << 3) |
               (u8)(amd64_encode_register_value(
                   instruction.lhs.u.effective_address.base));

    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(
        sb, (u32)instruction.lhs.u.effective_address.displacement, allocator);

    return;
  }
  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.rhs.kind) {
    Register reg = instruction.lhs.u.reg;
    Amd64EffectiveAddress effective_address =
        instruction.rhs.u.effective_address;
    PG_ASSERT(0 == effective_address.scale && "todo");
    PG_ASSERT(0 == effective_address.index.value && "todo");
    PG_ASSERT(AMD64_RBP == effective_address.base.value && "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x03;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b10 /* rbp+disp32 */ << 6) |
               (u8)((amd64_encode_register_value(reg) & 0b111) << 3) |
               (u8)(amd64_encode_register_value(effective_address.base));

    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)effective_address.displacement,
                              allocator);

    return;
  }
  if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    u64 immediate = instruction.rhs.u.immediate;
    PG_ASSERT(immediate <= INT32_MAX);
    Amd64EffectiveAddress effective_address =
        instruction.lhs.u.effective_address;

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(effective_address.base)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x81;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b10 /* rbp+disp32 */ << 6) |
               (u8)(amd64_encode_register_value(effective_address.base));

    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)effective_address.displacement,
                              allocator);
    pg_byte_buffer_append_u32(sb, (u32)immediate, allocator);
    return;
  }
  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_sub(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_SUB == instruction.kind);

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.u.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    if (amd64_is_register_64_bits_only(instruction.rhs.u.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x29;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) |
               (u8)((amd64_encode_register_value(instruction.lhs.u.reg) & 0b111)
                    << 3) |
               (u8)(amd64_encode_register_value(instruction.rhs.u.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;
    return;
  }

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.u.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    PG_ASSERT(instruction.rhs.u.immediate <= UINT32_MAX);

    u8 opcode = 0x81;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) | (u8)(5 << 3) |
               (u8)(amd64_encode_register_value(instruction.lhs.u.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.u.immediate, allocator);
    return;
  }
  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_syscall(Pgu8Dyn *sb,
                                             Amd64Instruction instruction,
                                             PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_SYSCALL == instruction.kind);

  PG_DYN_APPEND_SLICE(sb, PG_S("\x0f\x05"), allocator);
}

static void amd64_encode_instruction_push(Pgu8Dyn *sb,
                                          Amd64Instruction instruction,
                                          PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_PUSH == instruction.kind);
  PG_ASSERT(AMD64_RBP == instruction.lhs.u.reg.value && "todo");

  u8 opcode = 0x50;
  *PG_DYN_PUSH(sb, allocator) =
      opcode + (amd64_encode_register_value(instruction.lhs.u.reg) & 0b111);
}

static void amd64_encode_instruction_pop(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_POP == instruction.kind);

  PG_ASSERT(AMD64_RBP == instruction.lhs.u.reg.value && "todo");

  u8 opcode = 0x58;
  *PG_DYN_PUSH(sb, allocator) =
      opcode + (amd64_encode_register_value(instruction.lhs.u.reg) & 0b111);
}

static void amd64_encode_instruction_je(Pgu8Dyn *sb,
                                        Amd64Instruction instruction,
                                        AsmProgram *program,
                                        PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_JMP_IF_EQ == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_LABEL == instruction.lhs.kind);
  PG_ASSERT(instruction.lhs.u.label.value.len);

  u8 opcode1 = 0x0f;
  *PG_DYN_PUSH(sb, allocator) = opcode1;

  u8 opcode2 = 0x84;
  *PG_DYN_PUSH(sb, allocator) = opcode2;

  *PG_DYN_PUSH(&program->jumps_to_backpatch, allocator) = (LabelAddress){
      .label = instruction.lhs.u.label,
      .code_address = sb->len,
  };

  // Backpatched with `program.label_addresses`.
  pg_byte_buffer_append_u32(sb, 0, allocator);
}

static void amd64_encode_instruction_jne(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         AsmProgram *program,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_JMP_IF_NOT_EQ == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_LABEL == instruction.lhs.kind);
  PG_ASSERT(instruction.lhs.u.label.value.len);

  u8 opcode1 = 0x0f;
  *PG_DYN_PUSH(sb, allocator) = opcode1;

  u8 opcode2 = 0x85;
  *PG_DYN_PUSH(sb, allocator) = opcode2;

  *PG_DYN_PUSH(&program->jumps_to_backpatch, allocator) = (LabelAddress){
      .label = instruction.lhs.u.label,
      .code_address = sb->len,
  };

  // Backpatched with `program.label_addresses`.
  pg_byte_buffer_append_u32(sb, 0, allocator);
}

static void amd64_encode_instruction_jz(Pgu8Dyn *sb,
                                        Amd64Instruction instruction,
                                        AsmProgram *program,
                                        PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_JMP_IF_ZERO == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_LABEL == instruction.lhs.kind);
  PG_ASSERT(instruction.lhs.u.label.value.len);

  u8 opcode1 = 0x0f;
  *PG_DYN_PUSH(sb, allocator) = opcode1;

  u8 opcode2 = 0x84;
  *PG_DYN_PUSH(sb, allocator) = opcode2;

  *PG_DYN_PUSH(&program->jumps_to_backpatch, allocator) = (LabelAddress){
      .label = instruction.lhs.u.label,
      .code_address = sb->len,
  };

  // Backpatched with `program.label_addresses`.
  pg_byte_buffer_append_u32(sb, 0, allocator);
}

static void amd64_encode_instruction_jmp(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         AsmProgram *program,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_JMP == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_LABEL == instruction.lhs.kind);
  PG_ASSERT(instruction.lhs.u.label.value.len);

  u8 opcode = 0xe9;
  *PG_DYN_PUSH(sb, allocator) = opcode;

  *PG_DYN_PUSH(&program->jumps_to_backpatch, allocator) = (LabelAddress){
      .label = instruction.lhs.u.label,
      .code_address = sb->len,
  };

  // Backpatched with `program.label_addresses`.
  pg_byte_buffer_append_u32(sb, 0, allocator);
}

static void amd64_encode_instruction_cmp(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_CMP == instruction.kind);

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    Register reg = instruction.lhs.u.reg;
    u64 immediate = instruction.rhs.u.immediate;

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    PG_ASSERT(immediate <= INT32_MAX);

    u8 opcode = 0x81;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) | (u8)(7 << 3) |
               (u8)(amd64_encode_register_value(reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)immediate, allocator);
    return;
  }

  if (AMD64_OPERAND_KIND_IMMEDIATE == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    PG_ASSERT(0 && "unsupported");
  }

  if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    u64 immediate = instruction.rhs.u.immediate;
    Amd64EffectiveAddress effective_address =
        instruction.lhs.u.effective_address;
    PG_ASSERT(effective_address.base.value == AMD64_RBP && "todo");
    PG_ASSERT(0 == effective_address.index.value);
    PG_ASSERT(0 == effective_address.scale);

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(effective_address.base)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    PG_ASSERT(immediate <= INT32_MAX);

    u8 opcode = 0x81;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm =
        (0b10 /* rbp+disp32 */ << 6) | (u8)(7 << 3) |
        (u8)(amd64_encode_register_value(effective_address.base) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)effective_address.displacement,
                              allocator);
    pg_byte_buffer_append_u32(sb, (u32)immediate, allocator);
    return;
  }

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    Register lhs_reg = instruction.lhs.u.reg;
    Register rhs_reg = instruction.rhs.u.reg;

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(lhs_reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    if (amd64_is_register_64_bits_only(rhs_reg)) {
      rex |= AMD64_REX_MASK_B;
    }

    u8 opcode = 0x3B;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) |
               (u8)((amd64_encode_register_value(lhs_reg) & 0b111) << 3) |
               (u8)(amd64_encode_register_value(rhs_reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;
    return;
  }

  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_sete(Pgu8Dyn *sb,
                                          Amd64Instruction instruction,
                                          PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_SET_IF_EQ == instruction.kind);

  u8 opcode1 = 0x0F;
  u8 opcode2 = 0x94;
  *PG_DYN_PUSH(sb, allocator) = opcode1;
  *PG_DYN_PUSH(sb, allocator) = opcode2;

  PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind);
  Register reg = instruction.lhs.u.reg;

  u8 modrm = (0b11 << 6) |

             (u8)(amd64_encode_register_value(reg) & 0b111);
  *PG_DYN_PUSH(sb, allocator) = modrm;
}

static void amd64_encode_instruction(AsmProgram *program, Pgu8Dyn *sb,
                                     Amd64Instruction instruction,
                                     PgAllocator *allocator) {

  switch (instruction.kind) {
  case AMD64_INSTRUCTION_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_INSTRUCTION_KIND_UD2:
    amd64_encode_instruction_ud2(sb, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_MOV:
    amd64_encode_instruction_mov(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_ADD:
    amd64_encode_instruction_add(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_SUB:
    amd64_encode_instruction_sub(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_LEA:
    amd64_encode_instruction_lea(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_RET:
    amd64_encode_instruction_ret(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_SYSCALL:
    amd64_encode_instruction_syscall(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_PUSH:
    amd64_encode_instruction_push(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_POP:
    amd64_encode_instruction_pop(sb, instruction, allocator);
    break;

  case AMD64_INSTRUCTION_KIND_LABEL_DEFINITION:
    PG_ASSERT(instruction.lhs.u.label.value.len);

    *PG_DYN_PUSH(&program->label_addresses, allocator) = (LabelAddress){
        .label = instruction.lhs.u.label,
        .code_address = sb->len,
    };
    break;

  case AMD64_INSTRUCTION_KIND_JMP_IF_EQ:
    amd64_encode_instruction_je(sb, instruction, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_NOT_EQ:
    amd64_encode_instruction_jne(sb, instruction, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_ZERO:
    amd64_encode_instruction_jz(sb, instruction, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP:
    amd64_encode_instruction_jmp(sb, instruction, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_CMP:
    amd64_encode_instruction_cmp(sb, instruction, allocator);
    break;

  case AMD64_INSTRUCTION_KIND_SET_IF_EQ:
    amd64_encode_instruction_sete(sb, instruction, allocator);
    break;

  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static Amd64Operand
amd64_convert_memory_location_to_amd64_operand(MetadataIndex meta_idx,
                                               MetadataDyn metadata) {
  PG_ASSERT(meta_idx.value);
  Metadata meta = PG_SLICE_AT(metadata, meta_idx.value);
  MemoryLocation mem_loc = meta.memory_location;

  switch (mem_loc.kind) {
  case MEMORY_LOCATION_KIND_REGISTER: {
    PG_ASSERT(MEMORY_LOCATION_KIND_REGISTER == mem_loc.kind);
    PG_ASSERT(mem_loc.u.reg.value);

    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_REGISTER,
        .u.reg = mem_loc.u.reg,
        .size = asm_type_size_to_operand_size(meta.type->size),
    };
  }
  case MEMORY_LOCATION_KIND_STATUS_REGISTER:
    PG_ASSERT(0 && "todo");
    break;
  case MEMORY_LOCATION_KIND_STACK: {
    PG_ASSERT(mem_loc.u.base_pointer_offset);
    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
        .u.effective_address =
            {
                .base = {AMD64_RBP},
                .displacement = -mem_loc.u.base_pointer_offset,
            },
        .size = asm_type_size_to_operand_size(meta.type->size),
    };
  }
  case MEMORY_LOCATION_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static Amd64Operand
amd64_convert_ir_operand_to_amd64_operand(IrOperand op, MetadataDyn metadata) {
  if (IR_OPERAND_KIND_NUM == op.kind) {
    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_IMMEDIATE,
        .u.immediate = op.u.u64,
        .size = ASM_OPERAND_SIZE_8,
    };
  }

  if (IR_OPERAND_KIND_LABEL == op.kind) {
    PG_ASSERT(op.u.label.value.len);
    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_LABEL,
        .u.label = op.u.label,
        .size = ASM_OPERAND_SIZE_4,
    };
  }

  PG_ASSERT(IR_OPERAND_KIND_VREG == op.kind);
  PG_ASSERT(op.u.vreg_meta_idx.value);
  return amd64_convert_memory_location_to_amd64_operand(op.u.vreg_meta_idx,
                                                        metadata);
}

static void amd64_sanity_check_section(AsmCodeSection section) {
  for (u64 i = 0; i < section.u.amd64_instructions.len; i++) {
    Amd64Instruction ins = PG_SLICE_AT(section.u.amd64_instructions, i);

    // Prohibited by amd64 rules.
    PG_ASSERT(!(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.lhs.kind &&
                AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.rhs.kind));

    PG_ASSERT(!(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.lhs.kind &&
                AMD64_OPERAND_KIND_IMMEDIATE == ins.rhs.kind));

    PG_ASSERT(!(AMD64_OPERAND_KIND_IMMEDIATE == ins.lhs.kind &&
                AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.rhs.kind));

    PG_ASSERT(!(AMD64_OPERAND_KIND_IMMEDIATE == ins.lhs.kind &&
                AMD64_OPERAND_KIND_IMMEDIATE == ins.rhs.kind));

    if (ins.lhs.kind) {
      PG_ASSERT(ins.lhs.size);
    }

    if (ins.rhs.kind) {
      PG_ASSERT(ins.rhs.size);
    }
  }
}

static void amd64_emit_fn_body(AsmCodeSection *section, FnDefinition fn_def,
                               PgAllocator *allocator) {

  for (u32 i = 0; i < fn_def.instructions.len; i++) {
    IrInstruction ins = PG_SLICE_AT(fn_def.instructions, i);

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_MOV: {
      PG_ASSERT(ins.meta_idx.value);
      Amd64Instruction ins_mov = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(ins.lhs,
                                                           fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(ins.rhs,
                                                           fn_def.metadata),
          .origin = ins.origin,
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_mov;

    } break;

    case IR_INSTRUCTION_KIND_COMPARISON: {
      PG_ASSERT(ins.lhs.kind);
      PG_ASSERT(ins.rhs.kind);
      PG_ASSERT(ins.meta_idx.value);

      Amd64Instruction ins_cmp = {
          .kind = AMD64_INSTRUCTION_KIND_CMP,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(ins.lhs,
                                                           fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(ins.rhs,
                                                           fn_def.metadata),
          .origin = ins.origin,
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_cmp;

      Amd64Instruction ins_sete = {
          .kind = AMD64_INSTRUCTION_KIND_SET_IF_EQ,
          .lhs = amd64_convert_memory_location_to_amd64_operand(
              ins.meta_idx, fn_def.metadata),
          .origin = ins.origin,
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_sete;
    } break;

    case IR_INSTRUCTION_KIND_ADD: {
      PG_ASSERT(ins.lhs.kind);
      PG_ASSERT(ins.rhs.kind);
      PG_ASSERT(ins.meta_idx.value);

      Amd64Instruction ins_mov = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs = amd64_convert_memory_location_to_amd64_operand(
              ins.meta_idx, fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(ins.lhs,
                                                           fn_def.metadata),
          .origin = ins.origin,
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_mov;

      Amd64Instruction ins_add = {
          .kind = AMD64_INSTRUCTION_KIND_ADD,
          .lhs = amd64_convert_memory_location_to_amd64_operand(
              ins.meta_idx, fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(ins.rhs,
                                                           fn_def.metadata),
          .origin = ins.origin,
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_add;
    } break;

    case IR_INSTRUCTION_KIND_TRAP: {
      Amd64Instruction ins_ud2 = {
          .kind = AMD64_INSTRUCTION_KIND_UD2,
          .origin = ins.origin,
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_ud2;
    } break;

    case IR_INSTRUCTION_KIND_JUMP: {
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.lhs.kind);

      Amd64Instruction ins_jmp = {
          .kind = AMD64_INSTRUCTION_KIND_JMP,
          .origin = ins.origin,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(ins.lhs,
                                                           fn_def.metadata),
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_jmp;
    } break;

    case IR_INSTRUCTION_KIND_SYSCALL: {
      Amd64Instruction ins_sys = {
          .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
          .origin = ins.origin,
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_sys;
    } break;

    case IR_INSTRUCTION_KIND_LOAD_ADDRESS: {
      Amd64Instruction ins_lea = {
          .kind = AMD64_INSTRUCTION_KIND_LEA,
          .origin = ins.origin,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(ins.lhs,
                                                           fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(ins.rhs,
                                                           fn_def.metadata),
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_lea;

      Amd64Instruction ins_mov = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .origin = ins.origin,
          .lhs = amd64_convert_memory_location_to_amd64_operand(
              ins.meta_idx, fn_def.metadata),
          .rhs = ins_lea.lhs,
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_mov;

    } break;

    case IR_INSTRUCTION_KIND_LABEL_DEFINITION: {
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.lhs.kind);

      Amd64Instruction ins_label_def = {
          .kind = AMD64_INSTRUCTION_KIND_LABEL_DEFINITION,
          .origin = ins.origin,
          .lhs =
              (Amd64Operand){
                  .kind = AMD64_OPERAND_KIND_LABEL,
                  .u.label = ins.lhs.u.label,
                  .size = ASM_OPERAND_SIZE_4,
              },
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_label_def;
    } break;

    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
      PG_ASSERT(IR_OPERAND_KIND_NONE != ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.rhs.kind);

      Amd64Instruction ins_cmp = {
          .kind = AMD64_INSTRUCTION_KIND_CMP,
          .origin = ins.origin,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(ins.lhs,
                                                           fn_def.metadata),
          .rhs =
              (Amd64Operand){
                  .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                  .u.immediate = 0,
                  .size = ASM_OPERAND_SIZE_1,
              },
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_cmp;

      Amd64Instruction ins_je = {
          .kind = AMD64_INSTRUCTION_KIND_JMP_IF_NOT_EQ,
          .origin = ins.origin,
          .lhs =
              (Amd64Operand){
                  .kind = AMD64_OPERAND_KIND_LABEL,
                  .u.label = ins.rhs.u.label,
                  .size = ASM_OPERAND_SIZE_4,
              },
      };
      *PG_DYN_PUSH(&section->u.amd64_instructions, allocator) = ins_je;
    } break;

    case IR_INSTRUCTION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }
}

[[nodiscard]]
static Register
amd64_map_constraint_to_register(VirtualRegisterConstraint constraint) {
  switch (constraint) {
  case VREG_CONSTRAINT_NONE:
    return (Register){0};
  case VREG_CONSTRAINT_CONDITION_FLAGS:
    return (Register){AMD64_RFLAGS};
  case VREG_CONSTRAINT_SYSCALL_NUM:
  case VREG_CONSTRAINT_SYSCALL_RET:
    return (Register){AMD64_RAX};
  case VREG_CONSTRAINT_SYSCALL0:
  case VREG_CONSTRAINT_SYSCALL1:
  case VREG_CONSTRAINT_SYSCALL2:
  case VREG_CONSTRAINT_SYSCALL3:
  case VREG_CONSTRAINT_SYSCALL4:
  case VREG_CONSTRAINT_SYSCALL5:
    return PG_SLICE_AT(amd64_arch.syscall_calling_convention,
                       constraint - VREG_CONSTRAINT_SYSCALL0);
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]]
static AsmCodeSection amd64_emit_fn_definition(FnDefinition fn_def,
                                               bool verbose,
                                               PgAllocator *allocator) {
  (void)verbose;

  AsmCodeSection section = {
      .name = fn_def.name,
      .flags = fn_def.flags,
  };
  amd64_emit_prolog(&section, allocator);

  if (fn_def.stack_base_pointer_offset_max > 0) {
    Amd64Instruction stack_sub = {
        .kind = AMD64_INSTRUCTION_KIND_SUB,
        .lhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .u.reg = {AMD64_RSP},
                .size = ASM_OPERAND_SIZE_8,
            },
        .rhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                .u.immediate = 0, // Backpatched.
                .size = ASM_OPERAND_SIZE_8,
            },
    };
    *PG_DYN_PUSH(&section.u.amd64_instructions, allocator) = stack_sub;
  }
  u64 stack_sub_instruction_idx_maybe = section.u.amd64_instructions.len - 1;

  amd64_emit_fn_body(&section, fn_def, allocator);

  if (fn_def.stack_base_pointer_offset > 0) {
    u32 rsp_max_offset_aligned_16 =
        (u32)PG_ROUNDUP(fn_def.stack_base_pointer_offset, 16);

    PG_SLICE_AT_PTR(&section.u.amd64_instructions,
                    stack_sub_instruction_idx_maybe)
        ->rhs.u.immediate = rsp_max_offset_aligned_16;

    Amd64Instruction stack_add = {
        .kind = AMD64_INSTRUCTION_KIND_ADD,
        .lhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .u.reg = {AMD64_RSP},
                .size = ASM_OPERAND_SIZE_8,
            },
        .rhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                .u.immediate = rsp_max_offset_aligned_16,
                .size = ASM_OPERAND_SIZE_8,
            },
    };

    *PG_DYN_PUSH(&section.u.amd64_instructions, allocator) = stack_add;
  }
  amd64_emit_epilog(&section, allocator);

  amd64_sanity_check_section(section);
  return section;
}
