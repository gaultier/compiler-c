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

typedef enum {
  AMD64_MODRM_ENCODING_RULE_NONE,
  AMD64_MODRM_ENCODING_RULE_SLASH_0,
  AMD64_MODRM_ENCODING_RULE_SLASH_1,
  AMD64_MODRM_ENCODING_RULE_SLASH_2,
  AMD64_MODRM_ENCODING_RULE_SLASH_3,
  AMD64_MODRM_ENCODING_RULE_SLASH_4,
  AMD64_MODRM_ENCODING_RULE_SLASH_5,
  AMD64_MODRM_ENCODING_RULE_SLASH_6,
  AMD64_MODRM_ENCODING_RULE_SLASH_7,
  AMD64_MODRM_ENCODING_RULE_SLASH_R,
} Amd64ModRmEncodingRule;

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

static const PgString amd64_register_to_string_table[][8 + 1] = {
    [AMD64_RAX] = {[1] = PG_S("al"),
                   [2] = PG_S("ax"),
                   [4] = PG_S("eax"),
                   [8] = PG_S("rax")},
    [AMD64_RBX] = {[1] = PG_S("bl"),
                   [2] = PG_S("bx"),
                   [4] = PG_S("ebx"),
                   [8] = PG_S("rbx")},
    [AMD64_RCX] = {[1] = PG_S("cl"),
                   [2] = PG_S("cx"),
                   [4] = PG_S("ecx"),
                   [8] = PG_S("rcx")},
    [AMD64_RDX] = {[1] = PG_S("dl"),
                   [2] = PG_S("dx"),
                   [4] = PG_S("edx"),
                   [8] = PG_S("rdx")},
    [AMD64_RDI] = {[1] = PG_S("dil"),
                   [2] = PG_S("di"),
                   [4] = PG_S("edi"),
                   [8] = PG_S("rdi")},
    [AMD64_RSI] = {[1] = PG_S("sil"),
                   [2] = PG_S("si"),
                   [4] = PG_S("esi"),
                   [8] = PG_S("rsi")},
    [AMD64_R8] = {[1] = PG_S("r8b"),
                  [2] = PG_S("r8w"),
                  [4] = PG_S("r8d"),
                  [8] = PG_S("r8")},
    [AMD64_R9] = {[1] = PG_S("r9b"),
                  [2] = PG_S("r9w"),
                  [4] = PG_S("r9d"),
                  [8] = PG_S("r9")},
    [AMD64_R10] = {[1] = PG_S("r10b"),
                   [2] = PG_S("r10w"),
                   [4] = PG_S("r10d"),
                   [8] = PG_S("r10")},
    [AMD64_R11] = {[1] = PG_S("r11b"),
                   [2] = PG_S("r11w"),
                   [4] = PG_S("r11d"),
                   [8] = PG_S("r11")},
    [AMD64_R12] = {[1] = PG_S("r12b"),
                   [2] = PG_S("r12w"),
                   [4] = PG_S("r12d"),
                   [8] = PG_S("r12")},
    [AMD64_R13] = {[1] = PG_S("r13b"),
                   [2] = PG_S("r13w"),
                   [4] = PG_S("r13d"),
                   [8] = PG_S("r13")},
    [AMD64_R14] = {[1] = PG_S("r14b"),
                   [2] = PG_S("r14w"),
                   [4] = PG_S("r14d"),
                   [8] = PG_S("r14")},
    [AMD64_R15] = {[1] = PG_S("r15b"),
                   [2] = PG_S("r15w"),
                   [4] = PG_S("r15d"),
                   [8] = PG_S("r15")},
    [AMD64_RSP] = {[1] = PG_S("spl"),
                   [2] = PG_S("sp"),
                   [4] = PG_S("esp"),
                   [8] = PG_S("rsp")},
    [AMD64_RBP] = {[1] = PG_S("bpl"),
                   [2] = PG_S("bp"),
                   [4] = PG_S("ebp"),
                   [8] = PG_S("rbp")},
    // FIXME
    [AMD64_RFLAGS] = {[1] = PG_S("rflags"),
                      [2] = PG_S("rflags"),
                      [4] = PG_S("rflags"),
                      [8] = PG_S("rflags")},
};

static const u8 amd64_register_to_encoded_value[16 + 1] = {
    [AMD64_RAX] = 0b0000, [AMD64_RCX] = 0b0001, [AMD64_RDX] = 0b0010,
    [AMD64_RBX] = 0b0011, [AMD64_RSP] = 0b0100, [AMD64_RBP] = 0b0101,
    [AMD64_RSI] = 0b0110, [AMD64_RDI] = 0b0111, [AMD64_R8] = 0b1000,
    [AMD64_R9] = 0b1001,  [AMD64_R10] = 0b1010, [AMD64_R11] = 0b1011,
    [AMD64_R12] = 0b1100, [AMD64_R13] = 0b1101, [AMD64_R14] = 0b1110,
    [AMD64_R15] = 0b1111,
};

static const PgString amd64_size_to_operand_size_string[] = {
    [ASM_OPERAND_SIZE_1] = PG_S("byte"),
    [ASM_OPERAND_SIZE_2] = PG_S("word"),
    [ASM_OPERAND_SIZE_4] = PG_S("dword"),
    [ASM_OPERAND_SIZE_8] = PG_S("qword"),
};

static const AsmOperandSize amd64_size_to_operand_size[] = {
    [1] = ASM_OPERAND_SIZE_1,
    [2] = ASM_OPERAND_SIZE_2,
    [4] = ASM_OPERAND_SIZE_4,
    [8] = ASM_OPERAND_SIZE_8,
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

[[nodiscard]] static PgString amd64_register_to_string(Register reg,
                                                       AsmOperandSize size) {
  return amd64_register_to_string_table[reg.value][size];
}

[[nodiscard]] static bool amd64_is_reg(Amd64Operand op) {
  return AMD64_OPERAND_KIND_REGISTER == op.kind;
}

[[nodiscard]] static bool amd64_is_mem(Amd64Operand op) {
  return AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == op.kind;
}

[[nodiscard]] static bool amd64_is_reg_or_mem(Amd64Operand op) {
  return amd64_is_reg(op) || amd64_is_mem(op);
}

[[nodiscard]] static bool amd64_is_imm(Amd64Operand op) {
  return AMD64_OPERAND_KIND_IMMEDIATE == op.kind;
}

[[nodiscard]] static bool amd64_is_reg8(Amd64Operand op) {
  return amd64_is_reg(op) && ASM_OPERAND_SIZE_1 == op.size;
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
  PG_DYN_PUSH(&section->u.amd64_instructions, ins_push, allocator) ;

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
  PG_DYN_PUSH(&section->u.amd64_instructions, ins_mov, allocator) ;
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
  PG_DYN_PUSH(&section->u.amd64_instructions, ins_pop, allocator) ;
}

static void amd64_print_operand(Amd64Operand op, bool with_op_size, PgWriter *w,
                                PgAllocator *allocator) {
  switch (op.kind) {
  case AMD64_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_OPERAND_KIND_REGISTER:
    (void)pg_writer_write_full(w, amd64_register_to_string(op.u.reg, op.size),
                               allocator);
    break;
  case AMD64_OPERAND_KIND_IMMEDIATE:
    (void)pg_writer_write_u64_as_string(w, op.u.immediate, allocator);
    break;
  case AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS: {
    if (with_op_size) {
      (void)pg_writer_write_full(w, amd64_size_to_operand_size_string[op.size],
                                 allocator);
      (void)pg_writer_write_full(w, PG_S(" ptr "), allocator);
    }
    (void)pg_writer_write_full(w, PG_S("["), allocator);
    (void)pg_writer_write_full(
        w,
        amd64_register_to_string(op.u.effective_address.base,
                                 ASM_OPERAND_SIZE_8),
        allocator);
    if (op.u.effective_address.index.value) {
      (void)pg_writer_write_full(w, PG_S(" + "), allocator);
      (void)pg_writer_write_full(
          w,
          amd64_register_to_string(op.u.effective_address.index,
                                   ASM_OPERAND_SIZE_8),
          allocator);
      (void)pg_writer_write_full(w, PG_S(" * "), allocator);
      (void)pg_writer_write_u64_as_string(w, op.u.effective_address.scale,
                                          allocator);
    }

    if (op.u.effective_address.displacement) {
      (void)pg_writer_write_full(
          w, op.u.effective_address.displacement >= 0 ? PG_S("+") : PG_S(""),
          allocator);
      (void)pg_writer_write_u64_as_string(
          w, (u64)op.u.effective_address.displacement, allocator);
    }

    (void)pg_writer_write_full(w, PG_S("]"), allocator);
  } break;
  case AMD64_OPERAND_KIND_LABEL:
    PG_ASSERT(op.u.label.value.data);
    PG_ASSERT(op.u.label.value.len);

    (void)pg_writer_write_full(w, op.u.label.value, allocator);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void amd64_print_instruction(Amd64Instruction ins, bool with_origin,
                                    PgWriter *w, PgAllocator *allocator) {
  if (with_origin) {
    origin_write(w, ins.origin, allocator);
    (void)pg_writer_write_full(w, PG_S(": "), allocator);
  }

  // TODO: Validate operands?
  switch (ins.kind) {
  case AMD64_INSTRUCTION_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_INSTRUCTION_KIND_UD2:
    (void)pg_writer_write_full(w, PG_S("ud2 "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_MOV:
    (void)pg_writer_write_full(w, PG_S("mov "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_ADD:
    (void)pg_writer_write_full(w, PG_S("add "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_SUB:
    (void)pg_writer_write_full(w, PG_S("sub "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_LEA:
    (void)pg_writer_write_full(w, PG_S("lea "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_RET:
    (void)pg_writer_write_full(w, PG_S("ret "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_SYSCALL:
    (void)pg_writer_write_full(w, PG_S("syscall "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_PUSH:
    (void)pg_writer_write_full(w, PG_S("push "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_POP:
    (void)pg_writer_write_full(w, PG_S("pop "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_LABEL_DEFINITION:
    // The operand carries the actual label.
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_EQ:
    PG_ASSERT(AMD64_OPERAND_KIND_LABEL == ins.lhs.kind);
    PG_ASSERT(AMD64_OPERAND_KIND_NONE == ins.rhs.kind);

    (void)pg_writer_write_full(w, PG_S("je "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_NOT_EQ:
    PG_ASSERT(AMD64_OPERAND_KIND_LABEL == ins.lhs.kind);
    PG_ASSERT(AMD64_OPERAND_KIND_NONE == ins.rhs.kind);

    (void)pg_writer_write_full(w, PG_S("jne "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_ZERO:
    PG_ASSERT(AMD64_OPERAND_KIND_LABEL == ins.lhs.kind);
    PG_ASSERT(AMD64_OPERAND_KIND_NONE == ins.rhs.kind);

    (void)pg_writer_write_full(w, PG_S("jz "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP:
    (void)pg_writer_write_full(w, PG_S("jmp "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_CMP:
    (void)pg_writer_write_full(w, PG_S("cmp "), allocator);
    break;
  case AMD64_INSTRUCTION_KIND_SET_IF_EQ:
    (void)pg_writer_write_full(w, PG_S("sete "), allocator);
    break;
  default:
    PG_ASSERT(0);
    break;
  }

  bool has_effective_address = (amd64_is_mem(ins.lhs) || amd64_is_mem(ins.rhs));
  if (AMD64_OPERAND_KIND_NONE != ins.lhs.kind) {
    amd64_print_operand(ins.lhs, has_effective_address, w, allocator);
  }

  if (AMD64_OPERAND_KIND_NONE != ins.rhs.kind) {
    PG_ASSERT(AMD64_OPERAND_KIND_NONE != ins.lhs.kind);

    (void)pg_writer_write_full(w, PG_S(", "), allocator);
    amd64_print_operand(ins.rhs, has_effective_address, w, allocator);
  }

  if (AMD64_INSTRUCTION_KIND_LABEL_DEFINITION == ins.kind) {
    (void)pg_writer_write_full(w, PG_S(":"), allocator);
  }
}

[[maybe_unused]] [[nodiscard]]
static PgString amd64_instruction_to_string_human_readable(
    Amd64Instruction ins, bool with_origin, PgAllocator *allocator) {
  u64 cap = with_origin ? 1024 : 128;
  PgWriter w = pg_writer_make_string_builder(cap, allocator);
  amd64_print_instruction(ins, false, &w, nullptr);

  return PG_DYN_SLICE(PgString, w.u.bytes);
}

static void amd64_print_instructions(Amd64InstructionDyn instructions,
                                     PgWriter *w, PgAllocator *allocator) {
  for (u64 i = 0; i < instructions.len; i++) {
    (void)pg_writer_write_full(w, PG_S("["), allocator);
    (void)pg_writer_write_u64_as_string(w, i, allocator);
    (void)pg_writer_write_full(w, PG_S("]"), allocator);

    Amd64Instruction ins = PG_SLICE_AT(instructions, i);

    amd64_print_instruction(ins, true, w, allocator);
    (void)pg_writer_write_full(w, PG_S("\n"), allocator);
  }
  (void)pg_writer_flush(w, allocator);
}

static void amd64_print_section(AsmCodeSection section, PgWriter *w,
                                PgAllocator *allocator) {
  if (AST_NODE_FLAG_GLOBAL & section.flags) {
    (void)pg_writer_write_full(w, PG_S("global "), allocator);
    (void)pg_writer_write_full(w, section.name, allocator);
    (void)pg_writer_write_full(w, PG_S(":\n"), allocator);
  }

  (void)pg_writer_write_full(w, section.name, allocator);
  (void)pg_writer_write_full(w, PG_S(":\n"), allocator);

  amd64_print_instructions(section.u.amd64_instructions, w, allocator);
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

[[nodiscard]]
static bool amd64_is_operand_register_64_bits_only(Amd64Operand op) {
  return (amd64_is_reg(op) && amd64_is_register_64_bits_only(op.u.reg)) ||
         (amd64_is_mem(op) &&
          // TODO: Check `op.u.effective_address.index`?
          amd64_is_register_64_bits_only(op.u.effective_address.base));
}

// REX: 0100WRXB
static const u8 AMD64_REX_DEFAULT = 0b0100'0000;
// Enable use of 64 operand size.
static const u8 AMD64_REX_MASK_W = 0b0000'1000;
// Enable use of 64 bits registers in the `modrm.reg` field.
static const u8 AMD64_REX_MASK_R = 0b0000'0100;
// Enable use of 64 bits registers in `sib.index` field.
static const u8 AMD64_REX_MASK_X = 0b0000'0010;
// Enable use of 64 bits registers in the `modrm.rm` field,
// `sib.base` field, or `opcode.reg` field.
static const u8 AMD64_REX_MASK_B = 0b0000'0001;

// No index register.
static const u8 AMD64_SIB_INDEX_NONE = 0b101'000;
// Base is not a register but a u32 displacement value.
static const u8 AMD64_SIB_BASE_DISP32 = 0b101;

static void amd64_encode_instruction_ud2(Pgu8Dyn *sb, PgAllocator *allocator) {
  u8 opcode1 = 0x0f;
  PG_DYN_PUSH(sb, opcode1, allocator) ;
  u8 opcode2 = 0x0b;
  PG_DYN_PUSH(sb, opcode2, allocator) ;
}

static void amd64_encode_16bits_prefix(Pgu8Dyn *sb, Amd64Operand op,
                                       PgAllocator *allocator) {
  if (ASM_OPERAND_SIZE_2 == op.size) {
    PG_DYN_PUSH(sb, 0x66, allocator) ;
  }
}

// > A REX prefix is necessary only if an instruction references
// > one of the extended registers or one of the byte registers SPL, BPL, SIL,
// DIL;
// > or uses a 64-bit operand.
[[nodiscard]] static bool amd64_is_rex_needed(Amd64Operand lhs,
                                              Amd64Operand rhs) {
  bool is_lhs_reg_spl_bpl_sil_dil =
      ASM_OPERAND_SIZE_1 == lhs.size && amd64_is_reg(lhs) &&
      (AMD64_RSP == lhs.u.reg.value || AMD64_RBP == lhs.u.reg.value ||
       AMD64_RSI == lhs.u.reg.value || AMD64_RDI == lhs.u.reg.value);

  bool is_rhs_reg_spl_bpl_sil_dil =
      ASM_OPERAND_SIZE_1 == rhs.size && amd64_is_reg(rhs) &&
      (AMD64_RSP == rhs.u.reg.value || AMD64_RBP == rhs.u.reg.value ||
       AMD64_RSI == rhs.u.reg.value || AMD64_RDI == rhs.u.reg.value);

  return ASM_OPERAND_SIZE_8 == lhs.size ||
         amd64_is_operand_register_64_bits_only(lhs) ||
         amd64_is_operand_register_64_bits_only(rhs) ||
         is_lhs_reg_spl_bpl_sil_dil || is_rhs_reg_spl_bpl_sil_dil;
}

static void amd64_encode_rex(Pgu8Dyn *sb, bool upper_registers_modrm_reg_field,
                             bool upper_register_modrm_rm_field, bool field_w,
                             Amd64Operand lhs, Amd64Operand rhs,
                             PgAllocator *allocator) {
  if (!amd64_is_rex_needed(lhs, rhs)) {
    return;
  }

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

  PG_DYN_PUSH(sb, rex, allocator);
}

[[nodiscard]]
static bool amd64_is_r_slash_m8(Amd64Operand op) {
  return amd64_is_reg8(op) ||
         (amd64_is_mem(op) && ASM_OPERAND_SIZE_1 == op.size);
}

[[nodiscard]]
static bool amd64_is_modrm_encoding_rip_relative(u8 modrm) {
  u8 mod = (u8)(modrm >> 6);
  u8 rm = modrm & 0b111;

  return (mod == AMD64_MODRM_MOD_00) && (rm == 0b101);
}

[[nodiscard]] static bool
amd64_does_immediate_fit_in_sign_extended_u8(u64 value) {
  return value == (u64)(u8)value;
}

[[nodiscard]] static bool
amd64_does_immediate_fit_in_sign_extended_u16(u64 value) {
  return value == (u64)(u16)value;
}

[[nodiscard]] static bool
amd64_does_immediate_fit_in_sign_extended_u32(u64 value) {
  return value == (u64)(u32)value;
}

// Avoid accidentally using RIP-relative addressing:
// > The ModR/M encoding for RIP-relative addressing does not depend on
// > using a prefix. Specifically, the r/m bit field encoding of 101B (used
// > to select RIP-relative addressing) is not affected by the REX prefix.
// > For example, selecting
// > R13 (REX.B = 1, r/m = 101B) with mod = 00B still results in
// > RIP-relative addressing. The 4-bit r/m field of REX.B combined with
// > ModR/M is not fully decoded. In order to address R13 with no
// > displacement, software must encode R13 + 0 using a 1-byte displacement
// > of zero.
[[nodiscard]] static bool
amd64_can_base_reg_in_address_be_mistaken_for_rip_rel_addressing(
    Amd64EffectiveAddress addr) {
  return AMD64_R13 == addr.base.value || AMD64_RBP == addr.base.value;
}

// Format: `mod (2 bits) | reg (3 bits) | rm (3bits)`.
static Pgu8Option amd64_encode_modrm(Pgu8Dyn *sb, Amd64ModRmEncodingRule rule,
                                     Amd64Operand op_rm, Amd64Operand op_reg,
                                     PgAllocator *allocator) {

  Pgu8Option res = {0};

  u8 reg = 0;
  switch (rule) {
  case AMD64_MODRM_ENCODING_RULE_NONE:
    return res;

  case AMD64_MODRM_ENCODING_RULE_SLASH_0:
    reg = 0;
    break;
  case AMD64_MODRM_ENCODING_RULE_SLASH_1:
    reg = 1;
    break;
  case AMD64_MODRM_ENCODING_RULE_SLASH_2:
    reg = 2;
    break;
  case AMD64_MODRM_ENCODING_RULE_SLASH_3:
    reg = 3;
    break;
  case AMD64_MODRM_ENCODING_RULE_SLASH_4:
    reg = 4;
    break;
  case AMD64_MODRM_ENCODING_RULE_SLASH_5:
    reg = 5;
    break;
  case AMD64_MODRM_ENCODING_RULE_SLASH_6:
    reg = 6;
    break;
  case AMD64_MODRM_ENCODING_RULE_SLASH_7:
    reg = 7;
    break;
  case AMD64_MODRM_ENCODING_RULE_SLASH_R:
    reg = amd64_encode_register_value_3bits(op_reg.u.reg);
    break;
  default:
    PG_ASSERT(0);
  }

  u8 mod = 0, rm = 0;
  if (amd64_is_reg(op_rm)) {
    mod = AMD64_MODRM_MOD_11;
    rm = amd64_encode_register_value_3bits(op_rm.u.reg);
  } else if (amd64_is_imm(op_rm)) { // disp32
    mod = AMD64_MODRM_MOD_00;
    rm = 0b101;
  } else if (amd64_is_mem(op_rm) &&
             0 == op_rm.u.effective_address.displacement) {
    // Encode `[reg]` as `[reg+0]` to avoid accidental RIP relative addressing.
    if (amd64_can_base_reg_in_address_be_mistaken_for_rip_rel_addressing(
            op_rm.u.effective_address)) {
      mod = AMD64_MODRM_MOD_01;
      rm = amd64_encode_register_value_3bits(op_rm.u.effective_address.base);
    } else {
      mod = AMD64_MODRM_MOD_00;
      rm = amd64_encode_register_value_3bits(op_rm.u.effective_address.base);
    }
  } else if (amd64_is_mem(op_rm) &&
             op_rm.u.effective_address.displacement <= UINT8_MAX) {
    mod = AMD64_MODRM_MOD_01;
    rm = amd64_encode_register_value_3bits(op_rm.u.effective_address.base);
  } else if (amd64_is_mem(op_rm)) {
    mod = AMD64_MODRM_MOD_10;
    rm = amd64_encode_register_value_3bits(op_rm.u.effective_address.base);
  } else {
    PG_ASSERT(0);
  }

  // Encode.
  {
    PG_ASSERT(reg <= 0b111);
    PG_ASSERT(rm <= 0b111);

    u8 modrm = (u8)(mod << 6) | (u8)(reg << 3) | rm;

    // We do not support RIP addressing for now. Ensure we do not accidentally
    // fall into it.
    // NOTE: Maybe only one of the two checks is needed.
    if (amd64_is_mem(op_rm) || amd64_is_mem(op_reg)) {
      PG_ASSERT(!amd64_is_modrm_encoding_rip_relative(modrm));
    }

    PG_DYN_PUSH(sb, modrm, allocator);
    res.value = modrm;
    res.has_value = true;
    return res;
  }
}

[[nodiscard]] static bool amd64_is_sib_required(u8 modrm) {
  u8 mod = (u8)(modrm >> 6);
  u8 rm = modrm & 0b111;

  return (mod == AMD64_MODRM_MOD_00 || mod == AMD64_MODRM_MOD_01 ||
          mod == AMD64_MODRM_MOD_10) &&
         (rm == 0b100);
}

// Encoding: `Scale(2 bits) | Index(3 bits) | Base (3bits)`.
static void amd64_encode_sib(Pgu8Dyn *sb, Amd64EffectiveAddress addr, u8 modrm,
                             PgAllocator *allocator) {
  PG_ASSERT(0 != addr.base.value);

  PG_ASSERT(0 == addr.scale || 1 == addr.scale || 2 == addr.scale ||
            4 == addr.scale || 8 == addr.scale);

  PG_ASSERT(0 == addr.scale && "todo");
  PG_ASSERT(0 == addr.index.value && "todo");

  if (!amd64_is_sib_required(modrm)) {
    goto encode_displacement;
  }

  // Scale.
  u8 scale_encoded = 0;
  {
    u8 scale_encoding[] = {
        [0] = 0b0, [1] = 0b0, [2] = 0b01, [4] = 0b10, [8] = 0b11,
    };
    scale_encoded = PG_C_ARRAY_AT(
        scale_encoding, PG_STATIC_ARRAY_LEN(scale_encoding), addr.scale);
  }

  u8 index_encoded = 0;
  // Index.
  {
    // TODO: Same as the plain 3 bits register encoding?
    // NOTE: R12 is the same as RSP is the same as 'none'.
    u8 index_encoding[] = {
        [0] = 0b100,         [AMD64_RAX] = 0b000, [AMD64_RCX] = 0b001,
        [AMD64_RDX] = 0b010, [AMD64_RBX] = 0b011, [AMD64_RBP] = 0b101,
        [AMD64_RSI] = 0b110, [AMD64_RDI] = 0b111, [AMD64_R8] = 0b010,
        [AMD64_R9] = 0b001,  [AMD64_R10] = 0b010, [AMD64_R11] = 0b011,
        [AMD64_R12] = 0b100, [AMD64_R13] = 0b101, [AMD64_R14] = 0b0110,
        [AMD64_R15] = 0b111,

    };
    index_encoded = PG_C_ARRAY_AT(
        index_encoding, PG_STATIC_ARRAY_LEN(index_encoding), addr.index.value);
  }

  // Base.
  u8 base_encoded = 0;
  {

    // > SIB byte required for ESP-based addressing.
    // > SIB byte also required for R12-based addressing.
    if (AMD64_R12 == addr.base.value || AMD64_RSP == addr.base.value) {
      base_encoded = amd64_encode_register_value_3bits(addr.base);
    }
  }

  u8 res = (u8)(scale_encoded << 6) | (u8)((index_encoded & 0b111) << 3) |
           (u8)(base_encoded & 0b111);

  PG_DYN_PUSH(sb, res, allocator);

encode_displacement:
  // Displacement bytes.
  if (addr.displacement ||
      amd64_can_base_reg_in_address_be_mistaken_for_rip_rel_addressing(addr)) {
    if (addr.displacement <= INT8_MAX) {
      pg_byte_buffer_append_u8(sb, (u8)addr.displacement, allocator);
    } else {
      pg_byte_buffer_append_u32(sb, (u32)addr.displacement, allocator);
    }
  }
}

static void amd64_encode_instruction_mov(Pgu8Dyn *sb, Amd64Instruction ins,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_MOV == ins.kind);

  // MOV reg/mem8, r8
  // MOV reg/mem16, r16
  // MOV reg/mem32, r32
  // MOV reg/mem64, r64
  if (amd64_is_reg_or_mem(ins.lhs) && amd64_is_reg(ins.rhs)) {
    PG_ASSERT(ins.lhs.size == ins.rhs.size); // TODO: Check.
    PG_ASSERT(0 != ins.lhs.size);

    Register rhs = ins.rhs.u.reg;

    // Rex.
    {
      bool modrm_reg_field = amd64_is_register_64_bits_only(rhs);
      bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
      bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
      amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                       ins.rhs, allocator);
    }

    // Opcode.
    {
      u8 opcode = 0x89;
      if (amd64_is_r_slash_m8(ins.lhs)) {
        opcode = 0x88;
      }
      PG_DYN_PUSH(sb, opcode, allocator);
    }

    // ModRM.
    u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R,
                                  ins.lhs, ins.rhs, allocator)
                   .value;

    // SIB.
    {
      if (amd64_is_mem(ins.lhs)) {
        amd64_encode_sib(sb, ins.lhs.u.effective_address, modrm, allocator);
      }
    }
    return;
  }

  bool is_lhs_64_bits_reg_and_rhs_imm32_sign_extendable =
      AMD64_OPERAND_KIND_REGISTER == ins.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == ins.rhs.kind &&
      ASM_OPERAND_SIZE_8 == ins.lhs.size &&
      ((u64)(i32)ins.rhs.u.immediate == ins.rhs.u.immediate);
  // MOV r8, imm8
  // MOV r16, imm16
  // MOV r32, imm32
  // MOV r64, imm64
  if (AMD64_OPERAND_KIND_REGISTER == ins.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == ins.rhs.kind &&
      !is_lhs_64_bits_reg_and_rhs_imm32_sign_extendable) {
    PG_ASSERT(ins.lhs.size == ins.rhs.size);
    PG_ASSERT(0 != ins.lhs.size);
    Register reg = ins.lhs.u.reg;
    u64 immediate = ins.rhs.u.immediate;

    // Rex.
    {
      bool modrm_reg_field = false;
      bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
      bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
      amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                       ins.rhs, allocator);
    }

    // Opcode.
    {
      u8 opcode = 0xB8;
      if (amd64_is_r_slash_m8(ins.lhs)) {
        opcode = 0xB0;
      }
      opcode |= amd64_encode_register_value(reg) & 0b111;
      PG_DYN_PUSH(sb, opcode, allocator);
    }

    // No ModRM.

    switch (ins.lhs.size) {
    case ASM_OPERAND_SIZE_1:
      pg_byte_buffer_append_u8(sb, (u8)immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_2:
      pg_byte_buffer_append_u16(sb, (u16)immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_4:
      pg_byte_buffer_append_u32(sb, (u32)immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_8:
      pg_byte_buffer_append_u64(sb, immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_0:
    default:
      PG_ASSERT(0);
    }

    return;
  }

  // MOV reg/mem8, imm8
  // MOV reg/mem16, imm16
  // MOV reg/mem32, imm32
  // MOV reg/mem64, imm32 (sign extended)
  if (amd64_is_reg_or_mem(ins.lhs) &&
      AMD64_OPERAND_KIND_IMMEDIATE == ins.rhs.kind &&
      is_lhs_64_bits_reg_and_rhs_imm32_sign_extendable) {
    PG_ASSERT(ins.lhs.size == ins.rhs.size);
    PG_ASSERT(0 != ins.lhs.size);
    u64 immediate = ins.rhs.u.immediate;

    // Rex.
    {
      bool modrm_reg_field = false;
      bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
      bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
      amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                       ins.rhs, allocator);
    }

    // Opcode.
    {
      u8 opcode = 0xC7;
      if (amd64_is_r_slash_m8(ins.lhs)) {
        opcode = 0xC6;
      }
      PG_DYN_PUSH(sb, opcode, allocator);
    }

    // ModRM.
    {
      amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_0, ins.lhs,
                         ins.rhs, allocator);
    }

    switch (ins.lhs.size) {
    case ASM_OPERAND_SIZE_1:
      pg_byte_buffer_append_u8(sb, (u8)immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_2:
      pg_byte_buffer_append_u16(sb, (u16)immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_4:
      pg_byte_buffer_append_u32(sb, (u32)immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_8:
      pg_byte_buffer_append_u32(sb, (u32)immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_0:
    default:
      PG_ASSERT(0);
    }

    return;
  }

  // MOV reg8, reg/mem8
  // MOV reg16, reg/mem16
  // MOV reg32, reg/mem32
  // MOV reg64, reg/mem64
  if (amd64_is_reg(ins.lhs) && amd64_is_reg_or_mem(ins.rhs)) {
    PG_ASSERT(ins.lhs.size == ins.rhs.size);
    PG_ASSERT(0 != ins.lhs.size);
    Register lhs = ins.lhs.u.reg;

    // Rex.
    {
      bool modrm_reg_field = amd64_is_register_64_bits_only(lhs);
      bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.rhs);
      bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
      amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                       ins.rhs, allocator);
    }

    // Opcode.
    {
      u8 opcode = 0x8B;
      if (amd64_is_r_slash_m8(ins.lhs)) {
        opcode = 0x8A;
      }
      PG_DYN_PUSH(sb, opcode, allocator);
    }

    // ModRM.
    u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R,
                                  ins.rhs, ins.lhs, allocator)
                   .value;

    // SIB.
    {
      if (amd64_is_mem(ins.rhs)) {
        amd64_encode_sib(sb, ins.rhs.u.effective_address, modrm, allocator);
      }
    }

    return;
  }

  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_lea(Pgu8Dyn *sb, Amd64Instruction ins,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_LEA == ins.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == ins.lhs.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.rhs.kind);
  PG_ASSERT(0 == ins.rhs.u.effective_address.index.value && "todo");
  PG_ASSERT(0 == ins.rhs.u.effective_address.scale && "todo");
  PG_ASSERT(ins.lhs.size > ASM_OPERAND_SIZE_1);

  Amd64EffectiveAddress effective_address = ins.rhs.u.effective_address;

  // Rex.
  {
    bool modrm_reg_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.rhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);
  }

  // Opcode.
  {
    u8 opcode = 0x8D;
    PG_DYN_PUSH(sb, opcode, allocator);
  }

  // ModRM.
  u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R, ins.rhs,
                                ins.lhs, allocator)
                 .value;

  // SIB.
  {
    amd64_encode_sib(sb, effective_address, modrm, allocator);
  }

  return;
}

static void amd64_encode_instruction_ret(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  (void)sb;
  (void)instruction;
  (void)allocator;
  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_add(Pgu8Dyn *sb, Amd64Instruction ins,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_ADD == ins.kind);

  // add reg/mem16, imm8
  // add reg/mem32, imm8
  // add reg/mem64, imm8
  if (amd64_is_reg_or_mem(ins.lhs) && ins.lhs.size > ASM_OPERAND_SIZE_1 &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u8(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x83;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_0, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // add al, imm8
  if (amd64_is_reg8(ins.lhs) && AMD64_RAX == ins.lhs.u.reg.value &&
      amd64_is_imm(ins.rhs)) {
    PG_ASSERT(ASM_OPERAND_SIZE_1 == ins.lhs.size);
    PG_ASSERT(ASM_OPERAND_SIZE_1 == ins.rhs.size);

    u8 opcode = 0x04;
    PG_DYN_PUSH(sb, opcode, allocator);

    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // add ax, imm16
  // add eax, imm32
  // add rax, imm32
  if (amd64_is_reg(ins.lhs) && AMD64_RAX == ins.lhs.u.reg.value &&
      amd64_is_imm(ins.rhs)) {
    PG_ASSERT(ins.lhs.size == ins.rhs.size);

    if (ASM_OPERAND_SIZE_8 == ins.lhs.size) {
      bool modrm_reg_field = false;
      bool modrm_rm_field = false;
      bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
      amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                       ins.rhs, allocator);
    }

    u8 opcode = 0x05;
    PG_DYN_PUSH(sb, opcode, allocator);

    switch (ins.lhs.size) {
    case ASM_OPERAND_SIZE_2:
      pg_byte_buffer_append_u16(sb, (u16)ins.rhs.u.immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_4:
    case ASM_OPERAND_SIZE_8:
      pg_byte_buffer_append_u32(sb, (u32)ins.rhs.u.immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_0:
    case ASM_OPERAND_SIZE_1:
    default:
      PG_ASSERT(0);
    }

    return;
  }

  // add reg/mem8, reg8
  // add reg/mem16, reg16
  // add reg/mem32, reg32
  // add reg/mem64, reg64
  if (amd64_is_reg_or_mem(ins.lhs) && amd64_is_reg(ins.rhs)) {

    bool modrm_reg_field = amd64_is_operand_register_64_bits_only(ins.rhs);
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x01;
    if (amd64_is_reg8(ins.rhs)) {
      opcode = 0x00;
    }
    PG_DYN_PUSH(sb, opcode, allocator);

    u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R,
                                  ins.lhs, ins.rhs, allocator)
                   .value;

    if (amd64_is_mem(ins.lhs)) {
      amd64_encode_sib(sb, ins.lhs.u.effective_address, modrm, allocator);
    }

    return;
  }

  // add reg8, reg/mem8
  // add reg16, reg/mem16
  // add reg32, reg/mem32
  // add reg64, reg/mem64
  if (amd64_is_reg(ins.lhs) && amd64_is_reg_or_mem(ins.rhs)) {

    bool modrm_reg_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.rhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x03;
    if (amd64_is_reg8(ins.lhs)) {
      opcode = 0x02;
    }
    PG_DYN_PUSH(sb, opcode, allocator);

    u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R,
                                  ins.rhs, ins.lhs, allocator)
                   .value;

    if (amd64_is_mem(ins.rhs)) {
      amd64_encode_sib(sb, ins.rhs.u.effective_address, modrm, allocator);
    }

    return;
  }

  // add reg/mem8, imm8
  if (amd64_is_reg_or_mem(ins.lhs) && ins.lhs.size == ASM_OPERAND_SIZE_1 &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u8(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x80;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_0, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // add reg/mem16, imm16
  if (amd64_is_reg_or_mem(ins.lhs) && ASM_OPERAND_SIZE_2 == ins.lhs.size &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u16(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x81;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_0, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u16(sb, (u16)ins.rhs.u.immediate, allocator);

    return;
  }

  // add reg/mem32, imm32
  // add reg/mem64, imm64
  if (amd64_is_reg_or_mem(ins.lhs) && amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u32(ins.rhs.u.immediate)) {
    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x81;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_0, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u32(sb, (u32)ins.rhs.u.immediate, allocator);

    return;
  }

  PG_ASSERT(0);
}

static void amd64_encode_instruction_sub(Pgu8Dyn *sb, Amd64Instruction ins,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_SUB == ins.kind);

  // sub reg/mem16, imm8
  // sub reg/mem32, imm8
  // sub reg/mem64, imm8
  if (amd64_is_reg_or_mem(ins.lhs) && ins.lhs.size > ASM_OPERAND_SIZE_1 &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u8(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x83;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_5, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // sub al, imm8
  if (amd64_is_reg8(ins.lhs) && AMD64_RAX == ins.lhs.u.reg.value &&
      amd64_is_imm(ins.rhs)) {
    PG_ASSERT(ASM_OPERAND_SIZE_1 == ins.lhs.size);
    PG_ASSERT(ASM_OPERAND_SIZE_1 == ins.rhs.size);

    u8 opcode = 0x2C;
    PG_DYN_PUSH(sb, opcode, allocator);

    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // sub ax, imm16
  // sub eax, imm32
  // sub rax, imm32
  if (amd64_is_reg(ins.lhs) && AMD64_RAX == ins.lhs.u.reg.value &&
      amd64_is_imm(ins.rhs)) {
    PG_ASSERT(ins.lhs.size == ins.rhs.size);

    if (ASM_OPERAND_SIZE_8 == ins.lhs.size) {
      bool modrm_reg_field = false;
      bool modrm_rm_field = false;
      bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
      amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                       ins.rhs, allocator);
    }

    u8 opcode = 0x2D;
    PG_DYN_PUSH(sb, opcode, allocator);

    switch (ins.lhs.size) {
    case ASM_OPERAND_SIZE_2:
      pg_byte_buffer_append_u16(sb, (u16)ins.rhs.u.immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_4:
    case ASM_OPERAND_SIZE_8:
      pg_byte_buffer_append_u32(sb, (u32)ins.rhs.u.immediate, allocator);
      break;
    case ASM_OPERAND_SIZE_0:
    case ASM_OPERAND_SIZE_1:
    default:
      PG_ASSERT(0);
    }

    return;
  }

  // sub reg/mem8, reg8
  // sub reg/mem16, reg16
  // sub reg/mem32, reg32
  // sub reg/mem64, reg64
  if (amd64_is_reg_or_mem(ins.lhs) && amd64_is_reg(ins.rhs)) {

    bool modrm_reg_field = amd64_is_operand_register_64_bits_only(ins.rhs);
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x29;
    if (amd64_is_reg8(ins.rhs)) {
      opcode = 0x28;
    }
    PG_DYN_PUSH(sb, opcode, allocator);

    u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R,
                                  ins.lhs, ins.rhs, allocator)
                   .value;

    if (amd64_is_mem(ins.lhs)) {
      amd64_encode_sib(sb, ins.lhs.u.effective_address, modrm, allocator);
    }

    return;
  }

  // sub reg8, reg/mem8
  // sub reg16, reg/mem16
  // sub reg32, reg/mem32
  // sub reg64, reg/mem64
  if (amd64_is_reg(ins.lhs) && amd64_is_reg_or_mem(ins.rhs)) {

    bool modrm_reg_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.rhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x2B;
    if (amd64_is_reg8(ins.lhs)) {
      opcode = 0x2A;
    }
    PG_DYN_PUSH(sb, opcode, allocator);

    u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R,
                                  ins.rhs, ins.lhs, allocator)
                   .value;

    if (amd64_is_mem(ins.rhs)) {
      amd64_encode_sib(sb, ins.rhs.u.effective_address, modrm, allocator);
    }

    return;
  }

  // sub reg/mem8, imm8
  if (amd64_is_reg_or_mem(ins.lhs) && ins.lhs.size == ASM_OPERAND_SIZE_1 &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u8(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x80;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_5, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // sub reg/mem16, imm16
  if (amd64_is_reg_or_mem(ins.lhs) && ASM_OPERAND_SIZE_2 == ins.lhs.size &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u16(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x81;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_5, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u16(sb, (u16)ins.rhs.u.immediate, allocator);

    return;
  }

  // sub reg/mem32, imm32
  // sub reg/mem64, imm64
  if (amd64_is_reg_or_mem(ins.lhs) && amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u32(ins.rhs.u.immediate)) {
    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x81;
    PG_DYN_PUSH(sb, opcode, allocator) ;

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_5, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u32(sb, (u32)ins.rhs.u.immediate, allocator);

    return;
  }

  PG_ASSERT(0);
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

  u8 opcode =
      0x50 + (amd64_encode_register_value(instruction.lhs.u.reg) & 0b111);
  PG_DYN_PUSH(sb, opcode, allocator);
}

static void amd64_encode_instruction_pop(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_POP == instruction.kind);

  PG_ASSERT(AMD64_RBP == instruction.lhs.u.reg.value && "todo");

  u8 opcode =
      0x58 + (amd64_encode_register_value(instruction.lhs.u.reg) & 0b111);

  PG_DYN_PUSH(sb, opcode, allocator);
}

static void amd64_encode_instruction_je(Pgu8Dyn *sb,
                                        Amd64Instruction instruction,
                                        AsmProgram *program,
                                        PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_JMP_IF_EQ == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_LABEL == instruction.lhs.kind);
  PG_ASSERT(instruction.lhs.u.label.value.len);

  u8 opcode1 = 0x0f;
  PG_DYN_PUSH(sb, opcode1, allocator);

  u8 opcode2 = 0x84;
  PG_DYN_PUSH(sb, opcode2, allocator);

  PG_DYN_PUSH(&program->jumps_to_backpatch,
              ((LabelAddress){
                  .label = instruction.lhs.u.label,
                  .code_address = sb->len,
              }),
              allocator);

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
  PG_DYN_PUSH(sb, opcode1, allocator);

  u8 opcode2 = 0x85;
  PG_DYN_PUSH(sb, opcode2, allocator);

  PG_DYN_PUSH(&program->jumps_to_backpatch,
              ((LabelAddress){
                  .label = instruction.lhs.u.label,
                  .code_address = sb->len,
              }),
              allocator);

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
  PG_DYN_PUSH(sb, opcode1, allocator);

  u8 opcode2 = 0x84;
  PG_DYN_PUSH(sb, opcode2, allocator);

  PG_DYN_PUSH(&program->jumps_to_backpatch,
              ((LabelAddress){
                  .label = instruction.lhs.u.label,
                  .code_address = sb->len,
              }),
              allocator);

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
  PG_DYN_PUSH(sb, opcode, allocator);

  PG_DYN_PUSH(&program->jumps_to_backpatch,
              ((LabelAddress){
                  .label = instruction.lhs.u.label,
                  .code_address = sb->len,
              }),
              allocator);

  // Backpatched with `program.label_addresses`.
  pg_byte_buffer_append_u32(sb, 0, allocator);
}

static void amd64_encode_instruction_cmp(Pgu8Dyn *sb, Amd64Instruction ins,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_CMP == ins.kind);

  // cmp reg/mem16, imm8
  // cmp reg/mem32, imm8
  // cmp reg/mem64, imm8
  if (amd64_is_reg_or_mem(ins.lhs) && ins.lhs.size > ASM_OPERAND_SIZE_1 &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u8(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x83;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_7, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // cmp al, imm8
  if (amd64_is_reg8(ins.lhs) && AMD64_RAX == ins.lhs.u.reg.value &&
      amd64_is_imm(ins.rhs)) {
    PG_ASSERT(ASM_OPERAND_SIZE_1 == ins.lhs.size);
    PG_ASSERT(ASM_OPERAND_SIZE_1 == ins.rhs.size);

    u8 opcode = 0x3C;
    pg_byte_buffer_append_u8(sb, opcode, allocator);
    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // cmp ax, imm16
  if (amd64_is_reg(ins.lhs) && AMD64_RAX == ins.lhs.u.reg.value &&
      ASM_OPERAND_SIZE_2 == ins.lhs.size && amd64_is_imm(ins.rhs)) {
    PG_ASSERT(ASM_OPERAND_SIZE_2 == ins.lhs.size);
    PG_ASSERT(ASM_OPERAND_SIZE_2 == ins.rhs.size);

    u8 opcode = 0x3D;
    pg_byte_buffer_append_u8(sb, opcode, allocator);
    pg_byte_buffer_append_u16(sb, (u16)ins.rhs.u.immediate, allocator);

    return;
  }

  // cmp eax, imm32
  if (amd64_is_reg(ins.lhs) && AMD64_RAX == ins.lhs.u.reg.value &&
      ASM_OPERAND_SIZE_4 == ins.lhs.size && amd64_is_imm(ins.rhs)) {
    PG_ASSERT(ASM_OPERAND_SIZE_4 == ins.lhs.size);
    PG_ASSERT(ASM_OPERAND_SIZE_4 == ins.rhs.size);

    u8 opcode = 0x3D;
    pg_byte_buffer_append_u8(sb, opcode, allocator);
    pg_byte_buffer_append_u32(sb, (u32)ins.rhs.u.immediate, allocator);

    return;
  }

  // cmp rax, imm32
  if (amd64_is_reg(ins.lhs) && AMD64_RAX == ins.lhs.u.reg.value &&
      ASM_OPERAND_SIZE_8 == ins.lhs.size && amd64_is_imm(ins.rhs)) {
    PG_ASSERT(ASM_OPERAND_SIZE_8 == ins.lhs.size);
    PG_ASSERT(ASM_OPERAND_SIZE_8 == ins.rhs.size);

    // Rex.
    {
      bool modrm_reg_field = false;
      bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
      bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
      amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                       ins.rhs, allocator);
    }

    u8 opcode = 0x3D;
    pg_byte_buffer_append_u8(sb, opcode, allocator);
    pg_byte_buffer_append_u32(sb, (u32)ins.rhs.u.immediate, allocator);

    return;
  }

  // cmp reg/mem8, reg8
  // cmp reg/mem16, reg16
  // cmp reg/mem32, reg32
  // cmp reg/mem64, reg64
  if (amd64_is_reg_or_mem(ins.lhs) && amd64_is_reg(ins.rhs)) {

    bool modrm_reg_field = amd64_is_operand_register_64_bits_only(ins.rhs);
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x39;
    if (amd64_is_reg8(ins.rhs)) {
      opcode = 0x38;
    }
    PG_DYN_PUSH(sb, opcode, allocator);

    u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R,
                                  ins.lhs, ins.rhs, allocator)
                   .value;

    if (amd64_is_mem(ins.lhs)) {
      amd64_encode_sib(sb, ins.lhs.u.effective_address, modrm, allocator);
    }

    return;
  }

  // cmp reg8, reg/mem8
  // cmp reg16, reg/mem16
  // cmp reg32, reg/mem32
  // cmp reg64, reg/mem64
  if (amd64_is_reg(ins.lhs) && amd64_is_reg_or_mem(ins.rhs)) {

    bool modrm_reg_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.rhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x3B;
    if (amd64_is_reg8(ins.lhs)) {
      opcode = 0x3A;
    }
    PG_DYN_PUSH(sb, opcode, allocator);

    u8 modrm = amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_R,
                                  ins.rhs, ins.lhs, allocator)
                   .value;

    if (amd64_is_mem(ins.rhs)) {
      amd64_encode_sib(sb, ins.rhs.u.effective_address, modrm, allocator);
    }

    return;
  }

  // cmp reg/mem8, imm8
  if (amd64_is_reg_or_mem(ins.lhs) && ins.lhs.size == ASM_OPERAND_SIZE_1 &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u8(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x80;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_7, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u8(sb, (u8)ins.rhs.u.immediate, allocator);

    return;
  }

  // cmp reg/mem16, imm16
  if (amd64_is_reg_or_mem(ins.lhs) && ASM_OPERAND_SIZE_2 == ins.lhs.size &&
      amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u16(ins.rhs.u.immediate)) {

    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x81;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_7, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u16(sb, (u16)ins.rhs.u.immediate, allocator);

    return;
  }

  // cmp reg/mem32, imm32
  // cmp reg/mem64, imm64
  if (amd64_is_reg_or_mem(ins.lhs) && amd64_is_imm(ins.rhs) &&
      amd64_does_immediate_fit_in_sign_extended_u32(ins.rhs.u.immediate)) {
    bool modrm_reg_field = false;
    bool modrm_rm_field = amd64_is_operand_register_64_bits_only(ins.lhs);
    bool field_w = ASM_OPERAND_SIZE_8 == ins.rhs.size;
    amd64_encode_rex(sb, modrm_reg_field, modrm_rm_field, field_w, ins.lhs,
                     ins.rhs, allocator);

    u8 opcode = 0x81;
    PG_DYN_PUSH(sb, opcode, allocator);

    amd64_encode_modrm(sb, AMD64_MODRM_ENCODING_RULE_SLASH_7, ins.lhs, ins.rhs,
                       allocator);

    pg_byte_buffer_append_u32(sb, (u32)ins.rhs.u.immediate, allocator);

    return;
  }

  PG_ASSERT(0);
}

static void amd64_encode_instruction_sete(Pgu8Dyn *sb,
                                          Amd64Instruction instruction,
                                          PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_SET_IF_EQ == instruction.kind);

  u8 opcode1 = 0x0F;
  u8 opcode2 = 0x94;
  PG_DYN_PUSH(sb, opcode1, allocator);
  PG_DYN_PUSH(sb, opcode2, allocator);

  PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind);
  Register reg = instruction.lhs.u.reg;

  u8 modrm = (0b11 << 6) |

             (u8)(amd64_encode_register_value(reg) & 0b111);
  PG_DYN_PUSH(sb, modrm, allocator) ;
}

static void amd64_encode_instruction(AsmProgram *program, Pgu8Dyn *sb,
                                     Amd64Instruction ins,
                                     PgAllocator *allocator) {
  amd64_encode_16bits_prefix(sb, ins.lhs, allocator);

  switch (ins.kind) {
  case AMD64_INSTRUCTION_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_INSTRUCTION_KIND_UD2:
    amd64_encode_instruction_ud2(sb, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_MOV:
    amd64_encode_instruction_mov(sb, ins, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_ADD:
    amd64_encode_instruction_add(sb, ins, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_SUB:
    amd64_encode_instruction_sub(sb, ins, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_LEA:
    amd64_encode_instruction_lea(sb, ins, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_RET:
    amd64_encode_instruction_ret(sb, ins, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_SYSCALL:
    amd64_encode_instruction_syscall(sb, ins, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_PUSH:
    amd64_encode_instruction_push(sb, ins, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_POP:
    amd64_encode_instruction_pop(sb, ins, allocator);
    break;

  case AMD64_INSTRUCTION_KIND_LABEL_DEFINITION:
    PG_ASSERT(ins.lhs.u.label.value.len);

    PG_DYN_PUSH(&program->label_addresses,( (LabelAddress){
        .label = ins.lhs.u.label,
        .code_address = sb->len,
    }),allocator);
    break;

  case AMD64_INSTRUCTION_KIND_JMP_IF_EQ:
    amd64_encode_instruction_je(sb, ins, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_NOT_EQ:
    amd64_encode_instruction_jne(sb, ins, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP_IF_ZERO:
    amd64_encode_instruction_jz(sb, ins, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP:
    amd64_encode_instruction_jmp(sb, ins, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_CMP:
    amd64_encode_instruction_cmp(sb, ins, allocator);
    break;

  case AMD64_INSTRUCTION_KIND_SET_IF_EQ:
    amd64_encode_instruction_sete(sb, ins, allocator);
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
amd64_convert_ir_operand_to_amd64_operand(IrOperand op, MetadataIndex meta_idx,
                                          MetadataDyn metadata) {
  if (IR_OPERAND_KIND_NUM == op.kind) {
    PG_ASSERT(meta_idx.value);
    Metadata meta = PG_SLICE_AT(metadata, meta_idx.value);
    PG_ASSERT(meta.type);
    PG_ASSERT(meta.type->size);

    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_IMMEDIATE,
        .u.immediate = op.u.u64,
        .size = PG_C_ARRAY_AT(amd64_size_to_operand_size,
                              PG_STATIC_ARRAY_LEN(amd64_size_to_operand_size),
                              meta.type->size),
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
          .lhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.lhs, ins.meta_idx, fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.rhs, ins.meta_idx, fn_def.metadata),
          .origin = ins.origin,
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_mov, allocator) ;

    } break;

    case IR_INSTRUCTION_KIND_COMPARISON: {
      PG_ASSERT(ins.lhs.kind);
      PG_ASSERT(ins.rhs.kind);
      PG_ASSERT(ins.meta_idx.value);

      Amd64Instruction ins_cmp = {
          .kind = AMD64_INSTRUCTION_KIND_CMP,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.lhs, ins.meta_idx, fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.rhs, ins.meta_idx, fn_def.metadata),
          .origin = ins.origin,
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_cmp, allocator) ;

      Amd64Instruction ins_sete = {
          .kind = AMD64_INSTRUCTION_KIND_SET_IF_EQ,
          .lhs = amd64_convert_memory_location_to_amd64_operand(
              ins.meta_idx, fn_def.metadata),
          .origin = ins.origin,
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_sete, allocator) ;
    } break;

    case IR_INSTRUCTION_KIND_ADD: {
      PG_ASSERT(ins.lhs.kind);
      PG_ASSERT(ins.rhs.kind);
      PG_ASSERT(ins.meta_idx.value);

      Amd64Instruction ins_mov = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs = amd64_convert_memory_location_to_amd64_operand(
              ins.meta_idx, fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.lhs, ins.meta_idx, fn_def.metadata),
          .origin = ins.origin,
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_mov, allocator) ;

      Amd64Instruction ins_add = {
          .kind = AMD64_INSTRUCTION_KIND_ADD,
          .lhs = amd64_convert_memory_location_to_amd64_operand(
              ins.meta_idx, fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.rhs, ins.meta_idx, fn_def.metadata),
          .origin = ins.origin,
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_add, allocator) ;
    } break;

    case IR_INSTRUCTION_KIND_TRAP: {
      Amd64Instruction ins_ud2 = {
          .kind = AMD64_INSTRUCTION_KIND_UD2,
          .origin = ins.origin,
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_ud2, allocator) ;
    } break;

    case IR_INSTRUCTION_KIND_JUMP: {
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.lhs.kind);

      Amd64Instruction ins_jmp = {
          .kind = AMD64_INSTRUCTION_KIND_JMP,
          .origin = ins.origin,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.lhs, ins.meta_idx, fn_def.metadata),
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_jmp, allocator) ;
    } break;

    case IR_INSTRUCTION_KIND_SYSCALL: {
      Amd64Instruction ins_sys = {
          .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
          .origin = ins.origin,
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_sys, allocator) ;
    } break;

    case IR_INSTRUCTION_KIND_LOAD_ADDRESS: {
      Amd64Instruction ins_lea = {
          .kind = AMD64_INSTRUCTION_KIND_LEA,
          .origin = ins.origin,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.lhs, ins.meta_idx, fn_def.metadata),
          .rhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.rhs, ins.meta_idx, fn_def.metadata),
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_lea, allocator) ;

      Amd64Instruction ins_mov = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .origin = ins.origin,
          .lhs = amd64_convert_memory_location_to_amd64_operand(
              ins.meta_idx, fn_def.metadata),
          .rhs = ins_lea.lhs,
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_mov, allocator) ;

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
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_label_def, allocator) ;
    } break;

    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
      PG_ASSERT(IR_OPERAND_KIND_NONE != ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.rhs.kind);

      Amd64Instruction ins_cmp = {
          .kind = AMD64_INSTRUCTION_KIND_CMP,
          .origin = ins.origin,
          .lhs = amd64_convert_ir_operand_to_amd64_operand(
              ins.lhs, ins.meta_idx, fn_def.metadata),
          .rhs =
              (Amd64Operand){
                  .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                  .u.immediate = 0,
                  .size = ASM_OPERAND_SIZE_1,
              },
      };
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_cmp, allocator) ;

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
      PG_DYN_PUSH(&section->u.amd64_instructions, ins_je, allocator) ;
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

[[maybe_unused]] // FIXME
static void
amd64_emit_runtime(PgAllocator *allocator) {
  (void)allocator;
  // TODO
}

[[nodiscard]]
static AsmCodeSection amd64_emit_fn_definition(FnDefinition fn_def,
                                               PgAllocator *allocator) {
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
    PG_DYN_PUSH(&section.u.amd64_instructions, stack_sub, allocator) ;
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

    PG_DYN_PUSH(&section.u.amd64_instructions, stack_add, allocator) ;
  }
  amd64_emit_epilog(&section, allocator);

  amd64_sanity_check_section(section);
  return section;
}
