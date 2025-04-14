#pragma once
#include "asm.h"

static const Register amd64_rax = {0};
static const Register amd64_rbx = {1};
static const Register amd64_rcx = {2};
static const Register amd64_rdx = {3};
static const Register amd64_rdi = {4};
static const Register amd64_rsi = {5};
static const Register amd64_r8 = {6};
static const Register amd64_r9 = {7};
static const Register amd64_r10 = {8};
static const Register amd64_r11 = {9};
static const Register amd64_r12 = {10};
static const Register amd64_r13 = {11};
static const Register amd64_r14 = {12};
static const Register amd64_r15 = {13};
static const Register amd64_rsp = {14};
static const Register amd64_rbp = {15};

static const PgString amd64_register_to_string[16] = {
    [0] = PG_S("rax"),  [1] = PG_S("rbx"),  [2] = PG_S("rcx"),
    [3] = PG_S("rdx"),  [4] = PG_S("rdi"),  [5] = PG_S("rsi"),
    [6] = PG_S("r8"),   [7] = PG_S("r9"),   [8] = PG_S("r10"),
    [9] = PG_S("r11"),  [10] = PG_S("r12"), [11] = PG_S("r13"),
    [12] = PG_S("r14"), [13] = PG_S("r15"), [14] = PG_S("rsp"),
    [15] = PG_S("rbp"),
};

static const PgStringSlice amd64_register_to_string_slice = {
    .data = (PgString *)amd64_register_to_string,
    .len = PG_STATIC_ARRAY_LEN(amd64_register_to_string),
};

static const u8 amd64_register_to_encoded_value[16] = {
    [0] = 0b0000,  [1] = 0b0011,  [2] = 0b0001,  [3] = 0b0010,
    [4] = 0b0111,  [5] = 0b0110,  [6] = 0b1000,  [7] = 0b1001,
    [8] = 0b1010,  [9] = 0b1011,  [10] = 0b1100, [11] = 0b1101,
    [12] = 0b1110, [13] = 0b1111, [14] = 0b0100, [15] = 0b0101,
};

static const Pgu8Slice amd64_register_to_encoded_value_slice = {
    .data = (u8 *)amd64_register_to_encoded_value,
    .len = PG_STATIC_ARRAY_LEN(amd64_register_to_encoded_value),
};

static const Register amd64_call_preserved[] = {
    amd64_rbx, amd64_rsp, amd64_rbp, amd64_r12, amd64_r13, amd64_r14, amd64_r15,
};

static const Register amd64_calling_convention[] = {
    amd64_rdi, amd64_rsi, amd64_rdx, amd64_rcx, amd64_r8, amd64_r9,
};

static const Architecture amd64_arch = {
    .return_value = amd64_rax,
    .call_preserved =
        {
            .data = (Register *)amd64_call_preserved,
            .len = PG_STATIC_ARRAY_LEN(amd64_call_preserved),
        },
    .calling_convention =
        {
            .data = (Register *)amd64_calling_convention,
            .len = PG_STATIC_ARRAY_LEN(amd64_calling_convention),
        },
    .stack_pointer = amd64_rsp,
    .base_pointer = amd64_rbp,
};

typedef enum {
  AMD64_OPERAND_KIND_NONE,
  AMD64_OPERAND_KIND_REGISTER,
  AMD64_OPERAND_KIND_IMMEDIATE,
  AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
} Amd64OperandKind;

// Effective address = `base + index * scale + displacement`.
typedef struct {
  Register base;
  Register index;
  u64 scale;
  u64 displacement;
} Amd64EffectiveAddress;

typedef struct {
  Amd64OperandKind kind;
  union {
    Register reg;
    u64 immediate;
    Amd64EffectiveAddress effective_address;
  };
} Amd64Operand;

typedef enum {
  AMD64_INSTRUCTION_KIND_NONE,
  AMD64_INSTRUCTION_KIND_MOV,
  AMD64_INSTRUCTION_KIND_ADD,
  AMD64_INSTRUCTION_KIND_LEA,
  AMD64_INSTRUCTION_KIND_RET,
  AMD64_INSTRUCTION_KIND_SYSCALL,
} Amd64InstructionKind;

typedef struct {
  Amd64InstructionKind kind;
  Amd64Operand dst, src;
} Amd64Instruction;
PG_SLICE(Amd64Instruction) Amd64InstructionSlice;

typedef enum {
  AMD64_SECTION_FLAG_NONE = 0,
  AMD64_SECTION_FLAG_GLOBAL = 1 << 0,
} Amd64SectionFlag;

typedef struct {
  PgString name;
  Amd64SectionFlag flags;
  Amd64InstructionSlice instructions;
} Amd64Section;
PG_SLICE(Amd64Section) Amd64SectionSlice;

typedef struct {
  Amd64SectionSlice text;
  // TODO: data, rodata, etc.

  PgString file_name;
} Amd64Program;

static void amd64_dump_register(Register reg, Pgu8Dyn *sb,
                                PgAllocator *allocator) {
  PgString s = PG_SLICE_AT(amd64_register_to_string_slice, reg.value);
  PG_DYN_APPEND_SLICE(sb, s, allocator);
}

static void amd64_dump_operand(Amd64Operand operand, Pgu8Dyn *sb,
                               PgAllocator *allocator) {
  switch (operand.kind) {
  case AMD64_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_OPERAND_KIND_REGISTER:
    amd64_dump_register(operand.reg, sb, allocator);
    break;
  case AMD64_OPERAND_KIND_IMMEDIATE:
    pg_string_builder_append_u64(sb, operand.immediate, allocator);
    break;
  case AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS:
    *PG_DYN_PUSH(sb, allocator) = '[';
    amd64_dump_register(operand.effective_address.base, sb, allocator);
    PG_DYN_APPEND_SLICE(sb, PG_S(" + "), allocator);
    amd64_dump_register(operand.effective_address.index, sb, allocator);
    PG_DYN_APPEND_SLICE(sb, PG_S(" * "), allocator);
    pg_string_builder_append_u64(sb, operand.effective_address.scale,
                                 allocator);
    PG_DYN_APPEND_SLICE(sb, PG_S(" + "), allocator);
    pg_string_builder_append_u64(sb, operand.effective_address.displacement,
                                 allocator);
    *PG_DYN_PUSH(sb, allocator) = ']';
    break;
  default:
    PG_ASSERT(0);
  }
}

[[maybe_unused]] [[nodiscard]]
static PgString amd64_dump_section(Amd64Section section,
                                   PgAllocator *allocator) {
  Pgu8Dyn sb = {0};
  PG_DYN_APPEND_SLICE(&sb, PG_S("BITS 64\n"), allocator);
  PG_DYN_APPEND_SLICE(&sb, PG_S("CPU X64\n"), allocator);

  if (AMD64_SECTION_FLAG_GLOBAL & section.flags) {
    PG_DYN_APPEND_SLICE(&sb, PG_S("global "), allocator);
    PG_DYN_APPEND_SLICE(&sb, section.name, allocator);
    PG_DYN_APPEND_SLICE(&sb, PG_S(":\n"), allocator);
  }

  PG_DYN_APPEND_SLICE(&sb, section.name, allocator);
  PG_DYN_APPEND_SLICE(&sb, PG_S(":\n"), allocator);

  for (u64 i = 0; i < section.instructions.len; i++) {
    Amd64Instruction instruction = PG_SLICE_AT(section.instructions, i);

    // TODO: Validate operands?
    switch (instruction.kind) {
    case AMD64_INSTRUCTION_KIND_NONE:
      PG_ASSERT(0);
    case AMD64_INSTRUCTION_KIND_MOV:
      PG_DYN_APPEND_SLICE(&sb, PG_S("mov "), allocator);
      break;
    case AMD64_INSTRUCTION_KIND_ADD:
      PG_DYN_APPEND_SLICE(&sb, PG_S("add "), allocator);
      break;
    case AMD64_INSTRUCTION_KIND_LEA:
      PG_DYN_APPEND_SLICE(&sb, PG_S("lea "), allocator);
      break;
    case AMD64_INSTRUCTION_KIND_RET:
      PG_DYN_APPEND_SLICE(&sb, PG_S("ret "), allocator);
      break;
    case AMD64_INSTRUCTION_KIND_SYSCALL:
      PG_DYN_APPEND_SLICE(&sb, PG_S("syscall "), allocator);
      break;
    default:
      PG_ASSERT(0);
      break;
    }

    if (AMD64_OPERAND_KIND_NONE != instruction.dst.kind) {
      amd64_dump_operand(instruction.dst, &sb, allocator);
    }

    if (AMD64_OPERAND_KIND_NONE != instruction.src.kind) {
      PG_ASSERT(AMD64_OPERAND_KIND_NONE != instruction.dst.kind);

      PG_DYN_APPEND_SLICE(&sb, PG_S(", "), allocator);
      amd64_dump_operand(instruction.src, &sb, allocator);
    }

    *PG_DYN_PUSH(&sb, allocator) = '\n';
  }

  return PG_DYN_SLICE(PgString, sb);
}

[[nodiscard]]
static u8 amd64_encode_register_value(Register reg) {
  return PG_SLICE_AT(amd64_register_to_encoded_value_slice, reg.value);
}

static void amd64_encode_instruction_mov(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_MOV == instruction.kind);

  // MOV reg64, imm64 | B8 +rq iq | Move an 64-bit immediate value into a 64-bit
  // register.
  if (AMD64_OPERAND_KIND_REGISTER == instruction.dst.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.src.kind &&
      instruction.src.immediate <= UINT32_MAX) {
    u8 rex = 0b100'1000;
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0xb8;
    *PG_DYN_PUSH(sb, allocator) =
        opcode + amd64_encode_register_value(instruction.dst.reg);
    pg_byte_buffer_append_u32(sb, (u32)instruction.src.immediate, allocator);

    // TODO: Prefix to do 64 bits immediate.

    return;
  }

  // MOV reg64, reg/mem64 | 8B /r | Move the contents of a 64-bit register or
  // memory operand to a 64-bit destination register.
  if (AMD64_OPERAND_KIND_REGISTER == instruction.dst.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.src.kind) {
    u8 rex = 0b100'1000;
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x8b;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm = (0b11 << 6) |
               (u8)(amd64_encode_register_value(instruction.dst.reg) << 3) |
               (u8)(amd64_encode_register_value(instruction.src.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    return;
  }

  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_lea(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  (void)sb;
  (void)instruction;
  (void)allocator;
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

  if (AMD64_OPERAND_KIND_REGISTER == instruction.dst.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.src.kind) {
    u8 rex = 0b100'1000;
    *PG_DYN_PUSH(sb, allocator) = rex;
    u8 opcode = 0x03;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) |
               (u8)(amd64_encode_register_value(instruction.dst.reg) << 3) |
               (u8)(amd64_encode_register_value(instruction.src.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;
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

static void amd64_encode_instruction(Pgu8Dyn *sb, Amd64Instruction instruction,
                                     PgAllocator *allocator) {
  switch (instruction.kind) {
  case AMD64_INSTRUCTION_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_INSTRUCTION_KIND_MOV:
    amd64_encode_instruction_mov(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_ADD:
    amd64_encode_instruction_add(sb, instruction, allocator);
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

  default:
    PG_ASSERT(0);
  }
}

static void amd64_encode_section(Pgu8Dyn *sb, Amd64Section section,
                                 PgAllocator *allocator) {
  for (u64 i = 0; i < section.instructions.len; i++) {
    Amd64Instruction instruction = PG_SLICE_AT(section.instructions, i);
    amd64_encode_instruction(sb, instruction, allocator);
  }
}

[[nodiscard]]
static PgString amd64_encode_program_text(Amd64Program program,
                                          PgAllocator *allocator) {
  Pgu8Dyn sb = {0};

  for (u64 i = 0; i < program.text.len; i++) {
    Amd64Section section = PG_SLICE_AT(program.text, i);
    amd64_encode_section(&sb, section, allocator);
  }

  return PG_DYN_SLICE(PgString, sb);
}
