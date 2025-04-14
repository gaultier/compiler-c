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
