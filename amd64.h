#pragma once
#include "asm.h"
#include "lir.h"

typedef enum {
  AMD64_OPERAND_KIND_NONE,
  AMD64_OPERAND_KIND_REGISTER,
  AMD64_OPERAND_KIND_IMMEDIATE,
  AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
  AMD64_OPERAND_KIND_LABEL,
} Amd64OperandKind;

typedef struct {
  Register base;
  Register index;
  u8 scale;
  i32 displacement;
} Amd64EffectiveAddress;

typedef struct {
  Amd64OperandKind kind;
  union {
    Register reg;
    u64 immediate;
    Amd64EffectiveAddress effective_address;
    LabelId label;
  };
} Amd64Operand;
PG_SLICE(Amd64Operand) Amd64OperandSlice;
PG_DYN(Amd64Operand) Amd64OperandDyn;

static const Register amd64_rax = {1};
static const Register amd64_rbx = {2};
static const Register amd64_rcx = {3};
static const Register amd64_rdx = {4};
static const Register amd64_rdi = {5};
static const Register amd64_rsi = {6};
static const Register amd64_r8 = {7};
static const Register amd64_r9 = {8};
static const Register amd64_r12 = {9};
static const Register amd64_r13 = {10};
static const Register amd64_r14 = {11};
static const Register amd64_r15 = {12};
static const Register amd64_r10 = {13};
static const Register amd64_r11 = {14};
static const Register amd64_rsp = {15};
static const Register amd64_rbp = {16};
static const Register amd64_rflags = {17};

static const Register amd64_register_allocator_gprs[] = {
    amd64_rax,
    amd64_rdi,
    amd64_rdx,
    amd64_rcx,
    amd64_r8,
    amd64_r9,
    /* Reserved for spilling: amd64_r10, amd64_r11, */
    amd64_rbx,
    amd64_r12,
    amd64_r13,
    amd64_r14,
    amd64_r15,
};

static const RegisterSlice amd64_register_allocator_gprs_slice = {
    .data = (Register *)amd64_register_allocator_gprs,
    .len = PG_STATIC_ARRAY_LEN(amd64_register_allocator_gprs),
};

static const PgString amd64_register_to_string[] = {
    [0] = PG_S("UNREACHABLE"), [1] = PG_S("rax"),  [2] = PG_S("rbx"),
    [3] = PG_S("rcx"),         [4] = PG_S("rdx"),  [5] = PG_S("rdi"),
    [6] = PG_S("rsi"),         [7] = PG_S("r8"),   [8] = PG_S("r9"),
    [9] = PG_S("r10"),         [10] = PG_S("r11"), [11] = PG_S("r12"),
    [12] = PG_S("r13"),        [13] = PG_S("r14"), [14] = PG_S("r15"),
    [15] = PG_S("rsp"),        [16] = PG_S("rbp"), [17] = PG_S("rflags"),
};

static const PgStringSlice amd64_register_to_string_slice = {
    .data = (PgString *)amd64_register_to_string,
    .len = PG_STATIC_ARRAY_LEN(amd64_register_to_string),
};

static const u8 amd64_register_to_encoded_value[16 + 1] = {
    [0] = 0,       // zero value
    [1] = 0b0000,  // rax
    [2] = 0b0011,  // rbx
    [3] = 0b0001,  // rcx
    [4] = 0b0010,  // rdx
    [5] = 0b0111,  // rdi
    [6] = 0b0110,  // rsi
    [7] = 0b1000,  // r8
    [8] = 0b1001,  // r9
    [9] = 0b1010,  // r10
    [10] = 0b1011, // r11
    [11] = 0b1100, // r12
    [12] = 0b1101, // r13
    [13] = 0b1110, // r14
    [14] = 0b1111, // r15
    [15] = 0b0100, // rsp
    [16] = 0b0101, // rbp
};

static const Pgu8Slice amd64_register_to_encoded_value_slice = {
    .data = (u8 *)amd64_register_to_encoded_value,
    .len = PG_STATIC_ARRAY_LEN(amd64_register_to_encoded_value),
};

// TODO: SystemV ABI vs Windows calling convention!
static const Register amd64_callee_saved[] = {
    amd64_rbx, amd64_rsp, amd64_rbp, amd64_r12, amd64_r13, amd64_r14, amd64_r15,
};

static const Register amd64_caller_saved[] = {
    amd64_rax, amd64_rdi, amd64_rdx, amd64_rcx,
    amd64_r8,  amd64_r9,  amd64_r10, amd64_r11,
};

static const Register amd64_spill_registers[] = {amd64_r10, amd64_r11};

static const Register amd64_calling_convention[] = {
    amd64_rdi, amd64_rsi, amd64_rdx, amd64_rcx, amd64_r8, amd64_r9,
};

static const Register amd64_syscall_calling_convention[6] = {
    amd64_rdi, amd64_rsi, amd64_rdx, amd64_r10, amd64_r8, amd64_r9,
};

static const Architecture amd64_arch = {
    .return_value = amd64_rax,
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
    .syscall_num = amd64_rax,
    .syscall_ret = amd64_rax,
    .stack_pointer = amd64_rsp,
    .base_pointer = amd64_rbp,
};

typedef enum {
  AMD64_INSTRUCTION_KIND_NONE,
  AMD64_INSTRUCTION_KIND_MOV,
  AMD64_INSTRUCTION_KIND_ADD,
  AMD64_INSTRUCTION_KIND_SUB,
  AMD64_INSTRUCTION_KIND_LEA,
  AMD64_INSTRUCTION_KIND_RET,
  AMD64_INSTRUCTION_KIND_SYSCALL,
  AMD64_INSTRUCTION_KIND_PUSH,
  AMD64_INSTRUCTION_KIND_POP,
  AMD64_INSTRUCTION_KIND_LABEL,
  AMD64_INSTRUCTION_KIND_CMP,
  AMD64_INSTRUCTION_KIND_JMP,
  AMD64_INSTRUCTION_KIND_JMP_IF_EQ,
  AMD64_INSTRUCTION_KIND_SET_IF_EQ,
} Amd64InstructionKind;

typedef struct {
  Amd64InstructionKind kind;
  Amd64Operand lhs, rhs;
  Origin origin;
  bool tombstone; // TODO: Consider if necessary.
} Amd64Instruction;
PG_SLICE(Amd64Instruction) Amd64InstructionSlice;
PG_DYN(Amd64Instruction) Amd64InstructionDyn;

typedef struct {
  ASM_EMITTER_FIELDS
} Amd64Emitter;

static void amd64_print_register(Register reg) {
  PgString s = PG_SLICE_AT(amd64_register_to_string_slice, reg.value);
  printf("%.*s", (i32)s.len, s.data);
}

static void amd64_add_instruction(PgAnyDyn *instructions_any,
                                  Amd64Instruction ins,
                                  PgAllocator *allocator) {
  Amd64InstructionDyn instructions = {
      .data = (Amd64Instruction *)instructions_any->data,
      .len = instructions_any->len,
      .cap = instructions_any->cap,
  };
  *PG_DYN_PUSH(&instructions, allocator) = ins;

  instructions_any->data = instructions.data;
  instructions_any->len = instructions.len;
  instructions_any->cap = instructions.cap;
}

// TODO: If any of the callee-saved registers were used by the register
// allocator, emit storing code (push).
static void amd64_emit_prolog(AsmCodeSection *section, PgAllocator *allocator) {

  Amd64Instruction ins_push = {
      .kind = AMD64_INSTRUCTION_KIND_PUSH,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rbp,
          },
  };
  amd64_add_instruction(&section->instructions, ins_push, allocator);

  Amd64Instruction ins_mov = {
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rbp,
          },
      .rhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rsp,
          },
  };
  amd64_add_instruction(&section->instructions, ins_mov, allocator);
}

// TODO: If any of the callee-saved registers were used by the register
// allocator, emit loading code (pop).
static void amd64_emit_epilog(AsmCodeSection *section, PgAllocator *allocator) {
  Amd64Instruction ins_pop = {
      .kind = AMD64_INSTRUCTION_KIND_POP,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rbp,
          },
  };
  amd64_add_instruction(&section->instructions, ins_pop, allocator);
}

static void amd64_print_operand(Amd64Operand operand) {
  switch (operand.kind) {
  case AMD64_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case AMD64_OPERAND_KIND_REGISTER:
    amd64_print_register(operand.reg);
    break;
  case AMD64_OPERAND_KIND_IMMEDIATE:
    printf("%" PRIu64, operand.immediate);
    break;
  case AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS: {
    char *size_cstr = "qword ptr";
    printf("%s [", size_cstr);
    amd64_print_register(operand.effective_address.base);
    if (operand.effective_address.index.value) {
      printf(" + ");
      amd64_print_register(operand.effective_address.index);
      printf(" * %" PRIu8 " ", operand.effective_address.scale);
    }
    printf("%s%" PRIi32 "]",
           operand.effective_address.displacement >= 0 ? "+" : "",
           operand.effective_address.displacement);
  } break;
  case AMD64_OPERAND_KIND_LABEL:
    PG_ASSERT(operand.label.value);
    printf(".%" PRIu32, operand.label.value);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void amd64_print_instructions(Amd64InstructionSlice instructions) {
  for (u64 i = 0; i < instructions.len; i++) {
    printf("[%" PRIu64 "] ", i);

    Amd64Instruction instruction = PG_SLICE_AT(instructions, i);
#if 0
    amd64_print_var_to_memory_location(
        instruction.var_to_memory_location_frozen);
#endif

    origin_print(instruction.origin);
    printf(": ");

    // TODO: Validate operands?
    switch (instruction.kind) {
    case AMD64_INSTRUCTION_KIND_NONE:
      PG_ASSERT(0);
    case AMD64_INSTRUCTION_KIND_MOV:
      printf("mov ");
      break;
    case AMD64_INSTRUCTION_KIND_ADD:
      printf("add ");
      break;
    case AMD64_INSTRUCTION_KIND_SUB:
      printf("sub ");
      break;
    case AMD64_INSTRUCTION_KIND_LEA:
      printf("lea ");
      break;
    case AMD64_INSTRUCTION_KIND_RET:
      printf("ret ");
      break;
    case AMD64_INSTRUCTION_KIND_SYSCALL:
      printf("syscall ");
      break;
    case AMD64_INSTRUCTION_KIND_PUSH:
      printf("push ");
      break;
    case AMD64_INSTRUCTION_KIND_POP:
      printf("pop ");
      break;
    case AMD64_INSTRUCTION_KIND_LABEL:
      // The operand carries the actual label.
      break;
    case AMD64_INSTRUCTION_KIND_JMP_IF_EQ:
      printf("je ");
      break;
    case AMD64_INSTRUCTION_KIND_JMP:
      printf("jmp ");
      break;
    case AMD64_INSTRUCTION_KIND_CMP:
      printf("cmp ");
      break;
    case AMD64_INSTRUCTION_KIND_SET_IF_EQ:
      printf("sete ");
      break;
    default:
      PG_ASSERT(0);
      break;
    }

    if (AMD64_OPERAND_KIND_NONE != instruction.lhs.kind) {
      amd64_print_operand(instruction.lhs);
    }

    if (AMD64_OPERAND_KIND_NONE != instruction.rhs.kind) {
      PG_ASSERT(AMD64_OPERAND_KIND_NONE != instruction.lhs.kind);

      printf(", ");
      amd64_print_operand(instruction.rhs);
    }

    if (AMD64_INSTRUCTION_KIND_LABEL == instruction.kind) {
      printf(":");
    }

    printf("\n");
  }
}

static void amd64_print_section(AsmCodeSection section) {
  if (ASM_SECTION_FLAG_GLOBAL & section.flags) {
    printf("global ");
    printf("%.*s", (i32)section.name.len, section.name.data);
    printf(":\n");
  }

  printf("%.*s", (i32)section.name.len, section.name.data);
  printf(":\n");

  Amd64InstructionSlice instructions = {
      .data = section.instructions.data,
      .len = section.instructions.len,
  };
  amd64_print_instructions(instructions);
}

static void amd64_print_program(AsmEmitter emitter) {
  for (u64 i = 0; i < emitter.program.text.len; i++) {
    AsmCodeSection section = PG_SLICE_AT(emitter.program.text, i);
    amd64_print_section(section);
    printf("\n");
  }
}

[[nodiscard]]
static u8 amd64_encode_register_value(Register reg) {
  return PG_SLICE_AT(amd64_register_to_encoded_value_slice, reg.value);
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

static void amd64_encode_instruction_mov(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_MOV == instruction.kind);
  // Illegal per amd64 rules.
  PG_ASSERT(!(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.rhs.kind &&
              AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind));

  // MOV reg64, imm64 | B8 +rq iq | Move an 64-bit immediate value into a 64-bit
  // register.
  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    u8 rex = AMD64_REX_DEFAULT;
    if (instruction.rhs.immediate > UINT32_MAX) {
      rex |= AMD64_REX_MASK_W;
    }
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_B;
    }

    if (AMD64_REX_DEFAULT != rex) {
      *PG_DYN_PUSH(sb, allocator) = rex;
    }

    u8 opcode = 0xb8;
    *PG_DYN_PUSH(sb, allocator) =
        opcode + (amd64_encode_register_value(instruction.lhs.reg) & 0b111);

    if (instruction.rhs.immediate <= UINT32_MAX) {
      pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.immediate, allocator);
    } else {
      pg_byte_buffer_append_u64(sb, instruction.rhs.immediate, allocator);
    }

    return;
  }

  // MOV reg/mem64, reg64 | 89 /r | Move the contents of a 64-bit register to a
  // 64-bit destination register or memory operand.
  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    if (amd64_is_register_64_bits_only(instruction.rhs.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x89;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm =
        (0b11 << 6) |
        (u8)((amd64_encode_register_value(instruction.rhs.reg) & 0b111) << 3) |
        (u8)(amd64_encode_register_value(instruction.lhs.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    return;
  }

  if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    PG_ASSERT(instruction.rhs.kind <= INT32_MAX);

    PG_ASSERT(amd64_rbp.value == instruction.lhs.effective_address.base.value &&
              "todo");
    PG_ASSERT(0 == instruction.lhs.effective_address.index.value && "todo");
    PG_ASSERT(0 == instruction.lhs.effective_address.scale && "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0xc7;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm = (0b10 /* rbp+disp32 */ << 6) |
               (u8)(amd64_encode_register_value(
                        instruction.lhs.effective_address.base) &
                    0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(
        sb, (u32)instruction.lhs.effective_address.displacement, allocator);
    pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.immediate, allocator);

    return;
  }

  if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    PG_ASSERT(instruction.lhs.effective_address.base.value == amd64_rbp.value &&
              "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(
            instruction.lhs.effective_address.base)) {
      rex |= AMD64_REX_MASK_B;
    }
    if (amd64_is_register_64_bits_only(instruction.rhs.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x89;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm =
        (0b10 /* [rbp] + disp32 */ << 6) |
        (u8)((amd64_encode_register_value(instruction.rhs.reg) & 0b111) << 3) |
        (u8)(amd64_encode_register_value(
                 instruction.lhs.effective_address.base) &
             0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(
        sb, (u32)instruction.lhs.effective_address.displacement, allocator);

    return;
  }

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.rhs.kind) {
    PG_ASSERT(amd64_rbp.value == instruction.rhs.effective_address.base.value &&
              "todo");
    PG_ASSERT(0 == instruction.rhs.effective_address.index.value && "todo");
    PG_ASSERT(0 == instruction.rhs.effective_address.scale && "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    if (amd64_is_register_64_bits_only(
            instruction.rhs.effective_address.base)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x8b;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm =
        (0b10 /* [rbp] + disp32 */ << 6) |
        (u8)((amd64_encode_register_value(instruction.lhs.reg) & 0b111) << 3) |
        (u8)(amd64_encode_register_value(
                 instruction.rhs.effective_address.base) &
             0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(
        sb, (u32)instruction.rhs.effective_address.displacement, allocator);

    return;
  }

  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_lea(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_LEA == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.rhs.kind);
  PG_ASSERT(0 == instruction.rhs.effective_address.index.value && "todo");
  PG_ASSERT(0 == instruction.rhs.effective_address.scale && "todo");
  PG_ASSERT(amd64_rbp.value == instruction.rhs.effective_address.base.value &&
            "todo");

  u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
  if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
    rex |= AMD64_REX_MASK_R;
  }
  if (amd64_is_register_64_bits_only(instruction.rhs.effective_address.base)) {
    rex |= AMD64_REX_MASK_B;
  }

  *PG_DYN_PUSH(sb, allocator) = rex;

  u8 opcode = 0x8d;
  *PG_DYN_PUSH(sb, allocator) = opcode;

  u8 modrm =
      (0b10 /* [rbp] + disp32 */ << 6) |
      (u8)((amd64_encode_register_value(instruction.lhs.reg) & 0b111) << 3) |
      (u8)((
          amd64_encode_register_value(instruction.rhs.effective_address.base) &
          0b111));
  *PG_DYN_PUSH(sb, allocator) = modrm;

  pg_byte_buffer_append_u32_within_capacity(
      sb, (u32)instruction.rhs.effective_address.displacement);
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
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    if (amd64_is_register_64_bits_only(instruction.rhs.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x03;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm =
        (0b11 << 6) |
        (u8)((amd64_encode_register_value(instruction.lhs.reg) & 0b111) << 3) |
        (u8)(amd64_encode_register_value(instruction.rhs.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;
    return;
  }

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    PG_ASSERT(instruction.rhs.immediate <= INT32_MAX);

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x81;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) |
               (u8)((amd64_encode_register_value(instruction.lhs.reg) & 0b111));
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.immediate, allocator);
    return;
  }
  if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.rhs.kind) {
    PG_ASSERT(0 == instruction.lhs.effective_address.scale && "todo");
    PG_ASSERT(0 == instruction.lhs.effective_address.index.value && "todo");
    PG_ASSERT(amd64_rbp.value == instruction.lhs.effective_address.base.value &&
              "todo");

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.rhs.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x01;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm =
        (0b10 /* rbp+disp32 */ << 6) |
        (u8)((amd64_encode_register_value(instruction.rhs.reg) & 0b111) << 3) |
        (u8)(amd64_encode_register_value(
            instruction.lhs.effective_address.base));

    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(
        sb, (u32)instruction.lhs.effective_address.displacement, allocator);

    return;
  }
  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.rhs.kind) {
    Register reg = instruction.lhs.reg;
    Amd64EffectiveAddress effective_address = instruction.rhs.effective_address;
    PG_ASSERT(0 == effective_address.scale && "todo");
    PG_ASSERT(0 == effective_address.index.value && "todo");
    PG_ASSERT(amd64_rbp.value == effective_address.base.value && "todo");

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
    u64 immediate = instruction.rhs.immediate;
    PG_ASSERT(immediate <= INT32_MAX);
    Amd64EffectiveAddress effective_address = instruction.lhs.effective_address;

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
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    if (amd64_is_register_64_bits_only(instruction.rhs.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x29;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm =
        (0b11 << 6) |
        (u8)((amd64_encode_register_value(instruction.lhs.reg) & 0b111) << 3) |
        (u8)(amd64_encode_register_value(instruction.rhs.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;
    return;
  }

  if (AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind) {
    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    PG_ASSERT(instruction.rhs.immediate <= UINT32_MAX);

    u8 opcode = 0x81;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) | (u8)(5 << 3) |
               (u8)(amd64_encode_register_value(instruction.lhs.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.immediate, allocator);
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
  PG_ASSERT(amd64_rbp.value == instruction.lhs.reg.value && "todo");

  u8 opcode = 0x50;
  *PG_DYN_PUSH(sb, allocator) =
      opcode + (amd64_encode_register_value(instruction.lhs.reg) & 0b111);
}

static void amd64_encode_instruction_pop(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_POP == instruction.kind);

  PG_ASSERT(amd64_rbp.value == instruction.lhs.reg.value && "todo");

  u8 opcode = 0x58;
  *PG_DYN_PUSH(sb, allocator) =
      opcode + (amd64_encode_register_value(instruction.lhs.reg) & 0b111);
}

static void amd64_encode_instruction_je(Pgu8Dyn *sb,
                                        Amd64Instruction instruction,
                                        AsmProgram *program,
                                        PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_JMP_IF_EQ == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_LABEL == instruction.lhs.kind);
  PG_ASSERT(instruction.lhs.label.value);

  u8 opcode1 = 0x0f;
  *PG_DYN_PUSH(sb, allocator) = opcode1;

  u8 opcode2 = 0x84;
  *PG_DYN_PUSH(sb, allocator) = opcode2;

  *PG_DYN_PUSH(&program->jumps_to_backpatch, allocator) = (LabelAddress){
      .label = instruction.lhs.label,
      .address_text = sb->len,
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
  PG_ASSERT(instruction.lhs.label.value);

  u8 opcode = 0xe9;
  *PG_DYN_PUSH(sb, allocator) = opcode;

  *PG_DYN_PUSH(&program->jumps_to_backpatch, allocator) = (LabelAddress){
      .label = instruction.lhs.label,
      .address_text = sb->len,
  };

  // Backpatched with `program.label_addresses`.
  pg_byte_buffer_append_u32(sb, 0, allocator);
}

static void amd64_encode_instruction_cmp(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_CMP == instruction.kind);

  if (AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind) {
    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    PG_ASSERT(instruction.rhs.immediate <= INT32_MAX);

    u8 opcode = 0x81;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm = (0b11 << 6) | (u8)(7 << 3) |
               (u8)(amd64_encode_register_value(instruction.lhs.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

    pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.immediate, allocator);
    return;
  }

  if (AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind &&
      AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.lhs.kind) {
    u64 immediate = instruction.rhs.immediate;
    Amd64EffectiveAddress effective_address = instruction.lhs.effective_address;
    PG_ASSERT(effective_address.base.value == amd64_rbp.value && "todo");
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

  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_sete(Pgu8Dyn *sb,
                                          Amd64Instruction instruction,
                                          PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_SET_IF_EQ == instruction.kind);

  (void)sb;
  (void)allocator;

  // PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction(AsmEmitter *asm_emitter, Pgu8Dyn *sb,
                                     Amd64Instruction instruction,
                                     PgAllocator *allocator) {
  (void)asm_emitter;

  switch (instruction.kind) {
  case AMD64_INSTRUCTION_KIND_NONE:
    PG_ASSERT(0);
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

  case AMD64_INSTRUCTION_KIND_LABEL:
    PG_ASSERT(instruction.lhs.label.value);
    *PG_DYN_PUSH(&asm_emitter->program.label_addresses, allocator) =
        (LabelAddress){
            .label = instruction.lhs.label,
            .address_text = sb->len,
        };
    break;

  case AMD64_INSTRUCTION_KIND_JMP_IF_EQ:
    amd64_encode_instruction_je(sb, instruction, &asm_emitter->program,
                                allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP:
    amd64_encode_instruction_jmp(sb, instruction, &asm_emitter->program,
                                 allocator);
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
amd64_convert_lir_operand_to_amd64_operand(Amd64Emitter *emitter,
                                           LirOperand lir_op) {
  (void)emitter;

  switch (lir_op.kind) {
  case LIR_OPERAND_KIND_VIRTUAL_REGISTER: {
    MemoryLocation mem_loc =
        PG_SLICE_AT(emitter->metadata, lir_op.meta_idx.value).memory_location;
    switch (mem_loc.kind) {
    case MEMORY_LOCATION_KIND_REGISTER: {
      PG_ASSERT(MEMORY_LOCATION_KIND_REGISTER == mem_loc.kind);
      PG_ASSERT(mem_loc.reg.value);

      return (Amd64Operand){
          .kind = AMD64_OPERAND_KIND_REGISTER,
          .reg = mem_loc.reg,
      };
    }
    case MEMORY_LOCATION_KIND_STATUS_REGISTER:
      PG_ASSERT(0 && "todo");
      break;
    case MEMORY_LOCATION_KIND_STACK: {
      PG_ASSERT(mem_loc.base_pointer_offset);
      return (Amd64Operand){
          .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
          .effective_address =
              {
                  .base = amd64_rbp,
                  .displacement = -mem_loc.base_pointer_offset,
              },
      };
    }
    case MEMORY_LOCATION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
#if 0
    InterferenceNode node =
        PG_SLICE_AT(emitter->interference_nodes, node_idx.value);
    PG_ASSERT(node.reg.value || node.base_stack_pointer_offset);

    if (0 == node.base_stack_pointer_offset) {
      return (Amd64Operand){
          .kind = AMD64_OPERAND_KIND_REGISTER,
          .reg = node.reg,
      };
    }

    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
        .effective_address.base = amd64_rbp,
        .effective_address.displacement = -(i32)node.base_stack_pointer_offset,
    };
#endif
  }
  case LIR_OPERAND_KIND_IMMEDIATE:
    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_IMMEDIATE,
        .immediate = lir_op.immediate,
    };
  case LIR_OPERAND_KIND_LABEL: {
    PG_ASSERT(lir_op.label.value);
    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_LABEL,
        .label = lir_op.label,
    };
  }
  case LIR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void amd64_sanity_check_section(Amd64Emitter *emitter,
                                       AsmCodeSection section) {
  (void)emitter;

  for (u64 i = 0; i < section.instructions.len; i++) {
    Amd64Instruction ins =
        PG_C_ARRAY_AT((Amd64Instruction *)section.instructions.data,
                      section.instructions.len, i);

    // Prohibited by amd64 rules.
    PG_ASSERT(!(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.lhs.kind &&
                AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.rhs.kind));

    PG_ASSERT(!(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.lhs.kind &&
                AMD64_OPERAND_KIND_IMMEDIATE == ins.rhs.kind));

    PG_ASSERT(!(AMD64_OPERAND_KIND_IMMEDIATE == ins.lhs.kind &&
                AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.rhs.kind));
  }
}

static void amd64_sanity_check_program(Amd64Emitter *emitter) {
  for (u64 i = 0; i < emitter->program.text.len; i++) {
    AsmCodeSection section = PG_SLICE_AT(emitter->program.text, i);
    amd64_sanity_check_section(emitter, section);
  }
}

static void amd64_lir_to_asm(Amd64Emitter *emitter, AsmCodeSection *section,
                             LirInstruction lir, PgAllocator *allocator) {
  switch (lir.kind) {
  case LIR_INSTRUCTION_KIND_ADD: {
    PG_ASSERT(2 == lir.operands.len);
    LirOperand lhs = PG_SLICE_AT(lir.operands, 0);
    LirOperand rhs = PG_SLICE_AT(lir.operands, 1);

    PG_ASSERT(LIR_OPERAND_KIND_VIRTUAL_REGISTER == lhs.kind);
    MemoryLocation lhs_mem_loc =
        PG_SLICE_AT(emitter->metadata, lhs.meta_idx.value).memory_location;

    // Easy case: `add rax, 123` or `add rax, [rbp-8]`.
    if (MEMORY_LOCATION_KIND_REGISTER == lhs_mem_loc.kind) {
      Amd64Instruction instruction = {
          .kind = AMD64_INSTRUCTION_KIND_ADD,
          .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
          .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
          .origin = lir.origin,
      };
      amd64_add_instruction(&section->instructions, instruction, allocator);
      return;
    }

    // Need to insert load/stores.

    Amd64Instruction ins_load = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .lhs =
            {
                .kind = AMD64_OPERAND_KIND_REGISTER,
                // TODO: pick one of the spill registers?
                .reg = amd64_spill_registers[0], // TODO: mark it as used?
            },
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
    };
    amd64_add_instruction(&section->instructions, ins_load, allocator);

    Amd64Instruction ins_add = {
        .kind = AMD64_INSTRUCTION_KIND_ADD,
        .origin = lir.origin,
        .lhs = ins_load.lhs,
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
    };
    amd64_add_instruction(&section->instructions, ins_add, allocator);

    Amd64Instruction ins_store = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
        .rhs = ins_load.lhs,
        .origin = lir.origin,
    };

    amd64_add_instruction(&section->instructions, ins_store, allocator);
  } break;
  case LIR_INSTRUCTION_KIND_SUB: {
    PG_ASSERT(2 == lir.operands.len);
    LirOperand lhs = PG_SLICE_AT(lir.operands, 0);
    LirOperand rhs = PG_SLICE_AT(lir.operands, 1);

    PG_ASSERT(LIR_OPERAND_KIND_VIRTUAL_REGISTER == lhs.kind);

    MemoryLocation lhs_mem_loc =
        PG_SLICE_AT(emitter->metadata, lhs.meta_idx.value).memory_location;

    PG_ASSERT(MEMORY_LOCATION_KIND_REGISTER == lhs_mem_loc.kind &&
              "todo: load/store");

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_SUB,
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
        .origin = lir.origin,
    };

    amd64_add_instruction(&section->instructions, instruction, allocator);

  } break;
  case LIR_INSTRUCTION_KIND_MOV: {
    PG_ASSERT(2 == lir.operands.len);

    LirOperand dst = PG_SLICE_AT(lir.operands, 0);
    LirOperand src = PG_SLICE_AT(lir.operands, 1);

    PG_ASSERT(LIR_OPERAND_KIND_VIRTUAL_REGISTER == dst.kind);
    MemoryLocation dst_mem_loc =
        PG_SLICE_AT(emitter->metadata, dst.meta_idx.value).memory_location;

    // Easy case: `sete rax` or `sete [rbp-8]`
    if (LIR_OPERAND_KIND_VIRTUAL_REGISTER == src.kind) {
      MemoryLocation src_mem_loc =
          PG_SLICE_AT(emitter->metadata, src.meta_idx.value).memory_location;

      if (MEMORY_LOCATION_KIND_STATUS_REGISTER == src_mem_loc.kind) {
        Amd64Instruction ins = {
            .kind = AMD64_INSTRUCTION_KIND_SET_IF_EQ,
            .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, dst),
            .origin = lir.origin,
        };
        amd64_add_instruction(&section->instructions, ins, allocator);
        return;
      }
    }

    // Easy case: `mov rax, 123`.
    if (MEMORY_LOCATION_KIND_REGISTER == dst_mem_loc.kind &&
        LIR_OPERAND_KIND_IMMEDIATE == src.kind) {
      Amd64Instruction instruction = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, dst),
          .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, src),
          .origin = lir.origin,
      };

      amd64_add_instruction(&section->instructions, instruction, allocator);
      return;
    }

    // Need to use a spill register: `mov [rbp-8], 123` is not allowed.
    // Need to transform it to a store: `mov r10, 123; mov [rbp-8], r10`.
    if (MEMORY_LOCATION_KIND_REGISTER != dst_mem_loc.kind &&
        LIR_OPERAND_KIND_IMMEDIATE == src.kind) {
      Amd64Instruction ins_load = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs =
              {
                  .kind = AMD64_OPERAND_KIND_REGISTER,
                  // TODO: pick one of the spill registers?
                  .reg = amd64_spill_registers[0], // TODO: mark it as used?
              },
          .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, src),
      };
      amd64_add_instruction(&section->instructions, ins_load, allocator);

      Amd64Instruction ins_store = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, dst),
          .rhs = ins_load.lhs,
          .origin = lir.origin,
      };

      amd64_add_instruction(&section->instructions, ins_store, allocator);
      return;
    }

    PG_ASSERT(LIR_OPERAND_KIND_VIRTUAL_REGISTER == src.kind);
    MemoryLocation src_mem_loc =
        PG_SLICE_AT(emitter->metadata, src.meta_idx.value).memory_location;

    // Easy case: at least one memory location is a register.
    if ((MEMORY_LOCATION_KIND_REGISTER == dst_mem_loc.kind ||
         MEMORY_LOCATION_KIND_REGISTER == src_mem_loc.kind)) {
      Amd64Instruction instruction = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, dst),
          .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, src),
          .origin = lir.origin,
      };

      amd64_add_instruction(&section->instructions, instruction, allocator);
      return;
    }

    // Need to insert load/store instructions from/to stack/memory.

    if (MEMORY_LOCATION_KIND_REGISTER != src_mem_loc.kind) {
      Amd64Instruction ins_load = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs =
              {
                  .kind = AMD64_OPERAND_KIND_REGISTER,
                  // TODO: pick one of the spill registers?
                  .reg = amd64_spill_registers[0], // TODO: mark it as used?
              },
          .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, src),
      };
      amd64_add_instruction(&section->instructions, ins_load, allocator);

      Amd64Instruction ins_store = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, dst),
          .rhs = ins_load.lhs,
          .origin = lir.origin,
      };

      amd64_add_instruction(&section->instructions, ins_store, allocator);
      return;
    }

    else if (MEMORY_LOCATION_KIND_REGISTER != dst_mem_loc.kind) {
      Amd64Instruction ins_store = {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .lhs =
              {
                  .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
                  .effective_address =
                      {
                          .base = amd64_rbp,
                          .displacement = -(i32)dst_mem_loc.base_pointer_offset,
                      },
              },
          .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, src),
      };
      amd64_add_instruction(&section->instructions, ins_store, allocator);
    } else {
      PG_ASSERT(0);
    }

  } break;
  case LIR_INSTRUCTION_KIND_SYSCALL: {
    PG_ASSERT(0 == lir.operands.len);
    Amd64Instruction ins = {
        .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
        .origin = lir.origin,
    };
    amd64_add_instruction(&section->instructions, ins, allocator);
  } break;

  case LIR_INSTRUCTION_KIND_JUMP_IF_EQ: {
    PG_ASSERT(1 == lir.operands.len);

    LirOperand label = PG_SLICE_AT(lir.operands, 0);
    PG_ASSERT(LIR_OPERAND_KIND_LABEL == label.kind);
    PG_ASSERT(label.label.value);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_JMP_IF_EQ,
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, label),
        .origin = lir.origin,
    };

    amd64_add_instruction(&section->instructions, instruction, allocator);

  } break;

  case LIR_INSTRUCTION_KIND_LABEL: {
    PG_ASSERT(1 == lir.operands.len);

    LirOperand label = PG_SLICE_AT(lir.operands, 0);
    PG_ASSERT(LIR_OPERAND_KIND_LABEL == label.kind);
    PG_ASSERT(label.label.value);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_LABEL,
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, label),
        .origin = lir.origin,
    };

    amd64_add_instruction(&section->instructions, instruction, allocator);
  } break;

  case LIR_INSTRUCTION_KIND_JUMP: {
    PG_ASSERT(1 == lir.operands.len);

    LirOperand label = PG_SLICE_AT(lir.operands, 0);
    PG_ASSERT(LIR_OPERAND_KIND_LABEL == label.kind);
    PG_ASSERT(label.label.value);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_JMP,
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, label),
        .origin = lir.origin,
    };

    amd64_add_instruction(&section->instructions, instruction, allocator);
  } break;

  case LIR_INSTRUCTION_KIND_CMP: {
    PG_ASSERT(3 == lir.operands.len);

    LirOperand res = PG_SLICE_AT(lir.operands, 0);
    (void)res; // TODO: Use?
    LirOperand lhs = PG_SLICE_AT(lir.operands, 1);
    LirOperand rhs = PG_SLICE_AT(lir.operands, 2);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_CMP,
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
        .origin = lir.origin,
    };

    amd64_add_instruction(&section->instructions, instruction, allocator);
  } break;
  case LIR_INSTRUCTION_KIND_ADDRESS_OF: {
    PG_ASSERT(2 == lir.operands.len);

    LirOperand dst = PG_SLICE_AT(lir.operands, 0);
    LirOperand src = PG_SLICE_AT(lir.operands, 1);

    PG_ASSERT(LIR_OPERAND_KIND_VIRTUAL_REGISTER == dst.kind);
    PG_ASSERT(LIR_OPERAND_KIND_VIRTUAL_REGISTER == src.kind);

    MemoryLocation src_mem_loc =
        PG_SLICE_AT(emitter->metadata, src.meta_idx.value).memory_location;

    PG_ASSERT(MEMORY_LOCATION_KIND_STACK == src_mem_loc.kind);

    Amd64Instruction ins_load = {
        .kind = AMD64_INSTRUCTION_KIND_LEA,
        .origin = lir.origin,
        .lhs =
            {
                .kind = AMD64_OPERAND_KIND_REGISTER,
                // TODO: pick one of the spill registers?
                .reg = amd64_spill_registers[0], // TODO: mark it as used?
            },
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, src),
    };
    PG_ASSERT(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins_load.rhs.kind);
    amd64_add_instruction(&section->instructions, ins_load, allocator);

    Amd64Instruction ins_store = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, dst),
        .rhs = ins_load.lhs,
        .origin = lir.origin,
    };
    amd64_add_instruction(&section->instructions, ins_store, allocator);

  } break;

  case LIR_INSTRUCTION_KIND_COMPARISON: {
    PG_ASSERT(2 == lir.operands.len);
    PG_ASSERT(0);
  } break;

  case LIR_INSTRUCTION_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static Register
amd64_map_constraint_to_register(AsmEmitter *asm_emitter,
                                 LirVirtualRegisterConstraint constraint) {
  (void)asm_emitter;

  switch (constraint) {
  case LIR_VIRT_REG_CONSTRAINT_NONE:
    return (Register){0};
  case LIR_VIRT_REG_CONSTRAINT_CONDITION_FLAGS:
    return amd64_rflags;
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM:
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET:
    return amd64_rax;
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL0:
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL1:
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL2:
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL3:
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL4:
  case LIR_VIRT_REG_CONSTRAINT_SYSCALL5:
    return PG_SLICE_AT(amd64_arch.syscall_calling_convention,
                       constraint - LIR_VIRT_REG_CONSTRAINT_SYSCALL0);
  default:
    PG_ASSERT(0);
  }
}

static void amd64_emit_lirs_to_asm(AsmEmitter *asm_emitter,
                                   AsmCodeSection *section,
                                   LirInstructionSlice lirs, bool verbose,
                                   PgAllocator *allocator) {
  Amd64Emitter *amd64_emitter = (Amd64Emitter *)asm_emitter;

  Amd64Instruction stack_sub = {
      .kind = AMD64_INSTRUCTION_KIND_SUB,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rsp,
          },
      .rhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_IMMEDIATE,
              .immediate = 0, // Backpatched.
          },
  };
  amd64_add_instruction(&section->instructions, stack_sub, allocator);
  u64 stack_sub_instruction_idx = section->instructions.len - 1;

  asm_color_interference_graph(asm_emitter, verbose, allocator);

  if (verbose) {
    printf("\n------------ Colored interference graph ------------\n");
    asm_print_interference_graph(amd64_emitter->interference_graph,
                                 amd64_emitter->metadata);

    printf("\n------------ Adjacency matrix of interference graph "
           "------------\n\n");
    pg_adjacency_matrix_print(amd64_emitter->interference_graph);
  }
  asm_sanity_check_interference_graph(amd64_emitter->interference_graph,
                                      amd64_emitter->metadata, true);

  for (u64 i = 0; i < lirs.len; i++) {
    amd64_lir_to_asm(amd64_emitter, section, PG_SLICE_AT(lirs, i), allocator);
  }

  if (amd64_emitter->stack_base_pointer_max_offset > 0) {
    u32 rsp_max_offset_aligned_16 =
        (u32)PG_ROUNDUP(amd64_emitter->stack_base_pointer_max_offset, 16);

    PG_C_ARRAY_AT_PTR((Amd64Instruction *)section->instructions.data,
                      section->instructions.len, stack_sub_instruction_idx)
        ->rhs.immediate = rsp_max_offset_aligned_16;

    Amd64Instruction stack_add = {
        .kind = AMD64_INSTRUCTION_KIND_ADD,
        .lhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = amd64_rsp,
            },
        .rhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                .immediate = rsp_max_offset_aligned_16,
            },
    };

    amd64_add_instruction(&section->instructions, stack_add, allocator);
  } else {
    PG_C_ARRAY_AT_PTR((Amd64Instruction *)section->instructions.data,
                      section->instructions.len, stack_sub_instruction_idx)
        ->tombstone = true;
  }
}

static void amd64_emit_program(AsmEmitter *asm_emitter,
                               LirInstructionSlice lirs, bool verbose,
                               PgAllocator *allocator) {

  {
    AsmCodeSection section_start = {
        .flags = ASM_SECTION_FLAG_GLOBAL,
        .name = PG_S("_start"),
    };
    amd64_emit_prolog(&section_start, allocator);
    amd64_emit_lirs_to_asm(asm_emitter, &section_start, lirs, verbose,
                           allocator);
    amd64_emit_epilog(&section_start, allocator);

    *PG_DYN_PUSH(&asm_emitter->program.text, allocator) = section_start;
  }

  amd64_sanity_check_program((Amd64Emitter *)asm_emitter);
}

static void amd64_encode_section(AsmEmitter *asm_emitter, Pgu8Dyn *sb,
                                 AsmCodeSection section,
                                 PgAllocator *allocator) {
  for (u64 i = 0; i < section.instructions.len; i++) {
    Amd64Instruction ins =
        PG_C_ARRAY_AT((Amd64Instruction *)section.instructions.data,
                      section.instructions.len, i);
    amd64_encode_instruction(asm_emitter, sb, ins, allocator);
  }

  for (u64 i = 0; i < asm_emitter->program.jumps_to_backpatch.len; i++) {
    LabelAddress jump_to_backpatch =
        PG_SLICE_AT(asm_emitter->program.jumps_to_backpatch, i);
    PG_ASSERT(jump_to_backpatch.label.value > 0);
    PG_ASSERT(jump_to_backpatch.address_text > 0);
    PG_ASSERT(jump_to_backpatch.address_text <= sb->len - 1);

    LabelAddress label = {0};
    for (u64 j = 0; j < asm_emitter->program.label_addresses.len; j++) {
      label = PG_SLICE_AT(asm_emitter->program.label_addresses, j);
      PG_ASSERT(label.label.value > 0);
      PG_ASSERT(label.address_text <= sb->len - 1);

      if (label.label.value == jump_to_backpatch.label.value) {
        break;
      }
    }
    PG_ASSERT(label.label.value > 0);
    PG_ASSERT(label.label.value == jump_to_backpatch.label.value);

    u8 *jump_displacement_encoded =
        PG_SLICE_AT_PTR(sb, jump_to_backpatch.address_text);
    i64 displacement = (i64)label.address_text -
                       (i64)jump_to_backpatch.address_text - (i64)sizeof(i32);
    PG_ASSERT(displacement <= INT32_MAX);

    memcpy(jump_displacement_encoded, &displacement, sizeof(i32));
  }
}

[[nodiscard]]
static Pgu8Slice amd64_encode_program_text(AsmEmitter *asm_emitter,
                                           PgAllocator *allocator) {
  Pgu8Dyn sb = {0};
  PG_DYN_ENSURE_CAP(&sb, 4 * PG_KiB, allocator);

  for (u64 i = 0; i < asm_emitter->program.text.len; i++) {
    AsmCodeSection section = PG_SLICE_AT(asm_emitter->program.text, i);
    amd64_encode_section(asm_emitter, &sb, section, allocator);
  }

  return PG_DYN_SLICE(Pgu8Slice, sb);
}

[[nodiscard]]
static AsmEmitter *amd64_make_asm_emitter(InterferenceGraph interference_graph,
                                          LirEmitter *lir_emitter,
                                          PgString exe_path,
                                          PgAllocator *allocator) {
  Amd64Emitter *amd64_emitter =
      pg_alloc(allocator, sizeof(Amd64Emitter), _Alignof(Amd64Emitter), 1);
  amd64_emitter->emit_program = amd64_emit_program;
  amd64_emitter->print_program = amd64_print_program;
  amd64_emitter->map_constraint_to_register = amd64_map_constraint_to_register;
  amd64_emitter->encode_program_text = amd64_encode_program_text;

  amd64_emitter->metadata = lir_emitter->metadata;
  amd64_emitter->interference_graph = interference_graph;
  amd64_emitter->lir_emitter = lir_emitter;

  amd64_emitter->gprs_count = amd64_register_allocator_gprs_slice.len;
  amd64_emitter->program.file_path = exe_path;
  amd64_emitter->program.vm_start = 1 << 22;
  // TODO: rodata.
  // u64 rodata_offset = 0x2000;

  return (AsmEmitter *)amd64_emitter;
}
