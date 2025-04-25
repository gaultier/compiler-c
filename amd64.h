#pragma once
#include "ir.h"
#include "lir.h"

static const Register amd64_rax = {1};
static const Register amd64_rbx = {2};
static const Register amd64_rcx = {3};
static const Register amd64_rdx = {4};
static const Register amd64_rdi = {5};
static const Register amd64_rsi = {6};
static const Register amd64_r8 = {7};
static const Register amd64_r9 = {8};
static const Register amd64_r10 = {9};
static const Register amd64_r11 = {10};
static const Register amd64_r12 = {11};
static const Register amd64_r13 = {12};
static const Register amd64_r14 = {13};
static const Register amd64_r15 = {14};
static const Register amd64_rsp = {15};
static const Register amd64_rbp = {16};

static const PgString amd64_register_to_string[16 + 1] = {
    [0] = PG_S("UNREACHABLE"), [1] = PG_S("rax"),  [2] = PG_S("rbx"),
    [3] = PG_S("rcx"),         [4] = PG_S("rdx"),  [5] = PG_S("rdi"),
    [6] = PG_S("rsi"),         [7] = PG_S("r8"),   [8] = PG_S("r9"),
    [9] = PG_S("r10"),         [10] = PG_S("r11"), [11] = PG_S("r12"),
    [12] = PG_S("r13"),        [13] = PG_S("r14"), [14] = PG_S("r15"),
    [15] = PG_S("rsp"),        [16] = PG_S("rbp"),
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

static const Register amd64_call_preserved[] = {
    amd64_rbx, amd64_rsp, amd64_rbp, amd64_r12, amd64_r13, amd64_r14, amd64_r15,
};

static const Register amd64_calling_convention[] = {
    amd64_rdi, amd64_rsi, amd64_rdx, amd64_rcx, amd64_r8, amd64_r9,
};

static const Register amd64_syscall_calling_convention[] = {
    amd64_rax, amd64_rdi, amd64_rsi, amd64_rdx, amd64_rcx, amd64_r8, amd64_r9,
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
    .syscall_calling_convention =
        {
            .data = (Register *)amd64_syscall_calling_convention,
            .len = PG_STATIC_ARRAY_LEN(amd64_syscall_calling_convention),
        },
    .stack_pointer = amd64_rsp,
    .base_pointer = amd64_rbp,
};

typedef enum {
  AMD64_OPERAND_KIND_NONE,
  AMD64_OPERAND_KIND_REGISTER,
  AMD64_OPERAND_KIND_IMMEDIATE,
  AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
  AMD64_OPERAND_KIND_LABEL,
} Amd64OperandKind;

// Effective address = `base + index * scale + displacement`.
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
    IrLabelId label;
  };
} Amd64Operand;

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
} Amd64InstructionKind;

typedef struct {
  Amd64InstructionKind kind;
  Amd64Operand lhs, rhs;
  Origin origin;
  VarToMemoryLocationDyn var_to_memory_location_frozen;
} Amd64Instruction;
PG_SLICE(Amd64Instruction) Amd64InstructionSlice;
PG_DYN(Amd64Instruction) Amd64InstructionDyn;

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
PG_DYN(Amd64Section) Amd64SectionDyn;

typedef enum {
  AMD64_CONSTANT_KIND_NONE,
  AMD64_CONSTANT_KIND_U64,
  AMD64_CONSTANT_KIND_BYTES,
} Amd64ConstantKind;

typedef struct {
  PgString name;
  u64 address_absolute;
  Amd64ConstantKind kind;
  union {
    u64 n64;
    PgString bytes;
  };
} Amd64Constant;
PG_SLICE(Amd64Constant) Amd64ConstantSlice;
PG_DYN(Amd64Constant) Amd64ConstantDyn;

typedef struct {
  Amd64SectionSlice text;
  Amd64ConstantSlice rodata;
  u64 vm_start;
  LabelAddressDyn label_addresses;
  LabelAddressDyn jumps_to_backpatch;

  PgString file_name;
} Amd64Program;

typedef struct {
  // Track in which locations is a var stored currently.
  VarToMemoryLocationDyn var_to_memory_location;
  u32 rbp_offset;
  u32 rbp_max_offset;
} Amd64RegisterAllocator;

static void amd64_print_register(Register reg) {
  PgString s = PG_SLICE_AT(amd64_register_to_string_slice, reg.value);
  printf("%.*s", (i32)s.len, s.data);
}

static void amd64_emit_prolog(Amd64InstructionDyn *instructions,
                              PgAllocator *allocator) {
  *PG_DYN_PUSH(instructions, allocator) = (Amd64Instruction){
      .kind = AMD64_INSTRUCTION_KIND_PUSH,
      .origin = {.synthetic = true},
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rbp,
          },
  };

  *PG_DYN_PUSH(instructions, allocator) = (Amd64Instruction){
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .origin = {.synthetic = true},
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
}

static void amd64_emit_epilog(Amd64InstructionDyn *instructions,
                              PgAllocator *allocator) {
  *PG_DYN_PUSH(instructions, allocator) = (Amd64Instruction){
      .kind = AMD64_INSTRUCTION_KIND_POP,
      .origin = {.synthetic = true},
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rbp,
          },
  };
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
  case AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS:
    printf("[");
    amd64_print_register(operand.effective_address.base);
    if (operand.effective_address.index.value) {
      printf(" + ");
      amd64_print_register(operand.effective_address.index);
      printf(" * %" PRIu8 " ", operand.effective_address.scale);
    }
    printf("%s%" PRIi32 "]",
           operand.effective_address.displacement >= 0 ? "+" : "",
           operand.effective_address.displacement);
    break;
  case AMD64_OPERAND_KIND_LABEL:
    printf(".%" PRIu32, operand.label.value);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void amd64_print_var_to_memory_location(
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
        amd64_print_register(loc.reg);
        break;
      case MEMORY_LOCATION_KIND_STACK: {
        amd64_print_register(amd64_rbp);
        i32 offset = loc.base_pointer_offset;
        printf("%" PRIi32, offset);
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

static void amd64_print_instructions(Amd64InstructionSlice instructions) {
  for (u64 i = 0; i < instructions.len; i++) {
    printf("[%" PRIu64 "]\n", i);

    Amd64Instruction instruction = PG_SLICE_AT(instructions, i);
    amd64_print_var_to_memory_location(
        instruction.var_to_memory_location_frozen);

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
      PG_ASSERT(instruction.lhs.label.value > 0);
      printf(".%u:", instruction.lhs.label.value);
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

    printf("\n");
  }
}

[[maybe_unused]]
static void amd64_print_section(Amd64Section section) {
  if (AMD64_SECTION_FLAG_GLOBAL & section.flags) {
    printf("global ");
    printf("%.*s", (i32)section.name.len, section.name.data);
    printf(":\n");
  }

  printf("%.*s", (i32)section.name.len, section.name.data);
  printf(":\n");

  amd64_print_instructions(section.instructions);
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

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0xc7;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm = (0b11 << 6) |
               (u8)(amd64_encode_register_value(instruction.lhs.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

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
        sb, (u32)instruction.lhs.effective_address.displacement, allocator);

    return;
  }

  PG_ASSERT(0 && "todo");
}

static void amd64_encode_instruction_lea(Pgu8Dyn *sb,
                                         Amd64Instruction instruction,
                                         Amd64Program program,
                                         PgAllocator *allocator) {
  (void)sb;
  (void)program;
  (void)allocator;

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

    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.rhs.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x01;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm =
        (0b10 << 6) |
        (u8)((amd64_encode_register_value(instruction.rhs.reg) & 0b111) << 3) |
        0b100; // sib + imm32

    *PG_DYN_PUSH(sb, allocator) = modrm;

    u8 sib =
        (0b100 << 3) /* no index */
        | (amd64_encode_register_value(instruction.lhs.effective_address.base) &
           0b111);
    *PG_DYN_PUSH(sb, allocator) = sib;

    pg_byte_buffer_append_u64(
        sb, (u32)instruction.rhs.effective_address.displacement, allocator);

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
                                        Amd64Program *program,
                                        PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_JMP_IF_EQ == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_LABEL == instruction.lhs.kind);
  PG_ASSERT(instruction.lhs.label.value > 0);

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
                                         Amd64Program *program,
                                         PgAllocator *allocator) {
  PG_ASSERT(AMD64_INSTRUCTION_KIND_JMP == instruction.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_LABEL == instruction.lhs.kind);
  PG_ASSERT(instruction.lhs.label.value > 0);

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

  PG_ASSERT(AMD64_OPERAND_KIND_IMMEDIATE == instruction.rhs.kind && "todo");
  PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == instruction.lhs.kind && "todo");

  u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
  if (amd64_is_register_64_bits_only(instruction.lhs.reg)) {
    rex |= AMD64_REX_MASK_B;
  }
  *PG_DYN_PUSH(sb, allocator) = rex;

  PG_ASSERT(instruction.rhs.immediate <= UINT32_MAX);

  u8 opcode = 0x81;
  *PG_DYN_PUSH(sb, allocator) = opcode;

  u8 modrm = (0b11 << 6) | (u8)(7 << 3) |
             (u8)(amd64_encode_register_value(instruction.lhs.reg) & 0b111);
  *PG_DYN_PUSH(sb, allocator) = modrm;

  pg_byte_buffer_append_u32(sb, (u32)instruction.rhs.immediate, allocator);
}

static void amd64_encode_instruction(Pgu8Dyn *sb, Amd64Instruction instruction,
                                     Amd64Program *program,
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
  case AMD64_INSTRUCTION_KIND_SUB:
    amd64_encode_instruction_sub(sb, instruction, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_LEA:
    amd64_encode_instruction_lea(sb, instruction, *program, allocator);
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
    PG_ASSERT(instruction.lhs.label.value > 0);
    *PG_DYN_PUSH(&program->label_addresses, allocator) = (LabelAddress){
        .label = instruction.lhs.label,
        .address_text = sb->len,
    };
    break;

  case AMD64_INSTRUCTION_KIND_JMP_IF_EQ:
    amd64_encode_instruction_je(sb, instruction, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_JMP:
    amd64_encode_instruction_jmp(sb, instruction, program, allocator);
    break;
  case AMD64_INSTRUCTION_KIND_CMP:
    amd64_encode_instruction_cmp(sb, instruction, allocator);
    break;

  default:
    PG_ASSERT(0);
  }
}

static void amd64_encode_section(Pgu8Dyn *sb, Amd64Section section,
                                 Amd64Program *program,
                                 PgAllocator *allocator) {
  for (u64 i = 0; i < section.instructions.len; i++) {
    Amd64Instruction instruction = PG_SLICE_AT(section.instructions, i);
    amd64_encode_instruction(sb, instruction, program, allocator);
  }

  for (u64 i = 0; i < program->jumps_to_backpatch.len; i++) {
    LabelAddress jump_to_backpatch =
        PG_SLICE_AT(program->jumps_to_backpatch, i);
    PG_ASSERT(jump_to_backpatch.label.value > 0);
    PG_ASSERT(jump_to_backpatch.address_text > 0);
    PG_ASSERT(jump_to_backpatch.address_text <= sb->len - 1);

    LabelAddress label = {0};
    for (u64 j = 0; j < program->label_addresses.len; j++) {
      label = PG_SLICE_AT(program->label_addresses, j);
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
static PgString amd64_encode_program_text(Amd64Program *program,
                                          PgAllocator *allocator) {
  Pgu8Dyn sb = {0};
  PG_DYN_ENSURE_CAP(&sb, 16 * PG_KiB, allocator);

  for (u64 i = 0; i < program->text.len; i++) {
    Amd64Section section = PG_SLICE_AT(program->text, i);
    amd64_encode_section(&sb, section, program, allocator);
  }

  return PG_DYN_SLICE(PgString, sb);
}

[[nodiscard]] static VarToMemoryLocationDyn
amd64_memory_location_clone(VarToMemoryLocationDyn var_to_memory_location,
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
amd64_memory_location_find_var(VarToMemoryLocationDyn var_to_memory_location,
                               IrVar var) {
  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation *elem = PG_SLICE_AT_PTR(&var_to_memory_location, i);
    if (elem->var.id.value == var.id.value) {
      return &elem->locations;
    }
  }

  return nullptr;
}

[[nodiscard]]
static MemoryLocation *amd64_memory_location_find_var_on_stack(
    VarToMemoryLocationDyn var_to_memory_location, IrVar var) {
  MemoryLocationDyn *locations =
      amd64_memory_location_find_var(var_to_memory_location, var);

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

static void
amd64_memory_location_add(VarToMemoryLocationDyn *var_to_memory_location,
                          IrVar var, MemoryLocation mem_loc,
                          PgAllocator *allocator) {
  MemoryLocationDyn *locations =
      amd64_memory_location_find_var(*var_to_memory_location, var);

  if (!locations) {
    *PG_DYN_PUSH(var_to_memory_location, allocator) =
        (VarToMemoryLocation){.var = var};
    locations = &PG_SLICE_LAST_PTR(var_to_memory_location)->locations;
  }

  PG_ASSERT(locations);

  *PG_DYN_PUSH(locations, allocator) = mem_loc;
}

static void amd64_memory_location_record_var_copy(
    VarToMemoryLocationDyn *var_to_memory_location, IrVar var,
    MemoryLocation loc_new, PgAllocator *allocator) {
  MemoryLocationDyn *locations =
      amd64_memory_location_find_var(*var_to_memory_location, var);
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

static MemoryLocation *amd64_memory_location_find_var_best(
    VarToMemoryLocationDyn var_to_memory_location, IrVar var) {
  MemoryLocation *loc = amd64_memory_location_find_var_in_register_any(
      var_to_memory_location, var);
  if (loc) {
    return loc;
  }

  loc = amd64_memory_location_find_var_on_stack(var_to_memory_location, var);
  if (loc) {
    return loc;
  }

  // TODO: global mem.

  return nullptr;
}

static void amd64_memory_location_empty_register(
    VarToMemoryLocationDyn *var_to_memory_location, Register reg) {
  VarToMemoryLocation *var_mem_loc =
      amd64_memory_location_find_register(*var_to_memory_location, reg);
  if (var_mem_loc) {
    u64 idx = (u64)(var_mem_loc - var_to_memory_location->data);
    PG_DYN_SWAP_REMOVE(var_to_memory_location, idx);
  }
}

[[nodiscard]]
static Amd64Operand amd64_memory_location_to_operand(MemoryLocation mem_loc) {
  Amd64Operand operand = {0};

  if (MEMORY_LOCATION_KIND_REGISTER == mem_loc.kind) {
    operand.kind = AMD64_OPERAND_KIND_REGISTER;
    operand.reg = mem_loc.reg;
  } else if (MEMORY_LOCATION_KIND_STACK == mem_loc.kind) {
    operand.kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS;
    operand.effective_address.base = amd64_rbp;
    operand.effective_address.displacement = (i32)mem_loc.base_pointer_offset;
  } else {
    PG_ASSERT(0);
  }

  return operand;
}

[[nodiscard]]
static MemoryLocation amd64_operand_to_memory_location(Amd64Operand operand) {
  MemoryLocation mem_loc = {0};

  if (AMD64_OPERAND_KIND_REGISTER == operand.kind) {
    mem_loc.kind = MEMORY_LOCATION_KIND_REGISTER;
    mem_loc.reg = operand.reg;
  } else if (AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == operand.kind &&
             operand.reg.value == amd64_rbp.value) {
    mem_loc.kind = MEMORY_LOCATION_KIND_STACK;
    mem_loc.base_pointer_offset = operand.effective_address.displacement;
  } else {
    PG_ASSERT(0);
  }

  return mem_loc;
}

[[nodiscard]] static Register
amd64_get_free_register(Amd64RegisterAllocator *reg_alloc) {
  Register amd64_all_grp_registers[] = {
      amd64_rax, amd64_rbx, amd64_rcx, amd64_rdx, amd64_rdi,
      amd64_rsi, amd64_r8,  amd64_r9,  amd64_r10, amd64_r11,
      amd64_r12, amd64_r13, amd64_r14, amd64_r15,
  };

  RegisterSlice amd64_all_grp_registers_slice = {
      .data = (Register *)amd64_all_grp_registers,
      .len = PG_STATIC_ARRAY_LEN(amd64_all_grp_registers),
  };

  for (u64 i = 0; i < amd64_all_grp_registers_slice.len;) {
    Register reg = PG_SLICE_AT(amd64_all_grp_registers_slice, i);
    if (amd64_memory_location_find_register(reg_alloc->var_to_memory_location,
                                            reg)) {
      PG_DYN_SWAP_REMOVE(&amd64_all_grp_registers_slice, i);
      continue;
    }
    i++;
  }

  return amd64_all_grp_registers_slice.len > 0
             ? PG_SLICE_AT(amd64_all_grp_registers_slice, 0)
             : (Register){0};
}

static i32 amd64_stack_alloc(Amd64RegisterAllocator *reg_alloc, u32 size) {
  reg_alloc->rbp_offset += size;
  reg_alloc->rbp_max_offset =
      PG_MAX(reg_alloc->rbp_max_offset, reg_alloc->rbp_offset);

  return -(i32)reg_alloc->rbp_offset;
}

static MemoryLocation
amd64_store_var_on_stack(Amd64RegisterAllocator *reg_alloc, u32 size, IrVar var,
                         MemoryLocation location_src,
                         Amd64InstructionDyn *instructions,
                         PgAllocator *allocator) {
  MemoryLocation *mem_loc = amd64_memory_location_find_var_on_stack(
      reg_alloc->var_to_memory_location, var);

  // No-op.
  if (mem_loc) {
    return *mem_loc;
  }

  i32 rbp_offset = amd64_stack_alloc(reg_alloc, size);

  MemoryLocation mem_loc_stack = {
      .kind = MEMORY_LOCATION_KIND_STACK,
      .base_pointer_offset = rbp_offset,
  };
  amd64_memory_location_add(&reg_alloc->var_to_memory_location, var,
                            mem_loc_stack, allocator);

  Amd64Instruction instruction = {
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .origin = {.synthetic = true},
      .lhs = amd64_memory_location_to_operand(mem_loc_stack),
      .rhs = amd64_memory_location_to_operand(location_src),
  };
  instruction.var_to_memory_location_frozen =
      amd64_memory_location_clone(reg_alloc->var_to_memory_location, allocator);

  *PG_DYN_PUSH(instructions, allocator) = instruction;

  amd64_memory_location_record_var_copy(&reg_alloc->var_to_memory_location, var,
                                        mem_loc_stack, allocator);

  return mem_loc_stack;
}

[[nodiscard]]
static Register amd64_create_register_for_var(Amd64RegisterAllocator *reg_alloc,
                                              IrVar var, u32 size,
                                              Amd64InstructionDyn *instructions,
                                              PgAllocator *allocator) {
  // Easy path: a register is free.
  Register reg_free = amd64_get_free_register(reg_alloc);
  if (reg_free.value) {
    return reg_free;
  }

  // Need to first free a register by spilling it to the stack.

  Register reg = amd64_r11; // TODO: Improve.
  VarToMemoryLocation *var_mem_loc_old = amd64_memory_location_find_register(
      reg_alloc->var_to_memory_location, reg);
  PG_ASSERT(var_mem_loc_old);
  PG_ASSERT(var_mem_loc_old->locations.len > 0);

  MemoryLocation *mem_loc_old = nullptr;
  for (u64 i = 0; i < var_mem_loc_old->locations.len; i++) {
    MemoryLocation *it = PG_SLICE_AT_PTR(&var_mem_loc_old->locations, i);
    if (MEMORY_LOCATION_KIND_REGISTER == it->kind &&
        it->reg.value == reg.value) {
      mem_loc_old = it;
      break;
    }
  }
  PG_ASSERT(mem_loc_old);

  (void)amd64_store_var_on_stack(reg_alloc, size, var, *mem_loc_old,
                                 instructions, allocator);

  return reg;
}

[[nodiscard]]
static Register amd64_find_or_create_register_for_var(
    Amd64RegisterAllocator *reg_alloc, IrVar var, u32 size,
    Amd64InstructionDyn *instructions, PgAllocator *allocator) {
  MemoryLocationDyn *mem_locs =
      amd64_memory_location_find_var(reg_alloc->var_to_memory_location, var);
  PG_ASSERT(mem_locs);

  for (u64 i = 0; i < mem_locs->len; i++) {
    MemoryLocation *it = PG_SLICE_AT_PTR(mem_locs, i);
    // Easy path: var already in register.
    if (MEMORY_LOCATION_KIND_REGISTER == it->kind) {
      return it->reg;
    }
  }

  return amd64_create_register_for_var(reg_alloc, var, size, instructions,
                                       allocator);
}

[[nodiscard]]
static MemoryLocation
amd64_make_any_memory_location_for_var(Amd64RegisterAllocator *reg_alloc,
                                       IrVar var) {
  // Register.
  Register reg_free = amd64_get_free_register(reg_alloc);
  if (reg_free.value) {
    MemoryLocation mem_loc = {
        .kind = MEMORY_LOCATION_KIND_REGISTER,
        .reg = reg_free,
    };
    return mem_loc;
  }

  // Stack.
  MemoryLocation *mem_loc_stack = amd64_memory_location_find_var_on_stack(
      reg_alloc->var_to_memory_location, var);
  // No-op.
  if (mem_loc_stack) {
    return *mem_loc_stack;
  }

  i32 stack_offset = amd64_stack_alloc(reg_alloc, 8);
  MemoryLocation mem_loc = {
      .kind = MEMORY_LOCATION_KIND_STACK,
      .base_pointer_offset = stack_offset,
  };
  return mem_loc;
}

static void amd64_store_immediate_into_register(
    Amd64RegisterAllocator *reg_alloc, Register dst, u64 val, Origin origin,
    Amd64InstructionDyn *instructions, PgAllocator *allocator) {
  VarToMemoryLocation *var_to_mem_loc_by_reg =
      amd64_memory_location_find_register(reg_alloc->var_to_memory_location,
                                          dst);

  if (var_to_mem_loc_by_reg) { // Target register is occupied by a different
                               // variable.
    // Move things around to free the target register.

    MemoryLocation mem_loc = amd64_make_any_memory_location_for_var(
        reg_alloc, var_to_mem_loc_by_reg->var);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .lhs = amd64_memory_location_to_operand(mem_loc),
        .rhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = dst,
            },
        .origin = {.synthetic = true},
    };

    amd64_memory_location_record_var_copy(&reg_alloc->var_to_memory_location,
                                          var_to_mem_loc_by_reg->var, mem_loc,
                                          allocator);
    instruction.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = instruction;
  }

  Amd64Instruction instruction = {
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = dst,
          },
      .rhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_IMMEDIATE,
              .immediate = val,
          },
      .origin = origin,
  };
  // TODO: Should we remember what immediate is in the register?
  instruction.var_to_memory_location_frozen =
      amd64_memory_location_clone(reg_alloc->var_to_memory_location, allocator);
  *PG_DYN_PUSH(instructions, allocator) = instruction;

  amd64_memory_location_empty_register(&reg_alloc->var_to_memory_location, dst);
}

static void amd64_store_var_into_register(Amd64RegisterAllocator *reg_alloc,
                                          Register dst, IrValue val,
                                          Origin origin,
                                          Amd64InstructionDyn *instructions,
                                          PgAllocator *allocator) {

  PG_ASSERT(IR_VALUE_KIND_VAR == val.kind);
  VarToMemoryLocation *var_to_mem_loc = amd64_memory_location_find_register(
      reg_alloc->var_to_memory_location, dst);

  // Nothing to do, the var is already located in the right register.
  if (var_to_mem_loc && var_to_mem_loc->var.id.value == val.var.id.value) {
    return;
  }

  if (var_to_mem_loc) { // Target register is occupied by a different
                        // variable.
    // Move things around to free the target register.
    MemoryLocation mem_loc =
        amd64_make_any_memory_location_for_var(reg_alloc, var_to_mem_loc->var);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .lhs = amd64_memory_location_to_operand(mem_loc),
        .rhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = dst,
            },
        .origin = {.synthetic = true},
    };

    amd64_memory_location_record_var_copy(&reg_alloc->var_to_memory_location,
                                          var_to_mem_loc->var, mem_loc,
                                          allocator);

    instruction.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = instruction;
  }

  Amd64Instruction instruction = {
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = dst,
          },
      .rhs =
          amd64_memory_location_to_operand(*amd64_memory_location_find_var_best(
              reg_alloc->var_to_memory_location, val.var)),
      .origin = origin,
  };
  // Finally the var is in the `dst` register.
  MemoryLocation mem_loc = {.kind = MEMORY_LOCATION_KIND_REGISTER, .reg = dst};
  if (IR_VALUE_KIND_VAR == val.kind) {
    amd64_memory_location_record_var_copy(&reg_alloc->var_to_memory_location,
                                          val.var, mem_loc, allocator);
  }
  instruction.var_to_memory_location_frozen =
      amd64_memory_location_clone(reg_alloc->var_to_memory_location, allocator);
  *PG_DYN_PUSH(instructions, allocator) = instruction;
}

// Convert:
// `<op> [rbp+8], [rbp+16]`
// to (TODO) `mov rax, [rbp+8]; <op> rax, [rbp+16]`.
// or `mov rax, [rbp+16]; <op> [rbp+16], rax`.
static void
amd64_insert_mem_to_register_load_if_both_operands_are_effective_address(
    Amd64InstructionDyn *instructions, Amd64Operand *lhs, Amd64Operand *rhs,
    IrValue rhs_val, Amd64RegisterAllocator *reg_alloc,
    PgAllocator *allocator) {
  if (!(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == lhs->kind &&
        AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == rhs->kind)) {
    // No-op.
    return;
  }

  PG_ASSERT(IR_VALUE_KIND_VAR == rhs_val.kind);

  // TODO: lhs.
  IrVar var = rhs_val.var;

  Register reg = amd64_find_or_create_register_for_var(
      reg_alloc, var, sizeof(u64), instructions, allocator);
  PG_ASSERT(0 != reg.value);

  amd64_store_var_into_register(reg_alloc, reg, rhs_val,
                                (Origin){.synthetic = true}, instructions,
                                allocator);

  *rhs = (Amd64Operand){
      .kind = AMD64_OPERAND_KIND_REGISTER,
      .reg = reg,
  };
}

// For now only expire registers.
// TODO: expire stack slots.
static void
amd64_expire_vars_if_lifetime_end_reached(Amd64RegisterAllocator *reg_alloc,
                                          IrVarLifetimeDyn var_lifetimes,
                                          IrId ir_id) {
  for (u64 i = 0; i < reg_alloc->var_to_memory_location.len; i++) {
    VarToMemoryLocation var_mem_loc =
        PG_SLICE_AT(reg_alloc->var_to_memory_location, i);

    for (u64 j = 0; j < var_mem_loc.locations.len; j++) {
      MemoryLocation mem_loc = PG_SLICE_AT(var_mem_loc.locations, j);
      if (MEMORY_LOCATION_KIND_REGISTER != mem_loc.kind) {
        continue;
      }

      IrVarLifetime *lifetime =
          ir_find_var_lifetime_by_var_id(var_lifetimes, var_mem_loc.var.id);
      PG_ASSERT(lifetime);

      // TODO: Expire stack slots.
      if (ir_id.value > lifetime->end.value &&
          MEMORY_LOCATION_KIND_REGISTER == mem_loc.kind) {
        amd64_memory_location_empty_register(&reg_alloc->var_to_memory_location,
                                             mem_loc.reg);

        printf("[D001] [%u] expire: ", ir_id.value);
        amd64_print_register(mem_loc.reg);
        printf(" ");
        ir_print_var(var_mem_loc.var);
        printf("\n");
      }
    }
  }
}

static void amd64_ir_to_asm(Ir ir, Amd64InstructionDyn *instructions,
                            Amd64RegisterAllocator *reg_alloc,
                            IrVarLifetimeDyn var_lifetimes,
                            PgAllocator *allocator) {
  amd64_expire_vars_if_lifetime_end_reached(reg_alloc, var_lifetimes, ir.id);
  if (ir.tombstone) {
    return;
  }

  switch (ir.kind) {
  case IR_KIND_NONE:
    PG_ASSERT(0);
  case IR_KIND_ADD: {
    PG_ASSERT(2 == ir.operands.len);
    PG_ASSERT(ir.var.id.value);
    IrValue val_lhs = PG_SLICE_AT(ir.operands, 0);
    IrValue val_rhs = PG_SLICE_AT(ir.operands, 1);
    PG_ASSERT(IR_VALUE_KIND_VAR == val_lhs.kind);
    PG_ASSERT(IR_VALUE_KIND_VAR == val_rhs.kind ||
              IR_VALUE_KIND_U64 == val_rhs.kind);

    Amd64Operand op_lhs =
        amd64_memory_location_to_operand(*amd64_memory_location_find_var_best(
            reg_alloc->var_to_memory_location, val_lhs.var));

    Amd64Operand op_rhs =
        amd64_memory_location_to_operand(*amd64_memory_location_find_var_best(
            reg_alloc->var_to_memory_location, val_rhs.var));

    amd64_insert_mem_to_register_load_if_both_operands_are_effective_address(
        instructions, &op_lhs, &op_rhs, val_rhs, reg_alloc, allocator);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_ADD,
        .rhs = op_rhs,
        .lhs = op_lhs,
        .origin = ir.origin,
    };

    MemoryLocation mem_loc = amd64_operand_to_memory_location(instruction.lhs);
    amd64_memory_location_add(&reg_alloc->var_to_memory_location, ir.var,
                              mem_loc, allocator);
    instruction.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = instruction;

  } break;
  case IR_KIND_LOAD: {
    PG_ASSERT(1 == ir.operands.len);
    PG_ASSERT(ir.var.id.value);

    IrValue src = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == src.kind || IR_VALUE_KIND_U64 == src.kind);
    Amd64Operand op_rhs = {0};
    if (IR_VALUE_KIND_U64 == src.kind) {
      op_rhs.kind = AMD64_OPERAND_KIND_IMMEDIATE;
      op_rhs.immediate = src.n64;
    } else if (IR_VALUE_KIND_VAR == src.kind) {
      MemoryLocation *loc_src = amd64_memory_location_find_var_best(
          reg_alloc->var_to_memory_location, src.var);
      PG_ASSERT(loc_src);
      op_rhs = amd64_memory_location_to_operand(*loc_src);
    }

    Amd64InstructionKind kind = AMD64_INSTRUCTION_KIND_MOV;

    // TODO: Could be any mem location.
    Register reg_dst = amd64_create_register_for_var(
        reg_alloc, ir.var, sizeof(u64), instructions, allocator);
    MemoryLocation mem_loc = {
        .kind = MEMORY_LOCATION_KIND_REGISTER,
        .reg = reg_dst,
    };

    Amd64Instruction instruction = {
        .kind = kind,
        .lhs = amd64_memory_location_to_operand(mem_loc),
        .rhs = op_rhs,
        .origin = ir.origin,
    };
    instruction.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);
    *PG_DYN_PUSH(instructions, allocator) = instruction;

    // TODO: add mem loc.

  } break;
  case IR_KIND_SYSCALL: {
    PG_ASSERT(ir.operands.len > 0);
    PG_ASSERT(ir.operands.len <= amd64_arch.syscall_calling_convention.len);

    // Save the first operand on the stack before the syscall since the
    // syscall will override `rax` with the return value and thus we might
    // lose the first operand. Only necessary if the variable gets used
    // afterwards.
    IrValue op0 = PG_SLICE_AT(ir.operands, 0);
    bool need_rax_saved = false;
    if (IR_VALUE_KIND_VAR == op0.kind) {
      IrVarLifetime *res_var_lifetime =
          ir_find_var_lifetime_by_var_id(var_lifetimes, op0.var.id);

      need_rax_saved =
          res_var_lifetime && res_var_lifetime->end.value > ir.id.value;
    }

    for (u64 j = 0; j < ir.operands.len; j++) {
      IrValue val = PG_SLICE_AT(ir.operands, j);
      Register dst = PG_SLICE_AT(amd64_arch.syscall_calling_convention, j);
      if (IR_VALUE_KIND_VAR == val.kind) {
        amd64_store_var_into_register(reg_alloc, dst, val, ir.origin,
                                      instructions, allocator);

        if (need_rax_saved && j == 0) {
          MemoryLocation rax_loc = {
              .kind = MEMORY_LOCATION_KIND_REGISTER,
              .reg = amd64_rax,
          };
          amd64_store_var_on_stack(reg_alloc, sizeof(u64), op0.var, rax_loc,
                                   instructions, allocator);
        }
      } else if (IR_VALUE_KIND_U64 == val.kind) {
        amd64_store_immediate_into_register(reg_alloc, dst, val.n64, ir.origin,
                                            instructions, allocator);
      } else {
        PG_ASSERT(0);
      }
    }

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
        .origin = ir.origin,
    };

    // Syscall result used?
    bool syscall_res_used = ir.var.id.value != 0;
    if (syscall_res_used) {
      MemoryLocation mem_loc = {
          .kind = MEMORY_LOCATION_KIND_REGISTER,
          .reg = amd64_arch.return_value,
      };
      amd64_memory_location_add(&reg_alloc->var_to_memory_location, ir.var,
                                mem_loc, allocator);
    } else {
      amd64_memory_location_empty_register(&reg_alloc->var_to_memory_location,
                                           amd64_rax);
    }

    instruction.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);
    *PG_DYN_PUSH(instructions, allocator) = instruction;

  } break;

  case IR_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir.operands.len);
    IrValue rhs = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == rhs.kind);

    MemoryLocation *loc_rhs = amd64_memory_location_find_var_in_register_any(
        reg_alloc->var_to_memory_location, rhs.var);
    if (loc_rhs) {
      amd64_store_var_on_stack(reg_alloc, sizeof(u64), rhs.var, *loc_rhs,
                               instructions, allocator);
    }
    loc_rhs = amd64_memory_location_find_var_on_stack(
        reg_alloc->var_to_memory_location, rhs.var);
    PG_ASSERT(loc_rhs);

    MemoryLocation mem_loc =
        amd64_make_any_memory_location_for_var(reg_alloc, ir.var);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_LEA,
        .origin = ir.origin,
        .lhs = amd64_memory_location_to_operand(mem_loc),
        .rhs = amd64_memory_location_to_operand(*loc_rhs),
    };
    instruction.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = instruction;

    amd64_memory_location_add(&reg_alloc->var_to_memory_location, ir.var,
                              mem_loc, allocator);

  } break;

  case IR_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ir.operands.len);
    IrValue cond = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == cond.kind);
    IrValue branch_else = PG_SLICE_AT(ir.operands, 1);
    PG_ASSERT(IR_VALUE_KIND_LABEL == branch_else.kind);

    MemoryLocation *cond_mem_loc = amd64_memory_location_find_var_best(
        reg_alloc->var_to_memory_location, cond.var);
    PG_ASSERT(cond_mem_loc);

    Amd64Instruction instruction_cmp = {
        .kind = AMD64_INSTRUCTION_KIND_CMP,
        .origin = ir.origin,
        .lhs = amd64_memory_location_to_operand(*cond_mem_loc),
        .rhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                .immediate = 0,
            },
    };
    instruction_cmp.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);
    *PG_DYN_PUSH(instructions, allocator) = instruction_cmp;

    Amd64Instruction instruction_je = {
        .kind = AMD64_INSTRUCTION_KIND_JMP_IF_EQ,
        .origin = ir.origin,
        .lhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_LABEL,
                .label = branch_else.label,
            },
    };
    instruction_je.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);
    *PG_DYN_PUSH(instructions, allocator) = instruction_je;

  } break;

  case IR_KIND_LABEL: {
    PG_ASSERT(1 == ir.operands.len);
    IrValue operand = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_LABEL == operand.kind);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_LABEL,
        .origin = ir.origin,
        .lhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_LABEL,
                .label = operand.label,
            },
    };
    instruction.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = instruction;
  } break;

  case IR_KIND_JUMP: {
    PG_ASSERT(1 == ir.operands.len);
    IrValue label = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_LABEL == label.kind);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_JMP,
        .origin = ir.origin,
        .lhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_LABEL,
                .label = label.label,
            },
    };
    instruction.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = instruction;

  } break;

  default:
    PG_ASSERT(0);
  }
}

static void amd64_irs_to_asm(IrSlice irs, Amd64InstructionDyn *instructions,
                             Amd64RegisterAllocator *reg_alloc,
                             IrVarLifetimeDyn var_lifetimes,
                             PgAllocator *allocator) {
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
      .origin.synthetic = true,
  };
  *PG_DYN_PUSH(instructions, allocator) = stack_sub;
  u64 stack_sub_instruction_idx = instructions->len - 1;

  for (u64 i = 0; i < irs.len; i++) {
    amd64_ir_to_asm(PG_SLICE_AT(irs, i), instructions, reg_alloc, var_lifetimes,
                    allocator);
  }

  if (reg_alloc->rbp_max_offset > 0) {
    u32 rsp_max_offset_aligned_16 =
        (u32)PG_ROUNDUP(reg_alloc->rbp_max_offset, 16);

    PG_SLICE_AT_PTR(instructions, stack_sub_instruction_idx)->rhs.immediate =
        rsp_max_offset_aligned_16;

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
        .origin.synthetic = true,
    };
    stack_add.var_to_memory_location_frozen = amd64_memory_location_clone(
        reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = stack_add;
  } else {
    PG_DYN_REMOVE_AT(instructions, stack_sub_instruction_idx);
  }
}
