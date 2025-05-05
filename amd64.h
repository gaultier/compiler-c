#pragma once
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
    IrLabelId label;
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
} Amd64InstructionKind;

typedef struct {
  Amd64InstructionKind kind;
  Amd64Operand lhs, rhs;
  Origin origin;
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
#if 0
  VarToMemoryLocationDyn var_to_memory_location;
#endif
  u32 rbp_offset;
  u32 rbp_max_offset;
  Amd64InstructionDyn instructions;
  InterferenceGraph interference_graph;
  LirEmitter *lir_emitter;
} Amd64Emitter;

static void amd64_print_register(Register reg) {
  PgString s = PG_SLICE_AT(amd64_register_to_string_slice, reg.value);
  printf("%.*s", (i32)s.len, s.data);
}

// TODO: If any of the callee-saved registers were used by the register
// allocator, emit storing code (push).
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

// TODO: If any of the callee-saved registers were used by the register
// allocator, emit loading code (pop).
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
  *PG_DYN_PUSH(instructions, allocator) = (Amd64Instruction){
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .origin = {.synthetic = true},
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rax,
          },
      .rhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_IMMEDIATE,
              .immediate = 60, // Linux x86_64 exit.
          },
  };
  *PG_DYN_PUSH(instructions, allocator) = (Amd64Instruction){
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .origin = {.synthetic = true},
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = amd64_rdi,
          },
      .rhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_IMMEDIATE,
              .immediate = 0, // Exit code.
          },
  };
  *PG_DYN_PUSH(instructions, allocator) = (Amd64Instruction){
      .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
      .origin = {.synthetic = true},
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
    printf(".%" PRIu32, operand.label.value);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void amd64_print_memory_locations(MemoryLocationDyn memory_locations,
                                         VirtualRegisterDyn virtual_registers) {
  for (u64 i = 0; i < memory_locations.len; i++) {
    MemoryLocation mem_loc = PG_SLICE_AT(memory_locations, i);
    printf("var=");
    ir_print_var(mem_loc.var);
    printf(" virt_reg=");
    lir_print_virtual_register(mem_loc.virt_reg_idx, virtual_registers);
    printf(" node_idx=%u ", mem_loc.node_idx.value);
    printf(" mem_loc=");

    switch (mem_loc.kind) {
    case MEMORY_LOCATION_KIND_REGISTER:
      amd64_print_register(mem_loc.reg);
      break;
    case MEMORY_LOCATION_KIND_STACK: {
      printf("[");
      amd64_print_register(amd64_rbp);
      i32 offset = mem_loc.base_pointer_offset;
      printf("-%" PRIi32 "]", offset);
    } break;
#if 0
    case MEMORY_LOCATION_KIND_MEMORY:
      printf("%#lx", loc.memory_address);
      break;
#endif
    case MEMORY_LOCATION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }

    printf("\n");
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

[[nodiscard]] static Amd64Operand
amd64_convert_lir_operand_to_amd64_operand(Amd64Emitter *emitter,
                                           LirOperand lir_op) {
  (void)emitter;

  switch (lir_op.kind) {
  case LIR_OPERAND_KIND_VIRTUAL_REGISTER: {
    MemoryLocationIndex mem_loc_idx =
        memory_locations_find_by_virtual_register_index(
            emitter->interference_graph.memory_locations, lir_op.virt_reg_idx);
    PG_ASSERT(-1U != mem_loc_idx.value);

    MemoryLocation mem_loc = PG_SLICE_AT(
        emitter->interference_graph.memory_locations, mem_loc_idx.value);
    switch (mem_loc.kind) {
    case MEMORY_LOCATION_KIND_REGISTER: {
      PG_ASSERT(MEMORY_LOCATION_KIND_REGISTER == mem_loc.kind);
      PG_ASSERT(mem_loc.reg.value);

      return (Amd64Operand){
          .kind = AMD64_OPERAND_KIND_REGISTER,
          .reg = mem_loc.reg,
      };
    }
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
  case LIR_OPERAND_KIND_LABEL:
    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_LABEL,
        .label = lir_op.label,
    };
  case LIR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void
amd64_sanity_check_instructions(Amd64InstructionSlice instructions) {
  for (u64 i = 0; i < instructions.len; i++) {
    Amd64Instruction ins = PG_SLICE_AT(instructions, i);

    // Prohibited by amd64 rules.
    PG_ASSERT(!(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.lhs.kind &&
                AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.rhs.kind));

    PG_ASSERT(!(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.lhs.kind &&
                AMD64_OPERAND_KIND_IMMEDIATE == ins.rhs.kind));

    PG_ASSERT(!(AMD64_OPERAND_KIND_IMMEDIATE == ins.lhs.kind &&
                AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == ins.rhs.kind));
  }
}

static void amd64_lir_to_asm(Amd64Emitter *emitter, LirInstruction lir,
                             PgAllocator *allocator) {
  switch (lir.kind) {
  case LIR_INSTRUCTION_KIND_ADD: {
    PG_ASSERT(2 == lir.operands.len);
    LirOperand lhs = PG_SLICE_AT(lir.operands, 0);
    LirOperand rhs = PG_SLICE_AT(lir.operands, 1);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_ADD,
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
        .origin = lir.origin,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = instruction;

  } break;
  case LIR_INSTRUCTION_KIND_SUB: {
    PG_ASSERT(2 == lir.operands.len);
    LirOperand lhs = PG_SLICE_AT(lir.operands, 0);
    LirOperand rhs = PG_SLICE_AT(lir.operands, 1);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_SUB,
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
        .origin = lir.origin,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = instruction;

  } break;
  case LIR_INSTRUCTION_KIND_MOV: {
    PG_ASSERT(2 == lir.operands.len);

    LirOperand lhs = PG_SLICE_AT(lir.operands, 0);
    LirOperand rhs = PG_SLICE_AT(lir.operands, 1);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
        .origin = lir.origin,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = instruction;

  } break;
#if 0
  case LIR_INSTRUCTION_KIND_SYSCALL: {
    PG_ASSERT(0 == lir.operands.len);
    Amd64Instruction ins = {
        .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
        .origin = lir.origin,
    };
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
  } break;
#endif

  case LIR_INSTRUCTION_KIND_JUMP_IF_EQ: {
    PG_ASSERT(1 == lir.operands.len);

    LirOperand label = PG_SLICE_AT(lir.operands, 0);
    PG_ASSERT(LIR_OPERAND_KIND_LABEL == label.kind);
    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_JMP_IF_EQ,
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, label),
        .origin = lir.origin,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = instruction;

  } break;

  case LIR_INSTRUCTION_KIND_LABEL: {
    PG_ASSERT(1 == lir.operands.len);

    LirOperand label = PG_SLICE_AT(lir.operands, 0);
    PG_ASSERT(LIR_OPERAND_KIND_LABEL == label.kind);
    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_LABEL,
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, label),
        .origin = lir.origin,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = instruction;
  } break;

  case LIR_INSTRUCTION_KIND_JUMP: {
    PG_ASSERT(1 == lir.operands.len);

    LirOperand label = PG_SLICE_AT(lir.operands, 0);
    PG_ASSERT(LIR_OPERAND_KIND_LABEL == label.kind);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_JMP,
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, label),
        .origin = lir.origin,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = instruction;
  } break;

  case LIR_INSTRUCTION_KIND_CMP: {
    PG_ASSERT(2 == lir.operands.len);

    LirOperand lhs = PG_SLICE_AT(lir.operands, 0);
    LirOperand rhs = PG_SLICE_AT(lir.operands, 1);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_CMP,
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
        .origin = lir.origin,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = instruction;
  } break;

  case LIR_INSTRUCTION_KIND_LOAD_FROM_MEMORY: {
    PG_ASSERT(2 == lir.operands.len);

    LirOperand lhs = PG_SLICE_AT(lir.operands, 0);
    LirOperand rhs = PG_SLICE_AT(lir.operands, 1);

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_LEA,
        .rhs = amd64_convert_lir_operand_to_amd64_operand(emitter, rhs),
        .lhs = amd64_convert_lir_operand_to_amd64_operand(emitter, lhs),
        .origin = lir.origin,
    };
    PG_ASSERT(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.rhs.kind);
    *PG_DYN_PUSH(&emitter->instructions, allocator) = instruction;

  } break;

  case LIR_INSTRUCTION_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static Register
amd64_get_free_register(GprSet regs, LirVirtualRegisterConstraint constraint) {
  switch (constraint) {
  case LIR_VIRT_REG_CONSTRAINT_NONE: {
    // TODO: Smarter free register selection.
    // E.g. favor caller-saved registers, etc.
    Register res = lir_gpr_pop_first_unset(&regs);
    PG_ASSERT(res.value && "todo: spill");
    return res;
  }
#if 0
  case LIR_VIRT_REG_CONSTRAINT_BASE_POINTER: {
    return amd64_arch.base_pointer;
  }
#endif
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static Register
amd64_color_assign_register(InterferenceGraph *graph,
                            InterferenceNodeIndex node_idx,
                            LirVirtualRegisterConstraint constraint) {
  GprSet neighbor_colors = {
      .len = amd64_register_allocator_gprs_slice.len,
      .set = 0,
  };

  PgAdjacencyMatrixNeighborIterator it =
      pg_adjacency_matrix_make_neighbor_iterator(graph->matrix, node_idx.value);

  PgAdjacencyMatrixNeighbor neighbor = {0};
  do {
    neighbor = pg_adjacency_matrix_neighbor_iterator_next(&it);
    MemoryLocationIndex neighbor_mem_loc_idx =
        memory_locations_find_by_node_index(
            graph->memory_locations,
            (InterferenceNodeIndex){(u32)neighbor.col});
    PG_ASSERT(-1U != neighbor_mem_loc_idx.value);

    // If a neighbor already has an assigned register, add it to the set.
    {
      MemoryLocation neighbor_mem_loc =
          PG_SLICE_AT(graph->memory_locations, neighbor_mem_loc_idx.value);
      if (MEMORY_LOCATION_KIND_REGISTER == neighbor_mem_loc.kind) {
        PG_ASSERT(neighbor_mem_loc.reg.value);
        PG_ASSERT(neighbor_mem_loc.reg.value <=
                  PG_SLICE_LAST(amd64_register_allocator_gprs_slice).value);
        lir_gpr_set_add(&neighbor_colors, neighbor_mem_loc.reg.value - 1);
      }
    }
  } while (neighbor.has_value);

  Register res = amd64_get_free_register(neighbor_colors, constraint);
  PG_ASSERT(res.value);

  // Update memory location.

  MemoryLocationIndex mem_loc_idx =
      memory_locations_find_by_node_index(graph->memory_locations, node_idx);
  PG_ASSERT(-1U != mem_loc_idx.value);
  {
    MemoryLocation *mem_loc =
        PG_SLICE_AT_PTR(&graph->memory_locations, mem_loc_idx.value);
    PG_ASSERT(MEMORY_LOCATION_KIND_NONE == mem_loc->kind);

    mem_loc->kind = MEMORY_LOCATION_KIND_REGISTER;
    mem_loc->reg = res;
  }
  return res;
}

[[maybe_unused]] [[nodiscard]]
static u32 amd64_reserve_stack_slot(Amd64Emitter *emitter, u32 slot_size) {
  emitter->rbp_offset += slot_size;
  emitter->rbp_max_offset =
      PG_MAX(emitter->rbp_max_offset, emitter->rbp_offset);

  PG_ASSERT(emitter->rbp_offset > 0);
  return emitter->rbp_offset;
}

// TODO: Better strategy to pick which virtual registers to spill.
// For now we simply spill them all if they have more neighbors than there are
// GPRs, on a 'first encounter' basis.
static void amd64_color_spill_remaining_nodes_in_graph(
    Amd64Emitter *emitter, InterferenceNodeIndexDyn *stack,
    PgString nodes_tombstones_bitfield, PgAllocator *allocator) {
  PG_ASSERT(!pg_adjacency_matrix_is_empty(emitter->interference_graph.matrix));

  for (u64 row = 0; row < emitter->interference_graph.matrix.nodes_count;) {
    if (pg_bitfield_get(nodes_tombstones_bitfield, row)) {
      row++;
      continue;
    }

    u64 neighbors_count = pg_adjacency_matrix_count_neighbors(
        emitter->interference_graph.matrix, row);

    pg_adjacency_matrix_remove_node(&emitter->interference_graph.matrix, row);
    pg_bitfield_set(nodes_tombstones_bitfield, row, true);

    InterferenceNodeIndex node_idx = {(u32)row};
    if (neighbors_count < amd64_register_allocator_gprs_slice.len) {
      PG_ASSERT(stack->len < emitter->interference_graph.matrix.nodes_count);
      *PG_DYN_PUSH_WITHIN_CAPACITY(stack) = node_idx;
      continue;
    }

    // Need to spill.
    u32 rbp_offset = amd64_reserve_stack_slot(emitter, sizeof(u64) /*FIXME*/);

    MemoryLocationIndex mem_loc_idx = memory_locations_find_by_node_index(
        emitter->interference_graph.memory_locations, node_idx);
    PG_ASSERT(-1U != mem_loc_idx.value);
    {
      MemoryLocation *mem_loc = PG_SLICE_AT_PTR(
          &emitter->interference_graph.memory_locations, mem_loc_idx.value);
      mem_loc->kind = MEMORY_LOCATION_KIND_STACK;
      mem_loc->base_pointer_offset = (i32)rbp_offset;
    }

    Amd64Instruction ins_load = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .origin = {.synthetic = true},
        .lhs =
            {
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = amd64_spill_registers[0], // TODO: mark it as used?
            },
        .rhs =
            {
                // FIXME
                .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                .immediate = 99,
            },
    };

    Amd64Instruction ins_store = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .origin = {.synthetic = true},
        .lhs =
            {
                .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
                .effective_address =
                    {
                        .base = amd64_rbp,
                        .displacement = -(i32)rbp_offset,
                    },
            },
        .rhs = ins_load.lhs,
    };

    // FIXME: Should not be 'push' (at the end) but somwhere in the middle.
    // FIXME: The original LIR should be removed.
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins_load;
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins_store;

    row++;
  }
}

// Assign a color (i.e. unique physical register) to each node in the graph
// so that no two adjacent nodes have the same color.
// Meaning that if two variables interfere, they are assigned a different
// physical register.

static void amd64_color_interference_graph(Amd64Emitter *emitter,
                                           PgAllocator *allocator) {
  if (0 == emitter->interference_graph.matrix.nodes_count) {
    return;
  }

  InterferenceNodeIndexDyn stack = {0};
  PG_DYN_ENSURE_CAP(&stack, emitter->interference_graph.matrix.nodes_count,
                    allocator);

  PgString nodes_tombstones_bitfield = pg_string_make(
      pg_div_ceil(emitter->interference_graph.matrix.nodes_count, 8),
      allocator);

  PgAdjacencyMatrix graph_clone =
      pg_adjacency_matrix_clone(emitter->interference_graph.matrix, allocator);

  for (u64 row = 0; row < emitter->interference_graph.matrix.nodes_count;
       row++) {
    u64 neighbors_count = pg_adjacency_matrix_count_neighbors(
        emitter->interference_graph.matrix, row);

    // TODO: Addressable virtual registers must be spilled.
    if (neighbors_count < amd64_register_allocator_gprs_slice.len) {
      PG_ASSERT(stack.len < emitter->interference_graph.matrix.nodes_count);

      *PG_DYN_PUSH_WITHIN_CAPACITY(&stack) = (InterferenceNodeIndex){(u32)row};
      pg_adjacency_matrix_remove_node(&emitter->interference_graph.matrix, row);
      pg_bitfield_set(nodes_tombstones_bitfield, row, true);
    }
  }
  PG_ASSERT(stack.len <= emitter->interference_graph.matrix.nodes_count);

  if (!pg_adjacency_matrix_is_empty(emitter->interference_graph.matrix)) {
    printf("\n============\n");
    lir_print_interference_graph(emitter->interference_graph,
                                 emitter->lir_emitter->lifetimes);

    amd64_color_spill_remaining_nodes_in_graph(
        emitter, &stack, nodes_tombstones_bitfield, allocator);
  }

  u64 stack_len = stack.len;
  for (u64 _i = 0; _i < stack_len; _i++) {
    if (0 == stack.len) {
      break;
    }

    // Pop the first node from the stack.
    InterferenceNodeIndex node_idx = PG_SLICE_LAST(stack);
    stack.len -= 1;

    // Add the node back to the graph.
    {
      u64 row = node_idx.value;
      pg_bitfield_set(nodes_tombstones_bitfield, row, false);

      PgAdjacencyMatrixNeighborIterator it =
          pg_adjacency_matrix_make_neighbor_iterator(graph_clone,
                                                     node_idx.value);

      PgAdjacencyMatrixNeighbor neighbor = {0};
      do {
        neighbor = pg_adjacency_matrix_neighbor_iterator_next(&it);
        // The node was originally connected in the original graph to its
        // neighbor. When re-adding the node to the graph, we only connect it
        // to non-tombstoned neighbors.
        if (pg_bitfield_get(nodes_tombstones_bitfield, neighbor.col)) {
          continue;
        }

        pg_adjacency_matrix_add_edge(&emitter->interference_graph.matrix, row,
                                     neighbor.col);
      } while (neighbor.has_value);

      LirVirtualRegisterConstraint constraint =
          PG_SLICE_AT(emitter->lir_emitter->virtual_registers, node_idx.value)
              .constraint;

      Register reg = amd64_color_assign_register(&emitter->interference_graph,
                                                 node_idx, constraint);
      PG_ASSERT(reg.value);
    }
  }

  // Sanity check: if two nodes interferred (had an edge) in the original
  // graph, then their assigned registers MUST be different.
  for (u64 row = 0; row < graph_clone.nodes_count; row++) {
    PgAdjacencyMatrixNeighborIterator it =
        pg_adjacency_matrix_make_neighbor_iterator(graph_clone, row);

    PgAdjacencyMatrixNeighbor neighbor = {0};
    do {
      neighbor = pg_adjacency_matrix_neighbor_iterator_next(&it);

      InterferenceNodeIndex san_node_idx = {(u32)row};
      MemoryLocationIndex node_mem_loc_idx =
          memory_locations_find_by_node_index(
              emitter->interference_graph.memory_locations, san_node_idx);
      PG_ASSERT(-1U != node_mem_loc_idx.value);
      MemoryLocation node_mem_loc = PG_SLICE_AT(
          emitter->interference_graph.memory_locations, node_mem_loc_idx.value);

      InterferenceNodeIndex neighbor_idx = {(u32)neighbor.col};
      MemoryLocationIndex neighbor_mem_loc_idx =
          memory_locations_find_by_node_index(
              emitter->interference_graph.memory_locations, neighbor_idx);
      PG_ASSERT(-1U != neighbor_mem_loc_idx.value);
      MemoryLocation neighbor_mem_loc =
          PG_SLICE_AT(emitter->interference_graph.memory_locations,
                      neighbor_mem_loc_idx.value);

      if (MEMORY_LOCATION_KIND_REGISTER == node_mem_loc.kind &&
          MEMORY_LOCATION_KIND_REGISTER == neighbor_mem_loc.kind) {
        PG_ASSERT(node_mem_loc.reg.value != neighbor_mem_loc.reg.value);
      }

    } while (neighbor.has_value);
  }
}

[[nodiscard]]
static InterferenceNodeIndexSlice
amd64_emit_lirs_to_asm(Amd64Emitter *emitter, LirInstructionSlice lirs,
                       bool verbose, PgAllocator *allocator) {
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
  *PG_DYN_PUSH(&emitter->instructions, allocator) = stack_sub;
  u64 stack_sub_instruction_idx = emitter->instructions.len - 1;

  amd64_color_interference_graph(emitter, allocator);

  if (verbose) {
    printf("\n------------ Colored interference graph ------------\n");
    lir_print_interference_graph(emitter->interference_graph,
                                 emitter->lir_emitter->lifetimes);
    printf("\n------------ Memory locations ------------\n");
    amd64_print_memory_locations(emitter->interference_graph.memory_locations,
                                 emitter->lir_emitter->virtual_registers);
  }
  lir_sanity_check_interference_graph(emitter->interference_graph, true);

  for (u64 i = 0; i < lirs.len; i++) {
    amd64_lir_to_asm(emitter, PG_SLICE_AT(lirs, i), allocator);
  }

  if (emitter->rbp_max_offset > 0) {
    u32 rsp_max_offset_aligned_16 =
        (u32)PG_ROUNDUP(emitter->rbp_max_offset, 16);

    PG_SLICE_AT_PTR(&emitter->instructions, stack_sub_instruction_idx)
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
        .origin.synthetic = true,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = stack_add;
  } else {
    PG_DYN_REMOVE_AT(&emitter->instructions, stack_sub_instruction_idx);
  }
  return (InterferenceNodeIndexSlice){0};
}
