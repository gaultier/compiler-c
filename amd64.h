#pragma once
#include "asm.h"
#include "ir.h"

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
} Amd64OperandKind;

// Effective address = `base + index * scale + displacement`.
typedef struct {
  Register base;
  Register index;
  u8 scale;
  u32 displacement;
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
  MemoryLocation location;
  IrVar var;
} VarToMemoryLocation;
PG_DYN(VarToMemoryLocation) VarToMemoryLocationDyn;

typedef struct {
  Amd64InstructionKind kind;
  Amd64Operand dst, src;
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

  PgString file_name;
} Amd64Program;

typedef struct {
  // TODO: Could remove this and instead track available registers with
  // `var_to_memory_location` with entries having no variable.
  RegisterDyn available;
  // Track in which machine register is a var stored currently.
  // Indexed by the var value.
  VarToMemoryLocationDyn var_to_memory_location;
} Amd64RegisterAllocator;

static void amd64_print_register(Register reg) {
  PgString s = PG_SLICE_AT(amd64_register_to_string_slice, reg.value);
  printf("%.*s", (i32)s.len, s.data);
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
    printf(" + ");
    amd64_print_register(operand.effective_address.index);
    printf(" * %" PRIu8 " + %" PRIu32 "]", operand.effective_address.scale,
           operand.effective_address.displacement);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void amd64_print_var_to_memory_location(
    VarToMemoryLocationDyn var_to_memory_location) {
  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation var_to_mem_loc = PG_SLICE_AT(var_to_memory_location, i);
    printf("x%" PRIu32 ":", var_to_mem_loc.var.value);
    switch (var_to_mem_loc.location.kind) {
    case MEMORY_LOCATION_KIND_REGISTER:
      amd64_print_register(var_to_mem_loc.location.reg);
      break;
    case MEMORY_LOCATION_KIND_STACK:
      amd64_print_register(amd64_rsp);
      i64 offset = var_to_mem_loc.location.stack_pointer_offset;
      printf("%c%ld", offset > 0 ? '+' : '-', offset);
      break;
    case MEMORY_LOCATION_KIND_MEMORY:
      printf("%#lx", var_to_mem_loc.location.memory_address);
      break;
    case MEMORY_LOCATION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
    printf(" ");
  }
  printf("\n");
}

static void amd64_print_instructions(Amd64InstructionSlice instructions) {
  for (u64 i = 0; i < instructions.len; i++) {
    printf("[%" PRIu64 "] ", i);

    Amd64Instruction instruction = PG_SLICE_AT(instructions, i);
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
    case AMD64_INSTRUCTION_KIND_LEA:
      printf("lea ");
      break;
    case AMD64_INSTRUCTION_KIND_RET:
      printf("ret ");
      break;
    case AMD64_INSTRUCTION_KIND_SYSCALL:
      printf("syscall ");
      break;
    default:
      PG_ASSERT(0);
      break;
    }

    if (AMD64_OPERAND_KIND_NONE != instruction.dst.kind) {
      amd64_print_operand(instruction.dst);
    }

    if (AMD64_OPERAND_KIND_NONE != instruction.src.kind) {
      PG_ASSERT(AMD64_OPERAND_KIND_NONE != instruction.dst.kind);

      printf(", ");
      amd64_print_operand(instruction.src);
    }

    printf(" ; ");
    amd64_print_var_to_memory_location(
        instruction.var_to_memory_location_frozen);

    printf("\n");
  }
}

[[maybe_unused]]
static void amd64_print_section(Amd64Section section) {
  printf("BITS 64\n");
  printf("CPU X64\n");

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

  // MOV reg64, imm64 | B8 +rq iq | Move an 64-bit immediate value into a 64-bit
  // register.
  if (AMD64_OPERAND_KIND_REGISTER == instruction.dst.kind &&
      AMD64_OPERAND_KIND_IMMEDIATE == instruction.src.kind) {
    u8 rex = AMD64_REX_DEFAULT;
    if (instruction.src.immediate > UINT32_MAX) {
      rex |= AMD64_REX_MASK_W;
    }
    if (amd64_is_register_64_bits_only(instruction.dst.reg)) {
      rex |= AMD64_REX_MASK_B;
    }

    if (AMD64_REX_DEFAULT != rex) {
      *PG_DYN_PUSH(sb, allocator) = rex;
    }

    u8 opcode = 0xb8;
    *PG_DYN_PUSH(sb, allocator) =
        opcode + (amd64_encode_register_value(instruction.dst.reg) & 0b111);

    if (instruction.src.immediate <= UINT32_MAX) {
      pg_byte_buffer_append_u32(sb, (u32)instruction.src.immediate, allocator);
    } else {
      pg_byte_buffer_append_u64(sb, instruction.src.immediate, allocator);
    }

    return;
  }

  // MOV reg/mem64, reg64 | 89 /r | Move the contents of a 64-bit register to a
  // 64-bit destination register or memory operand.
  if (AMD64_OPERAND_KIND_REGISTER == instruction.dst.kind &&
      AMD64_OPERAND_KIND_REGISTER == instruction.src.kind) {
    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.dst.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    if (amd64_is_register_64_bits_only(instruction.src.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x89;
    *PG_DYN_PUSH(sb, allocator) = opcode;
    u8 modrm =
        (0b11 << 6) |
        (u8)((amd64_encode_register_value(instruction.src.reg) & 0b111) << 3) |
        (u8)(amd64_encode_register_value(instruction.dst.reg) & 0b111);
    *PG_DYN_PUSH(sb, allocator) = modrm;

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
  PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == instruction.dst.kind);
  PG_ASSERT(AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS == instruction.src.kind);

  u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
  if (amd64_is_register_64_bits_only(instruction.dst.reg)) {
    rex |= AMD64_REX_MASK_B;
  }
  *PG_DYN_PUSH(sb, allocator) = rex;

  u8 opcode = 0x8d;
  *PG_DYN_PUSH(sb, allocator) = opcode;

  if (0 == instruction.src.effective_address.base.value &&
      0 == instruction.src.effective_address.index.value) {
    PG_ASSERT(0 == instruction.src.effective_address.scale);

    u8 modrm =
        (0b00 << 6) |
        (u8)((amd64_encode_register_value(instruction.dst.reg) & 0b111) << 3) |
        0b100 /* sib + disp32 */;
    *PG_DYN_PUSH(sb, allocator) = modrm;

    u8 sib = AMD64_SIB_INDEX_NONE | AMD64_SIB_BASE_DISP32;
    *PG_DYN_PUSH(sb, allocator) = sib;

    pg_byte_buffer_append_u32_within_capacity(
        sb, instruction.src.effective_address.displacement);
    return;
  }
  PG_ASSERT(0 && "todo");
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
    u8 rex = AMD64_REX_DEFAULT | AMD64_REX_MASK_W;
    if (amd64_is_register_64_bits_only(instruction.dst.reg)) {
      rex |= AMD64_REX_MASK_R;
    }
    if (amd64_is_register_64_bits_only(instruction.src.reg)) {
      rex |= AMD64_REX_MASK_B;
    }
    *PG_DYN_PUSH(sb, allocator) = rex;

    u8 opcode = 0x03;
    *PG_DYN_PUSH(sb, allocator) = opcode;

    u8 modrm =
        (0b11 << 6) |
        (u8)((amd64_encode_register_value(instruction.dst.reg) & 0b111) << 3) |
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
                                     Amd64Program program,
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
    amd64_encode_instruction_lea(sb, instruction, program, allocator);
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
                                 Amd64Program program, PgAllocator *allocator) {
  for (u64 i = 0; i < section.instructions.len; i++) {
    Amd64Instruction instruction = PG_SLICE_AT(section.instructions, i);
    amd64_encode_instruction(sb, instruction, program, allocator);
  }
}

[[nodiscard]]
static PgString amd64_encode_program_text(Amd64Program program,
                                          PgAllocator *allocator) {
  Pgu8Dyn sb = {0};
  PG_DYN_ENSURE_CAP(&sb, 16 * PG_KiB, allocator);

  for (u64 i = 0; i < program.text.len; i++) {
    Amd64Section section = PG_SLICE_AT(program.text, i);
    amd64_encode_section(&sb, section, program, allocator);
  }

  return PG_DYN_SLICE(PgString, sb);
}

[[nodiscard]]
static VarToMemoryLocation *amd64_find_var_to_memory_location_by_var(
    VarToMemoryLocationDyn var_to_memory_location, IrVar var) {
  VarToMemoryLocation *var_to_mem_loc = nullptr;

  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation *elem = PG_SLICE_AT_PTR(&var_to_memory_location, i);
    if (elem->var.value == var.value) {
      var_to_mem_loc = elem;
      break;
    }
  }

  return var_to_mem_loc;
}

[[nodiscard]]
static VarToMemoryLocation *amd64_find_var_to_memory_location_by_register(
    VarToMemoryLocationDyn var_to_memory_location, Register reg) {
  VarToMemoryLocation *var_to_mem_loc = nullptr;

  for (u64 i = 0; i < var_to_memory_location.len; i++) {
    VarToMemoryLocation *elem = PG_SLICE_AT_PTR(&var_to_memory_location, i);
    if (MEMORY_LOCATION_KIND_REGISTER == elem->location.kind &&
        elem->location.reg.value == reg.value) {
      var_to_mem_loc = elem;
      break;
    }
  }

  return var_to_mem_loc;
}

static void amd64_upsert_var_to_memory_location(
    VarToMemoryLocationDyn *var_to_memory_location, IrVar var, Register reg,
    PgAllocator *allocator) {
  VarToMemoryLocation *var_to_mem_loc =
      amd64_find_var_to_memory_location_by_var(*var_to_memory_location, var);

  if (!var_to_mem_loc) {
    *PG_DYN_PUSH(var_to_memory_location, allocator) = (VarToMemoryLocation){
        .location =
            {
                .kind = MEMORY_LOCATION_KIND_REGISTER,
                .reg = reg,
            },
        .var = var,
    };
  } else {
    PG_ASSERT(var_to_mem_loc->var.value == var.value);
    // TODO: Review.
    PG_ASSERT(MEMORY_LOCATION_KIND_REGISTER == var_to_mem_loc->location.kind);
    var_to_mem_loc->location.reg = reg;
  }

  // Another var previously in this register has just been overriden so
  // we remove the mapping.
  u64 other_vars_count = 0;
  for (u64 i = 0; i < var_to_memory_location->len;) {
    VarToMemoryLocation elem = PG_SLICE_AT(*var_to_memory_location, i);
    if (MEMORY_LOCATION_KIND_REGISTER == elem.location.kind &&
        elem.location.reg.value == reg.value && elem.var.value != var.value) {
      other_vars_count += 1;
      PG_DYN_SWAP_REMOVE(var_to_memory_location, i);
      continue;
    }

    i++;
  }
  PG_ASSERT(other_vars_count <= 1);
}

static Amd64Operand
amd64_ir_value_to_operand(IrValue val,
                          VarToMemoryLocationDyn var_to_memory_location) {
  switch (val.kind) {
  case IR_VALUE_KIND_NONE:
    PG_ASSERT(0);
  case IR_VALUE_KIND_U64:
    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_IMMEDIATE,
        .immediate = val.n64,
    };
  case IR_VALUE_KIND_VAR: {
    VarToMemoryLocation *var_to_mem_loc =
        amd64_find_var_to_memory_location_by_var(var_to_memory_location,
                                                 val.var);
    PG_ASSERT(nullptr != var_to_mem_loc);
    PG_ASSERT(MEMORY_LOCATION_KIND_REGISTER == var_to_mem_loc->location.kind);
    PG_ASSERT(var_to_mem_loc->location.reg.value != 0);

    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_REGISTER,
        .reg = var_to_mem_loc->location.reg,
    };
  }
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static Amd64RegisterAllocator
amd64_make_register_allocator(PgAllocator *allocator) {
  Amd64RegisterAllocator reg_alloc = {0};
  PG_DYN_ENSURE_CAP(&reg_alloc.available, 16, allocator);

  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_rax;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_rbx;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_rcx;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_rdx;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_rdi;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_rsi;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_r8;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_r9;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_r10;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_r11;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_r12;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_r13;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_r14;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc.available) = amd64_r15;

  return reg_alloc;
}

[[nodiscard]]
static Register
amd64_allocate_register_for_var(Amd64RegisterAllocator *reg_alloc, IrVar var,
                                PgAllocator *allocator) {
  // TODO: Spill.
  PG_ASSERT(reg_alloc->available.len > 0 && "todo");

  Register reg = PG_SLICE_AT(reg_alloc->available, 0);

  PG_DYN_SWAP_REMOVE(&reg_alloc->available, 0);

  amd64_upsert_var_to_memory_location(&reg_alloc->var_to_memory_location, var,
                                      reg, allocator);

  return reg;
}

static void amd64_store_var_into_register(Amd64RegisterAllocator *reg_alloc,
                                          Register dst, IrValue val,
                                          Origin origin,
                                          Amd64InstructionDyn *instructions,
                                          PgAllocator *allocator) {

  PG_ASSERT(IR_VALUE_KIND_VAR == val.kind);
  VarToMemoryLocation *var_to_mem_loc_by_var =
      amd64_find_var_to_memory_location_by_var(
          reg_alloc->var_to_memory_location, val.var);

  // Nothing to do, the var is already located in the right register.
  if (var_to_mem_loc_by_var &&
      MEMORY_LOCATION_KIND_REGISTER == var_to_mem_loc_by_var->location.kind &&
      var_to_mem_loc_by_var->location.reg.value == dst.value) {
    return;
  }

  VarToMemoryLocation *var_to_mem_loc_by_reg =
      amd64_find_var_to_memory_location_by_register(
          reg_alloc->var_to_memory_location, dst);

  if (var_to_mem_loc_by_reg) { // Target register is occupied by a different
                               // variable.
    // Move things around to free the target register.
    PG_ASSERT(var_to_mem_loc_by_var);
    PG_ASSERT(MEMORY_LOCATION_KIND_REGISTER ==
              var_to_mem_loc_by_var->location.kind);
    PG_ASSERT(var_to_mem_loc_by_var->location.reg.value != 0);

    Register reg_mov_dst = amd64_allocate_register_for_var(
        reg_alloc, var_to_mem_loc_by_reg->var, allocator);
    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .dst =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = reg_mov_dst,
            },
        .src =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = dst,
            },
        .origin = {.synthetic = true},
    };
    amd64_upsert_var_to_memory_location(&reg_alloc->var_to_memory_location,
                                        var_to_mem_loc_by_reg->var, reg_mov_dst,
                                        allocator);
    PG_DYN_CLONE(&instruction.var_to_memory_location_frozen,
                 reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = instruction;
    *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc->available) = dst;
  }
  // `dst` register is free.
  PG_ASSERT(nullptr == amd64_find_var_to_memory_location_by_register(
                           reg_alloc->var_to_memory_location, dst));

  i64 reg_idx = -1;
  for (u64 i = 0; i < reg_alloc->available.len; i++) {
    if (PG_SLICE_AT(reg_alloc->available, i).value == dst.value) {
      reg_idx = (i64)i;
      break;
    }
  }
  PG_ASSERT(-1 != reg_idx);
  PG_DYN_SWAP_REMOVE(&reg_alloc->available, reg_idx);

  Amd64Instruction instruction = {
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .dst =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .reg = dst,
          },
      .src = amd64_ir_value_to_operand(val, reg_alloc->var_to_memory_location),
      .origin = origin,
  };
  // Finally the var is in the `dst` register.
  amd64_upsert_var_to_memory_location(&reg_alloc->var_to_memory_location,
                                      val.var, dst, allocator);
  PG_DYN_CLONE(&instruction.var_to_memory_location_frozen,
               reg_alloc->var_to_memory_location, allocator);
  *PG_DYN_PUSH(instructions, allocator) = instruction;
}

static void amd64_ir_to_asm(IrSlice irs, u32 ir_idx,
                            Amd64InstructionDyn *instructions,
                            Amd64RegisterAllocator *reg_alloc,
                            PgAllocator *allocator) {
  Ir ir = PG_SLICE_AT(irs, ir_idx);

  switch (ir.kind) {
  case IR_KIND_NONE:
    PG_ASSERT(0);
  case IR_KIND_ADD: {
    PG_ASSERT(2 == ir.operands.len);
    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_ADD,
        .src = amd64_ir_value_to_operand(PG_SLICE_AT(ir.operands, 0),
                                         reg_alloc->var_to_memory_location),
        .dst = amd64_ir_value_to_operand(PG_SLICE_AT(ir.operands, 1),
                                         reg_alloc->var_to_memory_location),
        .origin = ir.origin,
    };
    PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == instruction.dst.kind);
    IrVar var = {ir_idx};
    amd64_upsert_var_to_memory_location(&reg_alloc->var_to_memory_location, var,
                                        instruction.dst.reg, allocator);
    PG_DYN_CLONE(&instruction.var_to_memory_location_frozen,
                 reg_alloc->var_to_memory_location, allocator);

    *PG_DYN_PUSH(instructions, allocator) = instruction;

  } break;
  case IR_KIND_LOAD: {
    PG_ASSERT(1 == ir.operands.len);
    IrValue src = PG_SLICE_AT(ir.operands, 0);
    Amd64InstructionKind kind =
        // TODO: Smarter mov vs lea selection.
        (IR_VALUE_KIND_U64 == src.kind || IR_VALUE_KIND_VAR == src.kind)
            ? AMD64_INSTRUCTION_KIND_MOV
            : AMD64_INSTRUCTION_KIND_LEA;

    Amd64Instruction instruction = {
        .kind = kind,
        .src =
            amd64_ir_value_to_operand(src, reg_alloc->var_to_memory_location),
        .dst =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = amd64_allocate_register_for_var(
                    reg_alloc, (IrVar){ir_idx}, allocator),
            },
        .origin = ir.origin,
    };
    PG_DYN_CLONE(&instruction.var_to_memory_location_frozen,
                 reg_alloc->var_to_memory_location, allocator);
    *PG_DYN_PUSH(instructions, allocator) = instruction;

  } break;
  case IR_KIND_SYSCALL: {
    PG_ASSERT(ir.operands.len <= amd64_arch.syscall_calling_convention.len);

    for (u64 j = 0; j < ir.operands.len; j++) {
      IrValue val = PG_SLICE_AT(ir.operands, j);
      Register dst = PG_SLICE_AT(amd64_arch.syscall_calling_convention, j);
      amd64_store_var_into_register(reg_alloc, dst, val, ir.origin,
                                    instructions, allocator);
    }

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
        .origin = ir.origin,
    };
    IrVar var = {ir_idx};
    amd64_upsert_var_to_memory_location(&reg_alloc->var_to_memory_location, var,
                                        amd64_arch.return_value, allocator);
    PG_DYN_CLONE(&instruction.var_to_memory_location_frozen,
                 reg_alloc->var_to_memory_location, allocator);
    *PG_DYN_PUSH(instructions, allocator) = instruction;

  } break;

  case IR_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir.operands.len);
    PG_ASSERT(0 && "TODO");
  } break;

  default:
    PG_ASSERT(0);
  }
}

static void amd64_irs_to_asm(IrSlice irs, Amd64InstructionDyn *instructions,
                             Amd64RegisterAllocator *reg_alloc,
                             PgAllocator *allocator) {
  for (u64 i = 0; i < irs.len; i++) {
    amd64_ir_to_asm(irs, (u32)i, instructions, reg_alloc, allocator);
  }
}
