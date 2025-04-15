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
    [0] = 0,       [1] = 0b0000,  [2] = 0b0011,  [3] = 0b0001,  [4] = 0b0010,
    [5] = 0b0111,  [6] = 0b0110,  [7] = 0b1000,  [8] = 0b1001,  [9] = 0b1010,
    [10] = 0b1011, [11] = 0b1100, [12] = 0b1101, [13] = 0b1110, [14] = 0b1111,
    [15] = 0b0100, [16] = 0b0101,
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
  Amd64InstructionKind kind;
  Amd64Operand dst, src;
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

// Track in which machine register is a var stored in given range.
typedef struct {
  // Ir indices.
  u32 start, end;
  IrVar var;
  Register reg;
} Amd64IrVarRange;
PG_SLICE(Amd64IrVarRange) Amd64IrVarRangeSlice;
PG_DYN(Amd64IrVarRange) Amd64IrVarRangeDyn;

typedef struct {
  RegisterDyn available;
  RegisterDyn taken;
  Amd64IrVarRangeDyn var_ranges;
} Amd64RegisterAllocator;

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

static void amd64_dump_instructions(Pgu8Dyn *sb,
                                    Amd64InstructionSlice instructions,
                                    PgAllocator *allocator) {
  for (u64 i = 0; i < instructions.len; i++) {
    Amd64Instruction instruction = PG_SLICE_AT(instructions, i);

    // TODO: Validate operands?
    switch (instruction.kind) {
    case AMD64_INSTRUCTION_KIND_NONE:
      PG_ASSERT(0);
    case AMD64_INSTRUCTION_KIND_MOV:
      PG_DYN_APPEND_SLICE(sb, PG_S("mov "), allocator);
      break;
    case AMD64_INSTRUCTION_KIND_ADD:
      PG_DYN_APPEND_SLICE(sb, PG_S("add "), allocator);
      break;
    case AMD64_INSTRUCTION_KIND_LEA:
      PG_DYN_APPEND_SLICE(sb, PG_S("lea "), allocator);
      break;
    case AMD64_INSTRUCTION_KIND_RET:
      PG_DYN_APPEND_SLICE(sb, PG_S("ret "), allocator);
      break;
    case AMD64_INSTRUCTION_KIND_SYSCALL:
      PG_DYN_APPEND_SLICE(sb, PG_S("syscall "), allocator);
      break;
    default:
      PG_ASSERT(0);
      break;
    }

    if (AMD64_OPERAND_KIND_NONE != instruction.dst.kind) {
      amd64_dump_operand(instruction.dst, sb, allocator);
    }

    if (AMD64_OPERAND_KIND_NONE != instruction.src.kind) {
      PG_ASSERT(AMD64_OPERAND_KIND_NONE != instruction.dst.kind);

      PG_DYN_APPEND_SLICE(sb, PG_S(", "), allocator);
      amd64_dump_operand(instruction.src, sb, allocator);
    }

    *PG_DYN_PUSH(sb, allocator) = '\n';
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

  amd64_dump_instructions(&sb, section.instructions, allocator);
  return PG_DYN_SLICE(PgString, sb);
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
// Enable use of 64 bits registers in ModRM.
static const u8 AMD64_REX_MASK_R = 0b0000'0100;
// Enable use of 64 bits registers in SIB.
static const u8 AMD64_REX_MASK_X = 0b0000'0010;
// TODO: document.
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
      rex |= AMD64_REX_MASK_B;
    }
    if (amd64_is_register_64_bits_only(instruction.src.reg)) {
      rex |= AMD64_REX_MASK_R;
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
static Amd64IrVarRange amd64_locate_ir_var_range(Amd64IrVarRangeSlice ranges,
                                                 IrVar var, u32 current_pos) {
  for (u64 i = 0; i < ranges.len; i++) {
    Amd64IrVarRange range = PG_SLICE_AT(ranges, i);

    if (range.var.value != var.value) {
      continue;
    }
    if (current_pos < range.start) {
      continue;
    }

    if (0 != range.end && current_pos >= range.end) {
      continue;
    }

    return range;
  }
  return (Amd64IrVarRange){0};
}

static Amd64Operand amd64_ir_value_to_operand(IrValue val, u32 ir_idx,
                                              Amd64IrVarRangeSlice ranges) {
  switch (val.kind) {
  case IR_VALUE_KIND_NONE:
    PG_ASSERT(0);
  case IR_VALUE_KIND_U64:
    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_IMMEDIATE,
        .immediate = val.n64,
    };
  case IR_VALUE_KIND_VAR: {
    Amd64IrVarRange var_range =
        amd64_locate_ir_var_range(ranges, val.var, ir_idx);
    PG_ASSERT(0 != var_range.reg.value);

    return (Amd64Operand){
        .kind = AMD64_OPERAND_KIND_REGISTER,
        .reg = var_range.reg,
    };
  }
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static Amd64RegisterAllocator
amd64_make_register_allocator(PgAllocator *allocator) {
  Amd64RegisterAllocator reg_alloc = {0};
  PG_DYN_ENSURE_CAP(&reg_alloc.taken, 16, allocator);
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
amd64_allocate_register_for_var(Amd64RegisterAllocator *reg_alloc, u32 ir_idx,
                                IrVar var, PgAllocator *allocator) {
  // TODO: Spill.
  PG_ASSERT(reg_alloc->available.len > 0 && "todo");

  Register res = PG_SLICE_AT(reg_alloc->available, 0);

  PG_DYN_SWAP_REMOVE(&reg_alloc->available, 0);
  *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc->taken) = res;

  Amd64IrVarRange var_range = {
      .reg = res,
      .var = var,
      .start = ir_idx,
      .end = 0,
  };
  *PG_DYN_PUSH(&reg_alloc->var_ranges, allocator) = var_range;

  return res;
}

static void amd64_store_into_register(Amd64RegisterAllocator *reg_alloc,
                                      Register dst, IrValue val, u32 ir_idx,
                                      Amd64InstructionDyn *instructions,
                                      PgAllocator *allocator) {

  if (IR_VALUE_KIND_VAR == val.kind) {
    Amd64IrVarRange var_range = amd64_locate_ir_var_range(
        PG_DYN_SLICE(Amd64IrVarRangeSlice, reg_alloc->var_ranges), val.var,
        ir_idx);

    // Nothing to do, the var is already located in the right register.
    if (var_range.reg.value == dst.value) {
      return;
    }
  }

  i32 reg_idx = -1;
  for (u64 i = 0; i < reg_alloc->available.len; i++) {
    Register reg = PG_SLICE_AT(reg_alloc->available, i);
    if (reg.value == dst.value) {
      reg_idx = (i32)i;
      break;
    }
  }

  if (-1 == reg_idx) {
    PG_ASSERT(0); // TODO: move things around to free register.
  } else {
    PG_DYN_SWAP_REMOVE(&reg_alloc->available, reg_idx);
    *PG_DYN_PUSH_WITHIN_CAPACITY(&reg_alloc->taken) = dst;

    if (IR_VALUE_KIND_VAR == val.kind) {
      Amd64IrVarRange var_range = {
          .reg = dst,
          .var = val.var,
          .start = ir_idx,
          .end = 0,
      };
      *PG_DYN_PUSH(&reg_alloc->var_ranges, allocator) = var_range;
    }

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .dst =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = dst,
            },
        .src = amd64_ir_value_to_operand(
            val, ir_idx,
            PG_DYN_SLICE(Amd64IrVarRangeSlice, reg_alloc->var_ranges)),
    };
    *PG_DYN_PUSH(instructions, allocator) = instruction;
  }
}

static void amd64_ir_to_asm(IrSlice irs, u32 ir_idx,
                            Amd64InstructionDyn *instructions,
                            Amd64RegisterAllocator *reg_alloc,
                            PgAllocator *allocator) {
  Ir ir = PG_SLICE_AT(irs, ir_idx);
  Amd64IrVarRangeSlice var_ranges =
      PG_DYN_SLICE(Amd64IrVarRangeSlice, reg_alloc->var_ranges);

  switch (ir.kind) {
  case IR_KIND_NONE:
    PG_ASSERT(0);
  case IR_KIND_ADD: {
    PG_ASSERT(2 == ir.operands.len);
    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_ADD,
        .src = amd64_ir_value_to_operand(PG_SLICE_AT(ir.operands, 0), ir_idx,
                                         var_ranges),
        .dst = amd64_ir_value_to_operand(PG_SLICE_AT(ir.operands, 1), ir_idx,
                                         var_ranges),
    };

    *PG_DYN_PUSH(instructions, allocator) = instruction;

    PG_ASSERT(AMD64_OPERAND_KIND_REGISTER == instruction.dst.kind);
    IrVar var = {ir_idx};
    Amd64IrVarRange var_range = {
        .reg = instruction.dst.reg,
        .var = var,
        .start = ir_idx,
    };
    *PG_DYN_PUSH(&reg_alloc->var_ranges, allocator) = var_range;
  } break;
  case IR_KIND_LOAD: {
    PG_ASSERT(1 == ir.operands.len);
    IrValue src = PG_SLICE_AT(ir.operands, 0);
    Amd64InstructionKind kind = (IR_VALUE_KIND_U64 == src.kind)
                                    ? AMD64_INSTRUCTION_KIND_MOV
                                    : AMD64_INSTRUCTION_KIND_LEA;

    Amd64Instruction instruction = {
        .kind = kind,
        .src = amd64_ir_value_to_operand(src, ir_idx, var_ranges),
        .dst =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .reg = amd64_allocate_register_for_var(
                    reg_alloc, ir_idx, (IrVar){ir_idx}, allocator),
            },
    };
    *PG_DYN_PUSH(instructions, allocator) = instruction;

    IrVar var = {ir_idx};
    Amd64IrVarRange var_range = {
        .reg = instruction.dst.reg,
        .var = var,
        .start = ir_idx,
    };
    *PG_DYN_PUSH(&reg_alloc->var_ranges, allocator) = var_range;

  } break;
  case IR_KIND_SYSCALL: {
    PG_ASSERT(ir.operands.len <= amd64_arch.syscall_calling_convention.len);

    for (u64 j = 0; j < ir.operands.len; j++) {
      IrValue val = PG_SLICE_AT(ir.operands, j);
      Register dst = PG_SLICE_AT(amd64_arch.syscall_calling_convention, j);
      amd64_store_into_register(reg_alloc, dst, val, ir_idx, instructions,
                                allocator);
    }

    Amd64Instruction instruction = {
        .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
    };
    *PG_DYN_PUSH(instructions, allocator) = instruction;

    IrVar var = {ir_idx};
    Amd64IrVarRange var_range = {
        .reg = amd64_arch.return_value,
        .var = var,
        .start = ir_idx,
    };
    *PG_DYN_PUSH(&reg_alloc->var_ranges, allocator) = var_range;

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
