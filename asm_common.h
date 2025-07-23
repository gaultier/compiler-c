#pragma once

#include "ir.h"

typedef struct {
  u32 indices_occupied_bitfield;
  PG_PAD(4);
  RegisterSlice registers;
} GprSet;

typedef struct {
  RegisterSlice caller_saved;
  RegisterSlice callee_saved;
  RegisterSlice calling_convention;
  RegisterSlice syscall_calling_convention;
  RegisterSlice gprs;
  Register syscall_num;
  Register syscall_ret;
  Register return_value;
  Register stack_pointer;
  Register base_pointer;
  PG_PAD(3);
} Architecture;

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
  PG_PAD(1);
  i32 displacement;
} Amd64EffectiveAddress;

// Size in bytes.
typedef enum : u8 {
  ASM_OPERAND_SIZE_0 = 0,
  ASM_OPERAND_SIZE_1 = 1,
  ASM_OPERAND_SIZE_2 = 2,
  ASM_OPERAND_SIZE_4 = 4,
  ASM_OPERAND_SIZE_8 = 8,
  // TODO: More (SIMD).
} AsmOperandSize;

static const AsmOperandSize asm_sizes[] = {
    ASM_OPERAND_SIZE_1,
    ASM_OPERAND_SIZE_2,
    ASM_OPERAND_SIZE_4,
    ASM_OPERAND_SIZE_8,
};

typedef struct {
  Amd64OperandKind kind;
  AsmOperandSize size;
  PG_PAD(3);
  union {
    Register reg;
    u64 immediate;
    Amd64EffectiveAddress effective_address;
    Label label;
  } u;
} Amd64Operand;
PG_SLICE(Amd64Operand) Amd64OperandSlice;
PG_DYN(Amd64Operand) Amd64OperandDyn;

typedef enum : u16 {
  AMD64_INSTRUCTION_KIND_NONE,
  AMD64_INSTRUCTION_KIND_MOV,
  AMD64_INSTRUCTION_KIND_ADD,
  AMD64_INSTRUCTION_KIND_SUB,
  AMD64_INSTRUCTION_KIND_LEA,
  AMD64_INSTRUCTION_KIND_RET,
  AMD64_INSTRUCTION_KIND_SYSCALL,
  AMD64_INSTRUCTION_KIND_PUSH,
  AMD64_INSTRUCTION_KIND_POP,
  AMD64_INSTRUCTION_KIND_LABEL_DEFINITION,
  AMD64_INSTRUCTION_KIND_CMP,
  AMD64_INSTRUCTION_KIND_JMP,
  AMD64_INSTRUCTION_KIND_JMP_IF_EQ,
  AMD64_INSTRUCTION_KIND_JMP_IF_NOT_EQ,
  AMD64_INSTRUCTION_KIND_JMP_IF_ZERO,
  AMD64_INSTRUCTION_KIND_SET_IF_EQ,
  AMD64_INSTRUCTION_KIND_UD2,
} Amd64InstructionKind;

typedef struct {
  Amd64InstructionKind kind;
  PG_PAD(6); // TODO: Optimize.
  Amd64Operand lhs, rhs;
  Origin origin;
} Amd64Instruction;
PG_SLICE(Amd64Instruction) Amd64InstructionSlice;
PG_DYN(Amd64Instruction) Amd64InstructionDyn;

typedef struct {
  PgString name;
  u16 flags;
  PG_PAD(6);
  union {
    Amd64InstructionDyn amd64_instructions;
  } u;
} AsmCodeSection;
PG_DYN(AsmCodeSection) AsmCodeSectionDyn;

typedef enum {
  ASM_CONSTANT_KIND_NONE,
  ASM_CONSTANT_KIND_U64,
  ASM_CONSTANT_KIND_BYTES,
} AsmConstantKind;

typedef struct {
  PgString name;
  u64 address_absolute;
  AsmConstantKind kind;
  PG_PAD(4);
  union {
    u64 n64;
    PgString bytes;
  } u;
} AsmConstant;
PG_DYN(AsmConstant) AsmConstantDyn;

typedef struct {
  Label label;
  u64 code_address;
} LabelAddress;
PG_DYN(LabelAddress) LabelAddressDyn;

typedef struct {
  AsmCodeSectionDyn text;
  AsmConstantDyn rodata;
  u64 vm_start;
  LabelAddressDyn label_addresses;
  LabelAddressDyn jumps_to_backpatch;

  PgString file_path;
} AsmProgram;

[[nodiscard]] static AsmOperandSize asm_type_size_to_operand_size(u64 size) {
  switch (size) {
  case 1:
    return ASM_OPERAND_SIZE_1;
  case 2:
    return ASM_OPERAND_SIZE_2;
  case 4:
    return ASM_OPERAND_SIZE_4;
  case 8:
    return ASM_OPERAND_SIZE_8;
  default:
    PG_ASSERT(0);
  }
}
