#pragma once
#include "ir.h"
#include "submodules/cstd/lib.c"

typedef struct {
  u64 value;
} Register;
PG_SLICE(Register) RegisterSlice;
PG_DYN(Register) RegisterDyn;

typedef struct {
  Register return_value;
  RegisterSlice call_preserved;
  RegisterSlice calling_convention;
  RegisterSlice syscall_calling_convention;
  Register stack_pointer;
  Register base_pointer;
} Architecture;

typedef enum {
  MEMORY_LOCATION_KIND_NONE,
  MEMORY_LOCATION_KIND_REGISTER,
  MEMORY_LOCATION_KIND_STACK,
  MEMORY_LOCATION_KIND_MEMORY,
} MemoryLocationKind;

typedef struct {
  MemoryLocationKind kind;
  union {
    Register reg;
    i32 base_pointer_offset;
    u64 memory_address;
  };
} MemoryLocation;
PG_SLICE(MemoryLocation) MemoryLocationSlice;
PG_DYN(MemoryLocation) MemoryLocationDyn;

typedef struct {
  IrLabelId label;
  u64 address_text;
} LabelAddress;
PG_SLICE(LabelAddress) LabelAddressSlice;
PG_DYN(LabelAddress) LabelAddressDyn;

typedef enum {
  LIR_KIND_NONE,
  LIR_KIND_ADD,
  LIR_KIND_SUB,
  LIR_KIND_MOV,
  LIR_KIND_SYSCALL,
  LIR_KIND_LOAD_EFFECTIVE_ADDRESS,
  LIR_KIND_JUMP_IF_EQ,
  LIR_KIND_JUMP,
  LIR_KIND_LABEL,
  LIR_KIND_CMP,
} LirKind;

typedef enum {
  LIR_OPERAND_KIND_NONE,
  LIR_OPERAND_KIND_REGISTER,
  LIR_OPERAND_KIND_IMMEDIATE,
  LIR_OPERAND_KIND_EFFECTIVE_ADDRESS,
  LIR_OPERAND_KIND_LABEL,
} LirOperandKind;

typedef struct {
  Register base;
  Register index;
  u8 scale;
  i32 displacement;
} LirEffectiveAddress;

typedef struct {
  LirOperandKind kind;
  union {
    Register reg;
    u64 immediate;
    LirEffectiveAddress effective_address;
    IrLabelId label;
  };
} LirOperand;
PG_SLICE(LirOperand) LirOperandSlice;
PG_DYN(LirOperand) LirOperandDyn;

typedef struct {
  MemoryLocationDyn locations;
  IrVar var;
} VarToMemoryLocation;

PG_DYN(VarToMemoryLocation) VarToMemoryLocationDyn;
typedef struct {
  LirKind kind;
  LirOperandDyn operands;
  Origin origin;
  VarToMemoryLocationDyn var_to_memory_location_frozen;
} LirInstruction;
PG_SLICE(LirInstruction) LirInstructionSlice;
PG_DYN(LirInstruction) LirInstructionDyn;

typedef struct {
  LirInstructionDyn instructions;
  VarToMemoryLocationDyn var_to_memory_location;
} LirEmitter;

[[nodiscard]] static bool asm_memory_location_eq(MemoryLocation a,
                                                 MemoryLocation b) {
  if (a.kind != b.kind) {
    return false;
  }

  switch (a.kind) {
  case MEMORY_LOCATION_KIND_REGISTER:
    return a.reg.value == b.reg.value;
  case MEMORY_LOCATION_KIND_STACK:
    return a.base_pointer_offset == b.base_pointer_offset;
  case MEMORY_LOCATION_KIND_MEMORY:
    return a.memory_address == b.memory_address;
  case MEMORY_LOCATION_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void lir_emit(LirEmitter *emitter, IrSlice irs, PgAllocator *allocator) {
}
