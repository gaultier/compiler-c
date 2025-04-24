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
