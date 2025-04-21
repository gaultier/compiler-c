#pragma once
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

typedef struct {
  u32 value;
} Label;

typedef struct {
  Label label;
  u64 address_text;
} LabelLocation;
PG_SLICE(LabelLocation) LabelLocationSlice;
PG_DYN(LabelLocation) LabelLocationDyn;
