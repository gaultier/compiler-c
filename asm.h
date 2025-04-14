#pragma once
#include "submodules/cstd/lib.c"

typedef struct {
  u64 value;
} Register;
PG_SLICE(Register) RegisterSlice;

typedef struct {
  Register return_value;
  RegisterSlice call_preserved;
  RegisterSlice calling_convention;
  Register stack_pointer;
  Register base_pointer;
} Architecture;
