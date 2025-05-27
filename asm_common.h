#pragma once

#include "ir.h"

typedef struct {
  u32 indices_occupied_bitfield;
  RegisterSlice registers;
} GprSet;

typedef struct {
  Register return_value;
  RegisterSlice caller_saved;
  RegisterSlice callee_saved;
  RegisterSlice calling_convention;
  Register syscall_num;
  RegisterSlice syscall_calling_convention;
  Register syscall_ret;
  Register stack_pointer;
  Register base_pointer;
  RegisterSlice gprs;
} Architecture;

typedef struct {
  PgString name;
  u16 flags;
  PgAnyDyn instructions;
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
