#pragma once
#include "lir.h"

typedef enum {
  AMD64_SECTION_FLAG_NONE = 0,
  AMD64_SECTION_FLAG_GLOBAL = 1 << 0,
} AsmCodeSectionFlag;

typedef struct {
  PgString name;
  AsmCodeSectionFlag flags;
  PgAnySlice instructions;
} AsmCodeSection;
PG_SLICE(AsmCodeSection) AsmCodeSectionSlice;
PG_DYN(AsmCodeSection) AsmCodeSectionDyn;

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
  AsmCodeSectionSlice text;
  Amd64ConstantSlice rodata;
  u64 vm_start;
  LabelAddressDyn label_addresses;
  LabelAddressDyn jumps_to_backpatch;

  PgString file_name;
} Amd64Program;
