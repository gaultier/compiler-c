#pragma once
#include "lir.h"

typedef enum {
  ASM_SECTION_FLAG_NONE = 0,
  ASM_SECTION_FLAG_GLOBAL = 1 << 0,
} AsmCodeSectionFlag;

typedef struct {
  PgString name;
  AsmCodeSectionFlag flags;
  PgAnySlice instructions;
} AsmCodeSection;
PG_SLICE(AsmCodeSection) AsmCodeSectionSlice;
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
  };
} AsmConstant;
PG_SLICE(AsmConstant) AsmConstantSlice;
PG_DYN(AsmConstant) AsmConstantDyn;

typedef struct {
  AsmCodeSectionSlice text;
  AsmConstantSlice rodata;
  u64 vm_start;
  LabelAddressDyn label_addresses;
  LabelAddressDyn jumps_to_backpatch;

  PgString file_name;
} AsmProgram;

typedef struct AsmEmitter AsmEmitter;
struct AsmEmitter {
  void (*emit_prolog)(AsmEmitter *asm_emitter, PgAllocator *allocator);
  void (*emit_epilog)(AsmEmitter *asm_emitter, PgAllocator *allocator);
  void (*emit_lirs_to_asm)(AsmEmitter *asm_emitter,
                           LirInstructionSlice lir_instructions, bool verbose,
                           PgAllocator *allocator);
  PgString (*encode_code)(AsmProgram *program, PgAllocator *allocator);
  PgAnySlice (*get_instructions_slice)();
  void (*print_instructions)(PgAnySlice instructions);
  void (*sanity_check_instructions)(PgAnySlice instructions);
};
