#include "amd64.h"

#define PG_TEST_AMD64_GEN_DIR_NAME "test_amd64"

static void write_instruction(Amd64Instruction ins, PgWriter *writer_asm_text,
                              PgWriter *writer_instructions_binary) {
  amd64_print_instruction(ins, false, writer_asm_text, nullptr);
  (void)pg_writer_write_string_full(writer_asm_text, PG_S("\n"), nullptr);

  Pgu8Slice ins_bytes = {.data = (u8 *)&ins, .len = sizeof(ins)};
  PG_ASSERT(0 == pg_writer_write_string_full(writer_instructions_binary,
                                             ins_bytes, nullptr));
}

static void run_assembler(PgAllocator *allocator) {
  PgString args[] = {
      PG_S("-mllvm"),
      PG_S("--x86-asm-syntax=intel"),
      PG_S("-x"),
      PG_S("assembler"),
      PG_S("-O0"),
      PG_S("-nostdlib"),
      PG_S("-Wl,--oformat=binary"),
      PG_S("test_amd64.s"),
      PG_S("-o"),
      PG_S("test_amd64.bin"),
  };
  PgStringSlice args_slice = {.data = args, .len = PG_STATIC_ARRAY_LEN(args)};

  PgProcessSpawnOptions options = {0};
  PgProcessResult res_spawn =
      pg_process_spawn(PG_S("clang"), args_slice, options, allocator);
  PG_ASSERT(0 == res_spawn.err);

  PgProcess process = res_spawn.res;
  PgProcessExitResult res_proc = pg_process_wait(process, allocator);

  PG_ASSERT(0 == res_proc.err);
  PG_ASSERT(0 == res_proc.res.exit_status);
}

static void gen_lea(PgWriter *writer_asm_text,
                    PgWriter *writer_instructions_binary) {
  // Reg-Reg/mem.
  // TODO: Scale, index.
  for (u8 i = 1; i < 14; i++) {
    Register reg_a = {i};

    i32 displacements[] = {0, 8, INT32_MAX};
    Pgi32Slice displacements_slice = {
        .data = displacements,
        .len = PG_STATIC_ARRAY_LEN(displacements),
    };

    for (u8 j = 1; j < 14; j++) {
      Register reg_b = {j};

      // Skip `ASM_OPERAND_SIZE_1` since `lea` does not support it.
      for (u64 k = 1; k < PG_STATIC_ARRAY_LEN(asm_sizes); k++) {
        AsmOperandSize size =
            PG_C_ARRAY_AT(asm_sizes, PG_STATIC_ARRAY_LEN(asm_sizes), k);

        for (u64 l = 0; l < displacements_slice.len; l++) {
          i32 displacement = PG_SLICE_AT(displacements_slice, l);

          Amd64Instruction ins = {};
          ins.kind = AMD64_INSTRUCTION_KIND_LEA;
          ins.lhs = (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = reg_a,
              .size = size,
          };
          ins.rhs = (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
              .u.effective_address =
                  {
                      .base = reg_b,
                      .displacement = displacement,
                  },
              .size = size,
          };
          write_instruction(ins, writer_asm_text, writer_instructions_binary);
        }
      }
    }
  }
}

static void gen_mov(PgWriter *writer_asm_text,
                    PgWriter *writer_instructions_binary) {
  // Reg/mem-Reg and Reg-Reg/mem.
  // TODO: Scale, index.
  for (u8 i = 1; i < 14; i++) {
    Register reg_a = {i};

    i32 displacements[] = {0, 8, INT32_MAX};
    Pgi32Slice displacements_slice = {
        .data = displacements,
        .len = PG_STATIC_ARRAY_LEN(displacements),
    };

    for (u8 j = 1; j < 14; j++) {
      Register reg_b = {j};

      for (u64 k = 0; k < PG_STATIC_ARRAY_LEN(asm_sizes); k++) {
        AsmOperandSize size =
            PG_C_ARRAY_AT(asm_sizes, PG_STATIC_ARRAY_LEN(asm_sizes), k);

        for (u64 l = 0; l < displacements_slice.len; l++) {
          i32 displacement = PG_SLICE_AT(displacements_slice, l);

          Amd64Instruction ins = {};
          ins.kind = AMD64_INSTRUCTION_KIND_MOV;
          ins.lhs = (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
              .u.effective_address =
                  {
                      .base = reg_a,
                      .displacement = displacement,
                  },
              .size = size,
          };
          ins.rhs = (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = reg_b,
              .size = size,
          };
          write_instruction(ins, writer_asm_text, writer_instructions_binary);

          // Swap operands.
          {
            Amd64Operand tmp = ins.lhs;
            ins.lhs = ins.rhs;
            ins.rhs = tmp;
            write_instruction(ins, writer_asm_text, writer_instructions_binary);
          }
        }
      }
    }
  }

  // Reg-immediate.
  for (u8 i = 1; i < 14; i++) {
    Register reg_a = {i};

    u64 nums[] = {UINT8_MAX, UINT16_MAX, UINT32_MAX, UINT32_MAX + 1,
                  UINT64_MAX};
    Pgu64Slice nums_slice = {.data = nums, .len = PG_STATIC_ARRAY_LEN(nums)};

    for (u64 j = 0; j < nums_slice.len; j++) {
      u64 immediate = PG_SLICE_AT(nums_slice, j);

      for (u64 k = 0; k < PG_STATIC_ARRAY_LEN(asm_sizes); k++) {
        AsmOperandSize size =
            PG_C_ARRAY_AT(asm_sizes, PG_STATIC_ARRAY_LEN(asm_sizes), k);

        Amd64Instruction ins = {};
        ins.kind = AMD64_INSTRUCTION_KIND_MOV;
        ins.lhs = (Amd64Operand){
            .kind = AMD64_OPERAND_KIND_REGISTER,
            .u.reg = reg_a,
            .size = size,
        };
        ins.rhs = (Amd64Operand){
            .kind = AMD64_OPERAND_KIND_IMMEDIATE,
            .u.immediate = immediate,
            .size = size,
        };
        write_instruction(ins, writer_asm_text, writer_instructions_binary);
      }
    }
  }

  // Reg-reg.
  for (u8 i = 1; i < 14; i++) {
    Register reg_a = {i};

    for (u8 j = 1; j < 14; j++) {
      Register reg_b = {j};

      for (u8 k = 0; k < PG_STATIC_ARRAY_LEN(asm_sizes); k++) {
        AsmOperandSize size =
            PG_C_ARRAY_AT(asm_sizes, PG_STATIC_ARRAY_LEN(asm_sizes), k);

        Amd64Instruction ins = {};
        ins.kind = AMD64_INSTRUCTION_KIND_MOV;
        ins.lhs = (Amd64Operand){
            .kind = AMD64_OPERAND_KIND_REGISTER,
            .u.reg = reg_a,
            .size = size,
        };
        ins.rhs = (Amd64Operand){
            .kind = AMD64_OPERAND_KIND_REGISTER,
            .u.reg = reg_b,
            .size = size,
        };
        write_instruction(ins, writer_asm_text, writer_instructions_binary);
      }
    }
  }
}

static void gen_add(PgWriter *writer_asm_text,
                    PgWriter *writer_instructions_binary) {
  // Reg/mem-Reg and Reg-Reg/mem.
  // TODO: Scale, index.
  for (u8 i = 1; i < 14; i++) {
    Register reg_a = {i};

    i32 displacements[] = {0, 8, INT32_MAX};
    Pgi32Slice displacements_slice = {
        .data = displacements,
        .len = PG_STATIC_ARRAY_LEN(displacements),
    };

    for (u8 j = 1; j < 14; j++) {
      Register reg_b = {j};

      for (u64 k = 0; k < PG_STATIC_ARRAY_LEN(asm_sizes); k++) {
        AsmOperandSize size =
            PG_C_ARRAY_AT(asm_sizes, PG_STATIC_ARRAY_LEN(asm_sizes), k);

        for (u64 l = 0; l < displacements_slice.len; l++) {
          i32 displacement = PG_SLICE_AT(displacements_slice, l);

          Amd64Instruction ins = {};
          ins.kind = AMD64_INSTRUCTION_KIND_ADD;
          ins.lhs = (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
              .u.effective_address =
                  {
                      .base = reg_a,
                      .displacement = displacement,
                  },
              .size = size,
          };
          ins.rhs = (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = reg_b,
              .size = size,
          };
          write_instruction(ins, writer_asm_text, writer_instructions_binary);

          // Swap operands.
          {
            Amd64Operand tmp = ins.lhs;
            ins.lhs = ins.rhs;
            ins.rhs = tmp;
            write_instruction(ins, writer_asm_text, writer_instructions_binary);
          }
        }
      }
    }
  }

  // Reg-immediate.
  for (u8 i = 1; i < 14; i++) {
    Register reg_a = {i};

    i64 nums[] = {INT8_MAX, INT16_MAX, INT32_MAX};
    Pgi64Slice nums_slice = {.data = nums, .len = PG_STATIC_ARRAY_LEN(nums)};
    i64 maxs[] = {
        [ASM_OPERAND_SIZE_1] = INT8_MAX,
        [ASM_OPERAND_SIZE_2] = INT16_MAX,
        [ASM_OPERAND_SIZE_4] = INT32_MAX,
        [ASM_OPERAND_SIZE_8] = INT64_MAX,
    };

    for (u64 j = 0; j < nums_slice.len; j++) {
      i64 immediate = PG_SLICE_AT(nums_slice, j);

      for (u64 k = 0; k < PG_STATIC_ARRAY_LEN(asm_sizes); k++) {
        AsmOperandSize size =
            PG_C_ARRAY_AT(asm_sizes, PG_STATIC_ARRAY_LEN(asm_sizes), k);

        Amd64Instruction ins = {};
        ins.kind = AMD64_INSTRUCTION_KIND_ADD;
        ins.lhs = (Amd64Operand){
            .kind = AMD64_OPERAND_KIND_REGISTER,
            .u.reg = reg_a,
            .size = size,
        };
        i64 max = maxs[size];
        ins.rhs = (Amd64Operand){
            .kind = AMD64_OPERAND_KIND_IMMEDIATE,
            .u.immediate = (u64)(immediate > max ? max : immediate),
            .size = size,
        };
        write_instruction(ins, writer_asm_text, writer_instructions_binary);
      }
    }
  }

  // Reg-reg.
  for (u8 i = 1; i < 14; i++) {
    Register reg_a = {i};

    for (u8 j = 1; j < 14; j++) {
      Register reg_b = {j};

      for (u8 k = 0; k < PG_STATIC_ARRAY_LEN(asm_sizes); k++) {
        AsmOperandSize size =
            PG_C_ARRAY_AT(asm_sizes, PG_STATIC_ARRAY_LEN(asm_sizes), k);

        Amd64Instruction ins = {};
        ins.kind = AMD64_INSTRUCTION_KIND_ADD;
        ins.lhs = (Amd64Operand){
            .kind = AMD64_OPERAND_KIND_REGISTER,
            .u.reg = reg_a,
            .size = size,
        };
        ins.rhs = (Amd64Operand){
            .kind = AMD64_OPERAND_KIND_REGISTER,
            .u.reg = reg_b,
            .size = size,
        };
        write_instruction(ins, writer_asm_text, writer_instructions_binary);
      }
    }
  }
}

int main() {
  PgArena arena = pg_arena_make_from_virtual_mem(513 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  Pgu8Dyn sb_asm_text = {0};
  PG_DYN_ENSURE_CAP(&sb_asm_text, 256 * PG_MiB, allocator);
  PgWriter writer_asm_text = pg_writer_make_from_string_builder(&sb_asm_text);

  Pgu8Dyn sb_instructions_binary = {0};
  PG_DYN_ENSURE_CAP(&sb_instructions_binary, 256 * PG_MiB, allocator);
  PgWriter writer_instructions_binary =
      pg_writer_make_from_string_builder(&sb_instructions_binary);

  PG_ASSERT(0 == pg_writer_write_string_full(&writer_asm_text,
                                             PG_S(".globl _start\n _start:\n"),
                                             nullptr));

  gen_add(&writer_asm_text, &writer_instructions_binary);
  gen_lea(&writer_asm_text, &writer_instructions_binary);
  gen_mov(&writer_asm_text, &writer_instructions_binary);

  pg_file_write_full(PG_S("test_amd64.s"), PG_DYN_SLICE(PgString, sb_asm_text),
                     0600, allocator);
  pg_file_write_full(PG_S("test_amd64.ins"),
                     PG_DYN_SLICE(PgString, sb_instructions_binary), 0600,
                     allocator);
  run_assembler(allocator);
}
