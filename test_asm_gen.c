#include "amd64.h"

static void gen_helper_run_assembler(Amd64Instruction ins,
                                     PgAllocator *allocator) {
  PgString asm_human_readable = {0};
  {
    Pgu8Dyn sb = {0};
    PG_DYN_ENSURE_CAP(&sb, 256, allocator);
    PgWriter w = pg_writer_make_from_string_builder(&sb);
    amd64_print_instruction(ins, false, &w, allocator);
    (void)pg_writer_write_string_full(&w, PG_S("\n"), allocator);

    asm_human_readable = PG_DYN_SLICE(PgString, sb);
  }

  // NOTE: We could reduce the number of bytes written (and then read in the
  // tests) by not serializing the `origin` field which is always zero in this
  // context.
  Pgu8Slice ins_bytes = {.data = (u8 *)&ins, .len = sizeof(ins)};
  PgString ins_bytes_str = pg_bytes_to_hex_string(ins_bytes, 0, allocator);
  PG_ASSERT(!pg_string_is_empty(ins_bytes_str));

  PgString path_asm_s = pg_path_join(
      PG_S("test_amd64"),
      pg_string_concat(ins_bytes_str, PG_S(".s"), allocator), allocator);
  PG_ASSERT(
      0 == pg_file_write_full(path_asm_s, asm_human_readable, 0600, allocator));

  {
    PgString path_asm_ins = pg_path_join(
        PG_S("test_amd64"),
        pg_string_concat(ins_bytes_str, PG_S(".ins"), allocator), allocator);
    PG_ASSERT(0 ==
              pg_file_write_full(path_asm_ins, ins_bytes, 0600, allocator));
  }

  PgString path_asm_bin = pg_path_join(
      PG_S("test_amd64"),
      pg_string_concat(ins_bytes_str, PG_S(".bin"), allocator), allocator);

  printf("\n--- path_asm_s=%.*s path_asm_bin=%.*s\n%.*s\n---\n",
         (i32)path_asm_s.len, path_asm_s.data, (i32)path_asm_bin.len,
         path_asm_bin.data, (i32)asm_human_readable.len,
         asm_human_readable.data);

  PgString args[] = {
      PG_S("-mllvm"),
      PG_S("--x86-asm-syntax=intel"),
      PG_S("-x"),
      PG_S("assembler"),
      PG_S("-O0"),
      PG_S("-nostdlib"),
      PG_S("-Wl,--oformat=binary"),
      PG_S("-o"),
      path_asm_bin,
      PG_S("-"),
  };
  PgStringSlice args_slice = {.data = args, .len = PG_STATIC_ARRAY_LEN(args)};

  PgProcessSpawnOptions options = {
      .stdin_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
      .stderr_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
  };
  PgProcessResult res_spawn =
      pg_process_spawn(PG_S("clang"), args_slice, options, allocator);
  PG_ASSERT(0 == res_spawn.err);

  PgProcess process = res_spawn.res;
  PG_ASSERT(process.stdin_pipe.fd);

  PG_ASSERT(0 == pg_file_write_full_with_descriptor(process.stdin_pipe,
                                                    asm_human_readable));
  (void)pg_file_close(process.stdin_pipe);

  PgProcessExitResult res_proc = pg_process_wait(process, allocator);

  PG_ASSERT(0 == res_proc.err);
}

static void gen_mov(PgAllocator *allocator) {
  // Reg/mem-Reg.
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
          gen_helper_run_assembler(ins, allocator);
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
        gen_helper_run_assembler(ins, allocator);
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
        gen_helper_run_assembler(ins, allocator);
      }
    }
  }
}

int main() {
  // NOTE: Trivial to reduce memory usage if needed by reusing strings for file
  // paths etc.
  PgArena arena = pg_arena_make_from_virtual_mem(512 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  gen_mov(allocator);
}
