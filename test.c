#include "submodules/cstd/lib.c"
#include <sys/dir.h>

#include "amd64.h"

typedef struct {
  PgProcessStatus process_status;
  PgError err;
  PgString file_path;
} CompileAndRunResult;

[[nodiscard]]
static CompileAndRunResult test_run(PgString dir_name, PgString file_name,
                                    bool err_expected) {
  CompileAndRunResult res = {0};

  PgArena arena = pg_arena_make_from_virtual_mem(1 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  res.file_path = pg_path_join(dir_name, file_name, allocator);

  PgProcessSpawnOptions options = {
      .stdout_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
      .stderr_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
  };
  // Compile.
  {
    PgString args[] = {/*PG_S("-v"),*/ res.file_path};
    PgStringSlice args_slice = {.data = args, .len = PG_STATIC_ARRAY_LEN(args)};
    PgProcessResult res_spawn = pg_process_spawn(
        PG_S("./main_release.bin"), args_slice, options, allocator);
    PG_ASSERT(0 == res_spawn.err);

    PgProcess process = res_spawn.res;

    PgProcessExitResult res_wait = pg_process_wait(process, 0, 512, allocator);
    if ((res.err = res_wait.err)) {
      return res;
    }

    res.process_status = res_wait.res;
    if (!err_expected && 0 != res.process_status.exit_status) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (0 != res.process_status.signal) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (!res.process_status.exited) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (res.process_status.signaled) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (res.process_status.core_dumped) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (res.process_status.stopped) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }

    if (!pg_string_is_empty(res.process_status.stdout_captured)) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }

    // err_expected | stderr_empty | has_value
    // 0                 0         | 0
    // 0                 1         | 1
    // 1                 0         | 1
    // 1                 1         | 0
    // => xor

    bool stderr_opt =
        err_expected ^ pg_string_is_empty(res.process_status.stderr_captured);
    if (!stderr_opt) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }

    if (err_expected) {
      return res;
    }
  }
  // Run.
  {
    PG_ASSERT(!err_expected);

    PgString args[] = {0};
    PgStringSlice args_slice = {.data = args, .len = PG_STATIC_ARRAY_LEN(args)};

    PgString stem = pg_path_stem(res.file_path);
    PgString exe_name = pg_string_concat(stem, PG_S(".bin"), allocator);
    PgString exe_path = pg_path_join(PG_S("."), exe_name, allocator);

    PgProcessResult res_spawn =
        pg_process_spawn(exe_path, args_slice, options, allocator);
    PG_ASSERT(0 == res_spawn.err);

    PgProcess process = res_spawn.res;

    PgProcessExitResult res_wait = pg_process_wait(process, 64, 0, allocator);
    if ((res.err = res_wait.err)) {
      return res;
    }

    res.process_status = res_wait.res;
    if (0 != res.process_status.exit_status) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (0 != res.process_status.signal) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (!res.process_status.exited) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (res.process_status.signaled) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (res.process_status.core_dumped) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (res.process_status.stopped) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }

    // Could be has_value depending on the test case.
    // Need code comments to know what output to expect.
#if 0
    if (!pg_string_is_empty(res.process_status.stdout_captured)) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
    if (!pg_string_is_empty(res.process_status.stderr_captured)) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }
#endif
  }

  return res;
}

// TODO: Extract OS-independent API into cstd.
static void test_compile_and_run_samples() {

  bool failed = false;
  {
    PgString dir_name = PG_S("testdata");
    DIR *dir = opendir("testdata");
    if (!dir) {
      fprintf(stderr, "failed to open directory %s: %d\n", "testdata",
              pg_os_get_last_error());
      exit(pg_os_get_last_error());
    }

    struct dirent *dir_it = nullptr;

    while ((dir_it = readdir(dir))) {
      PgString file_name = pg_cstr_to_string(dir_it->d_name);
      // Not a regular file.
      if (DT_REG != dir_it->d_type) {
        continue;
      }
      if (!pg_string_ends_with(file_name, PG_S(".unicorn"))) {
        continue;
      }

      bool err_expected = false;
      CompileAndRunResult test_res =
          test_run(dir_name, file_name, err_expected);
      if (!test_res.err) {
        printf("OK %.*s\n", (i32)file_name.len, file_name.data);
        continue;
      }

      failed = true;
      fprintf(stderr, "FAIL %.*s\n", (i32)file_name.len, file_name.data);
      __builtin_dump_struct(&test_res, printf);
      fprintf(stderr, "stdout=%.*s\n",
              (i32)test_res.process_status.stdout_captured.len,
              test_res.process_status.stdout_captured.data);
      fprintf(stderr, "stderr=%.*s\n",
              (i32)test_res.process_status.stderr_captured.len,
              test_res.process_status.stderr_captured.data);
    }
  }
  {
    PgString dir_name = PG_S("err_testdata");
    DIR *dir = opendir("err_testdata");
    if (!dir) {
      fprintf(stderr, "failed to open directory %s: %d\n", "err_testdata",
              pg_os_get_last_error());
      exit(pg_os_get_last_error());
    }

    struct dirent *dir_it = nullptr;

    while ((dir_it = readdir(dir))) {
      PgString file_name = pg_cstr_to_string(dir_it->d_name);
      // Not a regular file.
      if (DT_REG != dir_it->d_type) {
        continue;
      }
      if (!pg_string_ends_with(file_name, PG_S(".unicorn"))) {
        continue;
      }

      bool err_expected = true;
      CompileAndRunResult test_res =
          test_run(dir_name, file_name, err_expected);
      if (!test_res.err) {
        printf("OK %.*s\n", (i32)test_res.file_path.len,
               test_res.file_path.data);
        continue;
      }

      failed = true;
      fprintf(stderr, "FAIL %.*s\n", (i32)test_res.file_path.len,
              test_res.file_path.data);
      __builtin_dump_struct(&test_res, printf);
      fprintf(stderr, "stdout=%.*s\n",
              (i32)test_res.process_status.stdout_captured.len,
              test_res.process_status.stdout_captured.data);
      fprintf(stderr, "stderr=%.*s\n",
              (i32)test_res.process_status.stderr_captured.len,
              test_res.process_status.stderr_captured.data);
    }
  }

  PG_ASSERT(!failed);
}

static void write_instruction(Amd64Instruction ins, PgWriter *writer_asm_text) {
  amd64_print_instruction(ins, false, writer_asm_text, nullptr);
  (void)pg_writer_write_full(writer_asm_text, PG_S("\n"), nullptr);
}

[[nodiscard]]
static PgString run_assembler(PgString in, PgAllocator *allocator) {
  PgString args[] = {
      PG_S("-mllvm"),
      PG_S("--x86-asm-syntax=intel"),
      PG_S("-x"),
      PG_S("assembler"),
      PG_S("-O0"),
      PG_S("-nostdlib"),
      PG_S("-Wl,--oformat=binary"),
      PG_S("-o"),
      PG_S("/dev/stdout"), // FIXME: Windows.
      PG_S("-"),
  };
  PgStringSlice args_slice = {.data = args, .len = PG_STATIC_ARRAY_LEN(args)};

  PgProcessSpawnOptions options = {
      .stdin_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
      .stdout_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
  };
  PgProcessResult res_spawn =
      pg_process_spawn(PG_S("clang"), args_slice, options, allocator);
  PG_ASSERT(0 == res_spawn.err);

  PgProcess process = res_spawn.res;
  PG_ASSERT(0 == pg_file_write_full_with_descriptor(process.stdin_pipe, in));
  (void)pg_file_close(process.stdin_pipe);

  PgStringResult read_res = pg_file_read_full_from_descriptor_until_eof(
      process.stdout_pipe, 1 * PG_MiB, allocator);
  PG_ASSERT(0 == read_res.err);
  PG_ASSERT(read_res.res.len);
  PgProcessExitResult res_proc =
      pg_process_wait(process, 64 * PG_MiB, 0, allocator);

  PG_ASSERT(0 == res_proc.err);
  PG_ASSERT(0 == res_proc.res.exit_status);

  return read_res.res;
}

static void gen_lea(PgWriter *writer_asm_text,
                    Amd64InstructionDyn *instructions) {
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
          *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
          write_instruction(ins, writer_asm_text);
        }
      }
    }
  }
}

static void gen_mov(PgWriter *writer_asm_text,
                    Amd64InstructionDyn *instructions) {
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
          *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
          write_instruction(ins, writer_asm_text);

          // Swap operands.
          {
            Amd64Operand tmp = ins.lhs;
            ins.lhs = ins.rhs;
            ins.rhs = tmp;

            *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
            write_instruction(ins, writer_asm_text);
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
        *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
        write_instruction(ins, writer_asm_text);
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
        *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
        write_instruction(ins, writer_asm_text);
      }
    }
  }
}

static void gen_add(PgWriter *writer_asm_text,
                    Amd64InstructionDyn *instructions) {
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
          *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
          write_instruction(ins, writer_asm_text);

          // Swap operands.
          {
            Amd64Operand tmp = ins.lhs;
            ins.lhs = ins.rhs;
            ins.rhs = tmp;
            *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
            write_instruction(ins, writer_asm_text);
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
        *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
        write_instruction(ins, writer_asm_text);
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
        *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
        write_instruction(ins, writer_asm_text);
      }
    }
  }
}

static void gen_sub(PgWriter *writer_asm_text,
                    Amd64InstructionDyn *instructions) {
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
          ins.kind = AMD64_INSTRUCTION_KIND_SUB;
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
          *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
          write_instruction(ins, writer_asm_text);

          // Swap operands.
          {
            Amd64Operand tmp = ins.lhs;
            ins.lhs = ins.rhs;
            ins.rhs = tmp;
            *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
            write_instruction(ins, writer_asm_text);
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
        ins.kind = AMD64_INSTRUCTION_KIND_SUB;
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
        *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
        write_instruction(ins, writer_asm_text);
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
        ins.kind = AMD64_INSTRUCTION_KIND_SUB;
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
        *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
        write_instruction(ins, writer_asm_text);
      }
    }
  }
}

static void gen_cmp(PgWriter *writer_asm_text,
                    Amd64InstructionDyn *instructions) {
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
          ins.kind = AMD64_INSTRUCTION_KIND_CMP;
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
          *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
          write_instruction(ins, writer_asm_text);

          // Swap operands.
          {
            Amd64Operand tmp = ins.lhs;
            ins.lhs = ins.rhs;
            ins.rhs = tmp;
            *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
            write_instruction(ins, writer_asm_text);
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
        ins.kind = AMD64_INSTRUCTION_KIND_CMP;
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
        *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
        write_instruction(ins, writer_asm_text);
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
        ins.kind = AMD64_INSTRUCTION_KIND_CMP;
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
        *PG_DYN_PUSH_WITHIN_CAPACITY(instructions) = ins;
        write_instruction(ins, writer_asm_text);
      }
    }
  }
}

static void test_asm() {
  PgArena arena = pg_arena_make_from_virtual_mem(128 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgWriter writer_asm_text =
      pg_writer_make_string_builder(4 * PG_MiB, allocator);

  Amd64InstructionDyn instructions = {0};
  PG_DYN_ENSURE_CAP(&instructions, 64'000, allocator);

  PG_ASSERT(0 == pg_writer_write_full(&writer_asm_text,
                                            PG_S(".globl _start\n _start:\n"),
                                            nullptr));

  gen_cmp(&writer_asm_text, &instructions);
  gen_sub(&writer_asm_text, &instructions);
  gen_add(&writer_asm_text, &instructions);
  gen_lea(&writer_asm_text, &instructions);
  gen_mov(&writer_asm_text, &instructions);

  PgString asm_s = PG_DYN_SLICE(PgString, writer_asm_text.u.bytes);
  PgString expected = run_assembler(asm_s, allocator);

  Pgu8Dyn sb = {0};
  // Size should be the same but in the event that output differs from the
  // oracle, at least avoid reallocating the big buffer.
  PG_DYN_ENSURE_CAP(&sb, expected.len + 1024, allocator);

  Pgu64Dyn ins_offsets = {0};
  PG_DYN_ENSURE_CAP(&ins_offsets, instructions.len, allocator);

  AsmProgram program = {0};
  for (u64 i = 0; i < instructions.len; i++) {
    Amd64Instruction ins = PG_SLICE_AT(instructions, i);
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_offsets) = sb.len;
    amd64_encode_instruction(&program, &sb, ins, allocator);
  }
  PgString actual = PG_DYN_SLICE(PgString, sb);

  bool eq = pg_bytes_eq(actual, expected);
  if (eq) {
    printf("OK AMD64 (%lu forms)\n", instructions.len);
    return;
  }

  i64 first_differing_byte_idx = 0;
  for (u64 i = 0; i < PG_MIN(actual.len, expected.len); i++) {
    u8 byte_actual = PG_SLICE_AT(actual, i);
    u8 byte_expected = PG_SLICE_AT(expected, i);

    if (byte_actual != byte_expected) {
      first_differing_byte_idx = (i64)i;
      break;
    }
  }
  PG_ASSERT(first_differing_byte_idx >= 0);

  Pgu64RangeOption res_search_ins = pg_u64_range_search(
      PG_DYN_SLICE(Pgu64Slice, ins_offsets), (u64)first_differing_byte_idx);
  PG_ASSERT(res_search_ins.has_value);
  Pgu64Range range_ins = res_search_ins.res;

  // NOTE: The two excerpts might actually differ in length and this might
  // truncate/extend `except` by a few bytes.
  Pgu8Slice expected_excerpt =
      PG_SLICE_RANGE(expected, range_ins.start_incl, range_ins.end_excl);
  Pgu8Slice actual_excerpt =
      PG_SLICE_RANGE(actual, range_ins.start_incl, range_ins.end_excl);
  PG_ASSERT(!pg_bytes_eq(expected_excerpt, actual_excerpt));

  Amd64Instruction ins = PG_SLICE_AT(instructions, res_search_ins.res.idx);
  PgString ins_str =
      amd64_instruction_to_string_human_readable(ins, false, allocator);

  PgString expected_excerpt_hex =
      pg_bytes_to_hex_string(expected_excerpt, ' ', allocator);
  PgString actual_excerpt_hex =
      pg_bytes_to_hex_string(actual_excerpt, ' ', allocator);

  fprintf(stderr,
          "Diff: first_differing_byte_idx=%ld ins=%.*s\nexpected=%.*s\nactual= "
          " %.*s\n",
          first_differing_byte_idx, (i32)ins_str.len, ins_str.data,
          (i32)expected_excerpt_hex.len, expected_excerpt_hex.data,
          (i32)actual_excerpt_hex.len, actual_excerpt_hex.data);

  PG_ASSERT(0);
}

int main() {
  test_asm();
  test_compile_and_run_samples();
}
