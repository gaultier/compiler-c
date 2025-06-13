#include "submodules/cstd/lib.c"
#include <dirent.h>
#include <sys/types.h>

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
    PgProcessResult res_spawn =
        pg_process_spawn(PG_S("./main.bin"), args_slice, options, allocator);
    PG_ASSERT(0 == res_spawn.err);

    PgProcess process = res_spawn.res;

    PgProcessExitResult res_wait = pg_process_wait(process, allocator);
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

    // err_expected | stderr_empty | ok
    // 0                 0         | 0
    // 0                 1         | 1
    // 1                 0         | 1
    // 1                 1         | 0
    // => xor

    bool stderr_ok =
        err_expected ^ pg_string_is_empty(res.process_status.stderr_captured);
    if (!stderr_ok) {
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

    PgProcessExitResult res_wait = pg_process_wait(process, allocator);
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

    // Could be ok depending on the test case.
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

[[nodiscard]]
static PgProcess test_helper_cc_assemble_spawn(Amd64Instruction ins,
                                               PgAllocator *allocator) {

  PgString args[] = {
      PG_S("-mllvm"),    PG_S("--x86-asm-syntax=intel"),
      PG_S("-x"),        PG_S("assembler"),
      PG_S("-nostdlib"), PG_S("-Wl,--oformat=binary"),
      PG_S("-o"),        PG_S("/dev/stdout"),
      PG_S("-"),
  };
  PgStringSlice args_slice = {.data = args, .len = PG_STATIC_ARRAY_LEN(args)};

  PgProcessSpawnOptions options = {
      .stdin_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
      .stdout_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
      .stderr_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
  };
  PgProcessResult res_spawn =
      pg_process_spawn(PG_S("clang"), args_slice, options, allocator);
  PG_ASSERT(0 == res_spawn.err);

  PgProcess process = res_spawn.res;
  PG_ASSERT(process.stdin_pipe.fd);

  FILE *process_stdin = fdopen(process.stdin_pipe.fd, "w");
  PG_ASSERT(process_stdin);

  amd64_print_instruction(process_stdin, ins, false);
  fclose(process_stdin);

  amd64_print_instruction(stderr, ins, false);
  fprintf(stderr, "\n");

  return process;
}

typedef struct {
  Pgu8Dyn expected;
  Pgu8Slice actual;
  PgString actual_human_readable;
  PgProcess process;
  PgAllocator *allocator;
} TestAssemblerData;

static void
test_helper_cc_assemble_check_on_child_proc_read(PgAioTask *task, PgError err,
                                                 Pgu8Slice read_data) {

  PG_ASSERT(task);
  PG_ASSERT(task->data);
  TestAssemblerData *data = task->data;

  PG_DYN_APPEND_SLICE(&data->expected, read_data, data->allocator);

  if (PG_ERR_EOF == err) {
    PG_ASSERT(
        pg_string_eq(data->actual, PG_DYN_SLICE(Pgu8Slice, data->expected)));

    (void)pg_aio_loop_read_stop(task);
    (void)pg_process_wait(data->process, data->allocator);
  }
}

static void test_assembler_amd64_mov() {
  PgArena arena = pg_arena_make_from_virtual_mem(16 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgAioLoopResult loop_res = pg_aio_loop_make();
  PG_ASSERT(!loop_res.err);
  PgAioLoop loop = loop_res.res;

  AsmOperandSize sizes[4] = {
      ASM_OPERAND_SIZE_1,
      ASM_OPERAND_SIZE_2,
      ASM_OPERAND_SIZE_4,
      ASM_OPERAND_SIZE_8,
  };

  // Reg-reg.
  for (u8 i = 1; i < 14; i++) {
    Register reg_a = {i};

    for (u8 j = 1; j < 14; j++) {
      Register reg_b = {j};

      for (u8 k = 0; k < PG_STATIC_ARRAY_LEN(sizes); k++) {
        AsmOperandSize size =
            PG_C_ARRAY_AT(sizes, PG_STATIC_ARRAY_LEN(sizes), k);

        Amd64Instruction ins = {
            .kind = AMD64_INSTRUCTION_KIND_MOV,
            .lhs =
                (Amd64Operand){
                    .kind = AMD64_OPERAND_KIND_REGISTER,
                    .u.reg = reg_a,
                    .size = size,
                },
            .rhs =
                (Amd64Operand){
                    .kind = AMD64_OPERAND_KIND_REGISTER,
                    .u.reg = reg_b,
                    .size = size,
                },

        };

        Pgu8Dyn sb = {0};
        amd64_encode_instruction_mov(&sb, ins, allocator);
        Pgu8Slice actual = PG_DYN_SLICE(Pgu8Slice, sb);

        PgProcess proc = test_helper_cc_assemble_spawn(ins, allocator);

        TestAssemblerData *data = PG_NEW(TestAssemblerData, allocator);
        data->actual = actual;
        data->actual_human_readable = PG_S("todo");
        data->process = proc;
        data->allocator = allocator;

        PgAioTask *task =
            pg_aio_task_make_for_file(&loop, proc.stdout_pipe, allocator);
        task->data = data;

        PgError err = pg_aio_loop_read(
            task, test_helper_cc_assemble_check_on_child_proc_read);
        PG_ASSERT(!err);
      }
    }
    PgError err = pg_aio_loop_wait(&loop, 1000);
    PG_ASSERT(!err);
  }

  PgError err = pg_aio_loop_wait(&loop, 1000);
  PG_ASSERT(!err);
}

int main() {
  test_assembler_amd64_mov();
  test_compile_and_run_samples();
}
