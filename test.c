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
static Pgu8Slice test_helper_cc_assemble(Amd64Instruction ins,
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

  FILE *process_stdin = fdopen(process.stdin_pipe.fd, "w");
  PG_ASSERT(process_stdin);

  amd64_print_instruction(process_stdin, ins, false);
  fclose(process_stdin);

  amd64_print_instruction(stderr, ins, false);
  fprintf(stderr, "\n");

  PgProcessExitResult res_wait = pg_process_wait(process, allocator);
  PG_ASSERT(!res_wait.err);

  PG_ASSERT(0 == res_wait.res.exit_status);
  PG_ASSERT(0 == res_wait.res.signal);
  PG_ASSERT(res_wait.res.exited);
  PG_ASSERT(!res_wait.res.signaled);
  PG_ASSERT(!res_wait.res.core_dumped);
  PG_ASSERT(!res_wait.res.stopped);
  if (!pg_string_is_empty(res_wait.res.stderr_captured)) {
    PG_ASSERT(pg_string_contains(res_wait.res.stderr_captured,
                                 PG_S("cannot find entry symbol")));
  }
  PG_ASSERT(!pg_string_is_empty(res_wait.res.stdout_captured));

  return res_wait.res.stdout_captured;
}

typedef struct {
  Register reg_a, reg_b;
  AsmOperandSize size;
  PgAllocator *allocator;
} TestAssemblerTask;

static int test_helper_task_assembler_run(void *data) {
  TestAssemblerTask *task = data;
  PG_ASSERT(task);
  PG_ASSERT(task->allocator);

  printf("task size=%u reg_a=%u reg_b=%u\n", task->size, task->reg_a.value,
         task->reg_b.value);

  Amd64Instruction ins = {
      .kind = AMD64_INSTRUCTION_KIND_MOV,
      .lhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = task->reg_a,
              .size = task->size,
          },
      .rhs =
          (Amd64Operand){
              .kind = AMD64_OPERAND_KIND_REGISTER,
              .u.reg = task->reg_b,
              .size = task->size,
          },

  };

  Pgu8Dyn sb = {0};
  amd64_encode_instruction_mov(&sb, ins, task->allocator);
  Pgu8Slice actual = PG_DYN_SLICE(Pgu8Slice, sb);

  Pgu8Slice expected = test_helper_cc_assemble(ins, task->allocator);
  PG_ASSERT(pg_string_eq(actual, expected));

  return 0;
}

static void test_assembler_amd64_mov() {
  PgArena arena = pg_arena_make_from_virtual_mem(4 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgThreadPoolResult pool_res = pg_thread_pool_make(4 /* FIXME */, allocator);
  PG_ASSERT(!pool_res.err);
  PgThreadPool pool = pool_res.res;

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

        TestAssemblerTask *task = PG_NEW(TestAssemblerTask, allocator);
        task->reg_a = reg_a;
        task->reg_b = reg_b;
        task->size = size;
        task->allocator = pg_heap_allocator();

        pg_thread_pool_enqueue_task(&pool, test_helper_task_assembler_run, task,
                                    allocator);
      }
    }
  }

  pg_thread_pool_wait(&pool);
}

int main() {
  test_assembler_amd64_mov();
  test_compile_and_run_samples();
}
