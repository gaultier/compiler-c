#include "submodules/cstd/lib.c"
#include <dirent.h>
#include <sys/types.h>

typedef struct {
  PgProcessStatus process_status;
  PgError err;
} TestResult;

[[nodiscard]]
static TestResult test_run(PgString dir_name, PgString file_name,
                           bool err_expected) {
  TestResult res = {0};

  PgArena arena = pg_arena_make_from_virtual_mem(1 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgString file_path = pg_path_join(dir_name, file_name, allocator);

  PgProcessSpawnOptions options = {
      .stdout_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
      .stderr_capture = PG_CHILD_PROCESS_STD_IO_PIPE,
  };
  // Compile.
  {
    PgString args[] = {/*PG_S("-v"),*/ file_path};
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

    // err_expected | stdout_empty | res
    // 0                 0         | 0
    // 0                 1         | 1
    // 1                 0         | 1
    // 1                 1         | 0
    // => xor

    bool stdout_ok =
        err_expected ^ pg_string_is_empty(res.process_status.stdout_captured);
    if (!stdout_ok) {
      res.err = PG_ERR_INVALID_VALUE;
      return res;
    }

    volatile PgString foo = res.process_status.stderr_captured;
    (void)foo;
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

    PgString stem = pg_path_stem(file_path);
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
int main() {

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
      TestResult test_res = test_run(dir_name, file_name, err_expected);
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
      TestResult test_res = test_run(dir_name, file_name, err_expected);
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

  return failed;
}
