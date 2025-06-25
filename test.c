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

// Load all files under `test_asm/` and check that `our_assembler(xxx.s) ==
// xxx.bin` i.e. that the output of our assembler is the same as clang's. NOTE:
// All files under `test_asm/` are generated by `./test_asm_gen.sh`.
static void test_asm() {
  PgArena arena = pg_arena_make_from_virtual_mem(16 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  {
    PgString dir_name = PG_S("test_amd64");
    DIR *dir = opendir("test_amd64");
    if (!dir) {
      fprintf(stderr, "failed to open directory %.*s: %d\n", (i32)dir_name.len,
              dir_name.data, pg_os_get_last_error());
      exit(pg_os_get_last_error());
    }

    struct dirent *dir_it = nullptr;

    while ((dir_it = readdir(dir))) {
      PgString file_name = pg_cstr_to_string(dir_it->d_name);
      // Not a regular file.
      if (DT_REG != dir_it->d_type) {
        continue;
      }
      if (!pg_string_ends_with(file_name, PG_S(".bin"))) {
        continue;
      }

      PgString expected = {0};
      PgString path_bin = pg_path_join(dir_name, file_name, allocator);
      {
        PgStringResult read_res =
            pg_file_read_full_from_path(path_bin, allocator);
        PG_ASSERT(0 == read_res.err);
        expected = read_res.res;
      }

      Amd64Instruction ins = {0};
      {
        PgString path_ins =
            pg_string_concat(pg_path_stem(path_bin), PG_S(".ins"), allocator);
        PgStringResult read_res =
            pg_file_read_full_from_path(path_ins, allocator);
        PG_ASSERT(0 == read_res.err);
        PG_ASSERT(sizeof(Amd64Instruction) == read_res.res.len);
        ins = *(Amd64Instruction *)(void *)read_res.res.data;
      }
      PgString asm_human_readable = {0};
      {
        PgString path_s =
            pg_string_concat(pg_path_stem(path_bin), PG_S(".s"), allocator);
        PgStringResult read_res =
            pg_file_read_full_from_path(path_s, allocator);
        PG_ASSERT(0 == read_res.err);
        asm_human_readable = pg_string_trim_space(read_res.res);
      }

      AsmProgram program = {0};
      Pgu8Dyn sb = pg_string_builder_make(256, allocator);
      amd64_encode_instruction(&program, &sb, ins, allocator);
      PgString actual = PG_DYN_SLICE(PgString, sb);

      bool eq = pg_bytes_eq(actual, expected);
      if (eq) {
        printf("OK %.*s %.*s\n", (i32)path_bin.len, path_bin.data,
               (i32)asm_human_readable.len, asm_human_readable.data);
      } else {
        PgString expected_str =
            pg_bytes_to_hex_string(expected, ' ', allocator);
        PgString actual_str = pg_bytes_to_hex_string(actual, ' ', allocator);
        fprintf(stderr, "FAIL %.*s %.*s\nExpected: %.*s\nActual: %.*s\n\n",
                (i32)path_bin.len, path_bin.data, (i32)asm_human_readable.len,
                asm_human_readable.data, (i32)expected_str.len,
                expected_str.data, (i32)actual_str.len, actual_str.data);
        PG_ASSERT(0);
      }
    }
  }
}

int main() {
  test_asm();
  test_compile_and_run_samples();
}
