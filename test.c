#include "submodules/cstd/lib.c"
#include <dirent.h>
#include <sys/types.h>

static void test_run(PgString dir_name, PgString file_name) {
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
    PG_ASSERT(0 == res_wait.err);

    PgProcessStatus status = res_wait.res;
    PG_ASSERT(0 == status.exit_status);
    PG_ASSERT(0 == status.signal);
    PG_ASSERT(status.exited);
    PG_ASSERT(!status.signaled);
    PG_ASSERT(!status.core_dumped);
    PG_ASSERT(!status.stopped);

    PG_ASSERT(pg_string_is_empty(status.stdout_captured));
    PG_ASSERT(pg_string_is_empty(status.stderr_captured));
  }
  // Run.
  {
    PgString args[] = {0};
    PgStringSlice args_slice = {.data = args, .len = PG_STATIC_ARRAY_LEN(args)};

    PgString stem = pg_path_stem(file_name);
    PgString exe_path = pg_string_concat(stem, PG_S(".bin"), allocator);

    PgProcessResult res_spawn =
        pg_process_spawn(exe_path, args_slice, options, allocator);
    PG_ASSERT(0 == res_spawn.err);

    PgProcess process = res_spawn.res;

    PgProcessExitResult res_wait = pg_process_wait(process, allocator);
    PG_ASSERT(0 == res_wait.err);

    PgProcessStatus status = res_wait.res;
    PG_ASSERT(0 == status.exit_status);
    PG_ASSERT(0 == status.signal);
    PG_ASSERT(status.exited);
    PG_ASSERT(!status.signaled);
    PG_ASSERT(!status.core_dumped);
    PG_ASSERT(!status.stopped);

    // PG_ASSERT(pg_string_is_empty(status.stdout_captured));
    // PG_ASSERT(pg_string_is_empty(status.stderr_captured));
  }
}

int main() {
  // TODO: Extract OS-independent API into cstd.

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

    test_run(dir_name, file_name);
    printf("OK %.*s\n", (i32)file_name.len, file_name.data);
  }
}
