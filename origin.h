#pragma once
#include "submodules/cstd/lib.c"

typedef struct {
  PgString file_path;
  u32 line, column, file_offset_start;
} Origin;

static void origin_print(Origin origin) {
  PG_ASSERT(origin.line);
  printf("%.*s:%" PRIu32 ":%" PRIu32 ":%" PRIu32, (i32)origin.file_path.len,
         origin.file_path.data, origin.line, origin.column,
         origin.file_offset_start);
}
