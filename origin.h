#pragma once
#include "submodules/cstd/lib.c"

typedef struct {
  PgString file_name;
  u32 line, column, file_offset;
  bool synthetic;
} Origin;

static void origin_print(Origin origin) {
  if (!origin.synthetic) {
    printf("%.*s:%" PRIu32 ":%" PRIu32 ":%" PRIu32, (i32)origin.file_name.len,
           origin.file_name.data, origin.line, origin.column,
           origin.file_offset);
  }
}
