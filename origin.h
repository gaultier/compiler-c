#pragma once
#include "submodules/cstd/lib.c"

typedef struct {
  PgString file_path;
  u32 line, column, file_offset_start;
} Origin;

static void origin_write(PgWriter *w, Origin origin, PgAllocator *allocator) {
  PG_ASSERT(0 == pg_writer_write_full(w, origin.file_path, allocator));
  PG_ASSERT(0 == pg_writer_write_full(w, PG_S(":"), allocator));
  PG_ASSERT(0 == pg_writer_write_u64_as_string(w, origin.line, allocator));
  PG_ASSERT(0 == pg_writer_write_full(w, PG_S(":"), allocator));
  PG_ASSERT(0 == pg_writer_write_u64_as_string(w, origin.column, allocator));
  PG_ASSERT(0 == pg_writer_write_full(w, PG_S(":"), allocator));
  PG_ASSERT(0 == pg_writer_write_u64_as_string(w, origin.file_offset_start,
                                               allocator));
}
