#pragma once

#include "origin.h"

typedef enum {
  ERROR_KIND_NONE,
  ERROR_KIND_UNKNOWN_TOKEN,
  ERROR_KIND_INVALID_UTF8,
  ERROR_KIND_INVALID_LITERAL_NUMBER,
  ERROR_KIND_INVALID_KEYWORD,
  ERROR_KIND_PARSE_MISSING_PAREN_LEFT,
  ERROR_KIND_PARSE_MISSING_PAREN_RIGHT,
  ERROR_KIND_PARSE_SYSCALL_MISSING_COMMA,
  ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND,
  ERROR_KIND_PARSE_BINARY_OP_MISSING_RHS,
  ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL,
  ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE,
  ERROR_KIND_PARSE_FACTOR_MISSING_RHS,
  ERROR_KIND_PARSE_EQUALITY_MISSING_RHS,
  ERROR_KIND_PARSE_UNARY_MISSING_RHS,
  ERROR_KIND_PARSE_STATEMENT,
  ERROR_KIND_VAR_UNDEFINED,
  ERROR_KIND_VAR_SHADOWING,
  ERROR_KIND_ADDRESS_OF_RHS_NOT_ADDRESSABLE,
  ERROR_KIND_PARSE_IF_MISSING_CONDITION,
  ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK,
  ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_LEFT,
  ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT,
  ERROR_KIND_PARSE_BLOCK_MISSING_STATEMENT,
  ERROR_KIND_PARSE_ASSERT_MISSING_EXPRESSION,
  ERROR_KIND_PARSE_PRINTLN_MISSING_EXPRESSION,
  ERROR_KIND_WRONG_ARGS_COUNT,
  ERROR_KIND_MALFORMED_AST,
  ERROR_KIND_TYPE_MISMATCH,
} ErrorKind;

typedef struct {
  ErrorKind kind;
  PG_PAD(4);
  Origin origin;
  PgString src_span;
  PgString src;
  PgString explanation;
} Error;
PG_DYN(Error) ErrorDyn;

static void err_print_src_span(PgString src, PgString src_span, PgWriter *w,
                               PgAllocator *allocator) {
  PG_ASSERT(src.data <= src_span.data);

  u64 excerpt_start = (u64)(src_span.data - src.data);
  u64 excerpt_end = (u64)src_span.data - (u64)src.data + src_span.len;
  i64 start = (i64)excerpt_start;

  while (start > 0 && '\n' != PG_SLICE_AT(src, start)) {
    start -= 1;
  }
  PG_ASSERT(start >= 0);
  PG_ASSERT((u64)start < src.len);

  u64 end = excerpt_end;
  while (end < src.len && '\n' != PG_SLICE_AT(src, end)) {
    end += 1;
  }
  PG_ASSERT((u64)start < end);
  PG_ASSERT(end <= src.len);
  PG_ASSERT((u64)start <= excerpt_start);
  PG_ASSERT(excerpt_end <= end);

  // TODO: Limit context length?

  PgString excerpt_before =
      pg_string_trim_space_left(PG_SLICE_RANGE(src, (u64)start, excerpt_start));
  PgString excerpt = PG_SLICE_RANGE(src, excerpt_start, excerpt_end);
  PgString excerpt_after =
      pg_string_trim_space_right(PG_SLICE_RANGE(src, excerpt_end, end));

  (void)pg_writer_write_full(w, excerpt_before, allocator);
  (void)pg_writer_write_full(w, PG_S("\x1B[4m"), allocator);
  (void)pg_writer_write_full(w, excerpt, allocator);
  (void)pg_writer_write_full(w, PG_S("\x1B[0m"), allocator);
  (void)pg_writer_write_full(w, excerpt_after, allocator);
}

static void error_print(Error err, PgWriter *w, PgAllocator *allocator) {
  switch (err.kind) {
  case ERROR_KIND_NONE:
    PG_ASSERT(0);
  case ERROR_KIND_UNKNOWN_TOKEN:
    (void)pg_writer_write_full(w, PG_S("unknown token"), allocator);
    break;
  case ERROR_KIND_INVALID_UTF8:
    (void)pg_writer_write_full(w, PG_S("invalid utf8"), allocator);
    break;
  case ERROR_KIND_INVALID_LITERAL_NUMBER:
    (void)pg_writer_write_full(w, PG_S("invalid number literal"), allocator);
    break;
  case ERROR_KIND_INVALID_KEYWORD:
    (void)pg_writer_write_full(w, PG_S("invalid keyword"), allocator);
    break;
  case ERROR_KIND_PARSE_MISSING_PAREN_LEFT:
    (void)pg_writer_write_full(w, PG_S("missing left parenthesis"), allocator);
    break;
  case ERROR_KIND_PARSE_MISSING_PAREN_RIGHT:
    (void)pg_writer_write_full(w, PG_S("missing right parenthesis"), allocator);
    break;
  case ERROR_KIND_PARSE_SYSCALL_MISSING_COMMA:
    (void)pg_writer_write_full(w, PG_S("missing comma in syscall arguments"),
                               allocator);
    break;
  case ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND:
    (void)pg_writer_write_full(w, PG_S("missing syscall argument"), allocator);
    break;
  case ERROR_KIND_PARSE_BINARY_OP_MISSING_RHS:
    (void)pg_writer_write_full(
        w, PG_S("missing second operand in binary operation"), allocator);
    break;
  case ERROR_KIND_PARSE_STATEMENT:
    (void)pg_writer_write_full(w, PG_S("failed to parse statement"), allocator);
    break;
  case ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL:
    (void)pg_writer_write_full(
        w, PG_S("missing := in variable declaration after variable name"),
        allocator);
    break;
  case ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE:
    (void)pg_writer_write_full(w, PG_S("missing value in variable declaration"),
                               allocator);
    break;
  case ERROR_KIND_PARSE_FACTOR_MISSING_RHS:
    (void)pg_writer_write_full(
        w, PG_S("missing right operand in -/+ operation"), allocator);
    break;
  case ERROR_KIND_PARSE_EQUALITY_MISSING_RHS:
    (void)pg_writer_write_full(
        w, PG_S("missing right operand in !=/= comparison"), allocator);
    break;
  case ERROR_KIND_PARSE_UNARY_MISSING_RHS:
    (void)pg_writer_write_full(
        w, PG_S("missing right operand in !/-/& operation"), allocator);
    break;
  case ERROR_KIND_VAR_UNDEFINED:
    (void)pg_writer_write_full(w, PG_S("undefined variable"), allocator);
    break;
  case ERROR_KIND_VAR_SHADOWING:
    (void)pg_writer_write_full(w, PG_S("shadowed variable"), allocator);
    break;
  case ERROR_KIND_ADDRESS_OF_RHS_NOT_ADDRESSABLE:
    (void)pg_writer_write_full(
        w, PG_S("trying to take address of something that is not addressable"),
        allocator);
    break;
  case ERROR_KIND_PARSE_IF_MISSING_CONDITION:
    (void)pg_writer_write_full(w, PG_S("missing if condition"), allocator);
    break;
  case ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK:
    (void)pg_writer_write_full(w, PG_S("missing if-then block"), allocator);
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_LEFT:
    (void)pg_writer_write_full(w, PG_S("missing '{' at the start of block"),
                               allocator);
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT:
    (void)pg_writer_write_full(w, PG_S("missing '}' at the end of block"),
                               allocator);
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_STATEMENT:
    (void)pg_writer_write_full(w, PG_S("missing statement in block"),
                               allocator);
    break;
  case ERROR_KIND_PARSE_ASSERT_MISSING_EXPRESSION:
    (void)pg_writer_write_full(w, PG_S("missing assert expression"), allocator);
    break;
  case ERROR_KIND_PARSE_PRINTLN_MISSING_EXPRESSION:
    (void)pg_writer_write_full(w, PG_S("missing println expression"),
                               allocator);
    break;
  case ERROR_KIND_WRONG_ARGS_COUNT:
    (void)pg_writer_write_full(w, PG_S("wrong argument count"), allocator);
    break;

  case ERROR_KIND_MALFORMED_AST:
    (void)pg_writer_write_full(w, PG_S("malformed ast"), allocator);
    break;

  case ERROR_KIND_TYPE_MISMATCH:
    (void)pg_writer_write_full(w, PG_S("mismatched types: "), allocator);
    (void)pg_writer_write_full(w, err.explanation, allocator);
    break;

  default:
    PG_ASSERT(0);
  }

  (void)pg_writer_write_full(w, PG_S(": "), allocator);
  err_print_src_span(err.src, err.src_span, w, allocator);
  (void)pg_writer_write_full(w, PG_S("\n"), allocator);
}

[[nodiscard]]
static int err_compare_errors_by_origin_offset(const void *v_a,
                                               const void *v_b) {
  const Error *a = v_a;
  const Error *b = v_b;

  return a->origin.file_offset_start < b->origin.file_offset_start ? -1 : 1;
}
