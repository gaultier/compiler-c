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
  Origin origin;
  PgString src_span;
  PgString src;
  PgString explanation;
} Error;
PG_DYN(Error) ErrorDyn;

static void err_print_src_span(FILE *out, PgString src, PgString src_span) {
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

  fprintf(out, "%.*s", (i32)excerpt_before.len, excerpt_before.data);
  fprintf(out, "\x1B[4m%.*s\x1B[0m", (i32)excerpt.len, excerpt.data);
  fprintf(out, "%.*s", (i32)excerpt_after.len, excerpt_after.data);
}

static void error_print(FILE *out, Error err) {
  switch (err.kind) {
  case ERROR_KIND_NONE:
    PG_ASSERT(0);
  case ERROR_KIND_UNKNOWN_TOKEN:
    fprintf(out, "unknown token");
    break;
  case ERROR_KIND_INVALID_UTF8:
    fprintf(out, "invalid utf8");
    break;
  case ERROR_KIND_INVALID_LITERAL_NUMBER:
    fprintf(out, "invalid number literal");
    break;
  case ERROR_KIND_INVALID_KEYWORD:
    fprintf(out, "invalid keyword");
    break;
  case ERROR_KIND_PARSE_MISSING_PAREN_LEFT:
    fprintf(out, "missing left parenthesis");
    break;
  case ERROR_KIND_PARSE_MISSING_PAREN_RIGHT:
    fprintf(out, "missing right parenthesis");
    break;
  case ERROR_KIND_PARSE_SYSCALL_MISSING_COMMA:
    fprintf(out, "missing comma in syscall arguments");
    break;
  case ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND:
    fprintf(out, "missing syscall argument");
    break;
  case ERROR_KIND_PARSE_BINARY_OP_MISSING_RHS:
    fprintf(out, "missing second operand in binary operation");
    break;
  case ERROR_KIND_PARSE_STATEMENT:
    fprintf(out, "failed to parse statement");
    break;
  case ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL:
    fprintf(out, "missing := in variable declaration after variable name");
    break;
  case ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE:
    fprintf(out, "missing value in variable declaration");
    break;
  case ERROR_KIND_PARSE_FACTOR_MISSING_RHS:
    fprintf(out, "missing right operand in -/+ operation");
    break;
  case ERROR_KIND_PARSE_EQUALITY_MISSING_RHS:
    fprintf(out, "missing right operand in !=/= comparison");
    break;
  case ERROR_KIND_PARSE_UNARY_MISSING_RHS:
    fprintf(out, "missing right operand in !/-/& operation");
    break;
  case ERROR_KIND_VAR_UNDEFINED:
    fprintf(out, "undefined variable");
    break;
  case ERROR_KIND_VAR_SHADOWING:
    fprintf(out, "shadowed variable");
    break;
  case ERROR_KIND_ADDRESS_OF_RHS_NOT_ADDRESSABLE:
    fprintf(out, "trying to take address of something that is not addressable");
    break;
  case ERROR_KIND_PARSE_IF_MISSING_CONDITION:
    fprintf(out, "missing if condition");
    break;
  case ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK:
    fprintf(out, "missing if-then block");
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_LEFT:
    fprintf(out, "missing '{' at the start of block");
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT:
    fprintf(out, "missing '}' at the end of block");
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_STATEMENT:
    fprintf(out, "missing statement in block");
    break;
  case ERROR_KIND_PARSE_ASSERT_MISSING_EXPRESSION:
    fprintf(out, "missing assert expression");
    break;
  case ERROR_KIND_PARSE_PRINTLN_MISSING_EXPRESSION:
    fprintf(out, "missing println expression");
    break;
  case ERROR_KIND_WRONG_ARGS_COUNT:
    fprintf(out, "wrong argument count");
    break;

  case ERROR_KIND_MALFORMED_AST:
    fprintf(out, "malformed ast");
    break;

  case ERROR_KIND_TYPE_MISMATCH:
    fprintf(out, "mismatched types: %.*s", (i32)err.explanation.len,
            err.explanation.data);
    break;

  default:
    PG_ASSERT(0);
  }

  fprintf(out, ": ");
  err_print_src_span(out, err.src, err.src_span);
  fprintf(out, "\n");
}

[[nodiscard]]
static int err_compare_errors_by_origin_offset(const void *v_a,
                                               const void *v_b) {
  const Error *a = v_a;
  const Error *b = v_b;

  return a->origin.file_offset_start < b->origin.file_offset_start ? -1 : 1;
}
