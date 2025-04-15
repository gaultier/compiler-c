#pragma once

#include "origin.h"
typedef enum {
  ERROR_KIND_NONE,
  ERROR_KIND_LEX_UNKNOWN_TOKEN,
  ERROR_KIND_LEX_INVALID_UTF8,
  ERROR_KIND_LEX_INVALID_LITERAL_NUMBER,
  ERROR_KIND_LEX_INVALID_KEYWORD,
} ErrorKind;

typedef struct {
  ErrorKind kind;
  Origin origin;
} Error;
PG_SLICE(Error) ErrorSlice;
PG_DYN(Error) ErrorDyn;

static void error_print(Error err) {
  switch (err.kind) {
  case ERROR_KIND_NONE:
    PG_ASSERT(0);
  case ERROR_KIND_LEX_UNKNOWN_TOKEN:
    printf("unknown token\n");
    break;
  case ERROR_KIND_LEX_INVALID_UTF8:
    printf("invalid utf8\n");
    break;
  case ERROR_KIND_LEX_INVALID_LITERAL_NUMBER:
    printf("invalid number literal\n");
    break;
  case ERROR_KIND_LEX_INVALID_KEYWORD:
    printf("invalid keyword\n");
    break;
  default:
    PG_ASSERT(0);
  }
}
