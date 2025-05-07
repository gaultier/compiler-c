#pragma once

#include "origin.h"
typedef enum {
  ERROR_KIND_NONE,
  ERROR_KIND_LEX_UNKNOWN_TOKEN,
  ERROR_KIND_LEX_INVALID_UTF8,
  ERROR_KIND_LEX_INVALID_LITERAL_NUMBER,
  ERROR_KIND_LEX_INVALID_KEYWORD,
  ERROR_KIND_PARSE_SYSCALL_MISSING_LEFT_PAREN,
  ERROR_KIND_PARSE_SYSCALL_MISSING_RIGHT_PAREN,
  ERROR_KIND_PARSE_SYSCALL_MISSING_COMMA,
  ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND,
  ERROR_KIND_PARSE_BINARY_OP_MISSING_RHS,
  ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL,
  ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE,
  ERROR_KIND_PARSE_FACTOR_MISSING_RHS,
  ERROR_KIND_PARSE_EQUALITY_MISSING_RHS,
  ERROR_KIND_PARSE_UNARY_MISSING_RHS,
  ERROR_KIND_PARSE_STATEMENT,
  ERROR_KIND_UNDEFINED_VAR,
  ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER,
  ERROR_KIND_PARSE_IF_MISSING_CONDITION,
  ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK,
  ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_LEFT,
  ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT,
  ERROR_KIND_PARSE_BLOCK_MISSING_STATEMENT,
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
  case ERROR_KIND_PARSE_SYSCALL_MISSING_LEFT_PAREN:
    printf("missing left parenthesis for syscall\n");
    break;
  case ERROR_KIND_PARSE_SYSCALL_MISSING_RIGHT_PAREN:
    printf("missing right parenthesis for syscall\n");
    break;
  case ERROR_KIND_PARSE_SYSCALL_MISSING_COMMA:
    printf("missing comma in syscall arguments\n");
    break;
  case ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND:
    printf("missing syscall argument\n");
    break;
  case ERROR_KIND_PARSE_BINARY_OP_MISSING_RHS:
    printf("missing second operand in binary operation\n");
    break;
  case ERROR_KIND_PARSE_STATEMENT:
    printf("failed to parse statement\n");
    break;
  case ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL:
    printf("missing := in variable declaration after variable name\n");
    break;
  case ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE:
    printf("missing value in variable declaration after :=\n");
    break;
  case ERROR_KIND_PARSE_FACTOR_MISSING_RHS:
    printf("missing right operand in -/+ operation\n");
    break;
  case ERROR_KIND_PARSE_EQUALITY_MISSING_RHS:
    printf("missing right operand in !=/= comparison\n");
    break;
  case ERROR_KIND_PARSE_UNARY_MISSING_RHS:
    printf("missing right operand in !/-/& operation\n");
    break;
  case ERROR_KIND_UNDEFINED_VAR:
    printf("undefined variable\n");
    break;
  case ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER:
    printf("trying to take address of something that is not a variable\n");
    break;
  case ERROR_KIND_PARSE_IF_MISSING_CONDITION:
    printf("missing if condition\n");
    break;
  case ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK:
    printf("missing if-then block\n");
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_LEFT:
    printf("missing '{' at the start of block\n");
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT:
    printf("missing '}' at the end of block\n");
    break;
  case ERROR_KIND_PARSE_BLOCK_MISSING_STATEMENT:
    printf("missing statement in block\n");
    break;
  default:
    PG_ASSERT(0);
  }
}
