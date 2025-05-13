#pragma once
#include "error.h"
#include "origin.h"
#include "submodules/cstd/lib.c"

typedef enum {
  LEX_TOKEN_KIND_NONE,
  LEX_TOKEN_KIND_LITERAL_U64,
  LEX_TOKEN_KIND_PLUS,
  LEX_TOKEN_KIND_PAREN_LEFT,
  LEX_TOKEN_KIND_PAREN_RIGHT,
  LEX_TOKEN_KIND_CURLY_LEFT,
  LEX_TOKEN_KIND_CURLY_RIGHT,
  LEX_TOKEN_KIND_COMMA,
  LEX_TOKEN_KIND_COLON_EQUAL,
  LEX_TOKEN_KIND_EQUAL,
  LEX_TOKEN_KIND_EQUAL_EQUAL,
  LEX_TOKEN_KIND_IDENTIFIER,
  LEX_TOKEN_KIND_AMPERSAND,
  LEX_TOKEN_KIND_KEYWORD_IF,
  LEX_TOKEN_KIND_KEYWORD_ELSE,
  LEX_TOKEN_KIND_KEYWORD_ASSERT,
#if 0
  LEX_TOKEN_KIND_KEYWORD_SYSCALL,
#endif
} LexTokenKind;

typedef struct {
  LexTokenKind kind;
  Origin origin;
  PgString s;
} LexToken;
PG_SLICE(LexToken) LexTokenSlice;
PG_DYN(LexToken) LexTokenDyn;

typedef struct {
  PgString file_path;
  PgString src;
  u32 line, column;
  LexTokenDyn tokens;
  PgUtf8Iterator it;

  ErrorDyn errors;
  bool err_mode;
} Lexer;

static void lex_advance(Lexer *lexer, PgRune rune) {
  if ('\n' == rune) {
    lexer->column = 1;
    lexer->line += 1;
  } else {
    lexer->column += pg_utf8_rune_bytes_count(rune);
  }
}

static void lex_add_token(Lexer *lexer, LexTokenKind token_kind,
                          PgAllocator *allocator) {
  *PG_DYN_PUSH(&lexer->tokens, allocator) = (LexToken){
      .kind = token_kind,
      .origin =
          {
              .file_path = lexer->file_path,
              .line = lexer->line,
              .column = lexer->column,
              .file_offset = (u32)lexer->it.idx,
          },
  };
}

[[nodiscard]]
static bool lex_match_rune_1(Lexer *lexer, PgRune rune1,
                             LexTokenKind token_kind1, PgAllocator *allocator) {

  PgRuneResult rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
  if (rune1 == rune_next_res.res) {
    lexer->it.idx += pg_utf8_rune_bytes_count(rune1);
    lex_add_token(lexer, token_kind1, allocator);
    lex_advance(lexer, rune1);

    return true;
  }

  return false;
}

[[nodiscard]]
static bool lex_match_rune_1_and_2(Lexer *lexer, PgRune rune1, PgRune rune2,
                                   LexTokenKind token_kind,
                                   PgAllocator *allocator) {

  {
    PgRuneResult rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune1 != rune_next_res.res) {
      return false;
    }
  }

  PgUtf8Iterator it_tmp = lexer->it;
  lex_advance(lexer, rune1);

  {
    PgRuneResult rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune2 != rune_next_res.res) {
      lexer->it = it_tmp;
      return false;
    }
  }

  lex_add_token(lexer, token_kind, allocator);
  lex_advance(lexer, rune2);

  return true;
}

[[nodiscard]]
static bool lex_match_rune_1_or_2(Lexer *lexer, PgRune rune1, PgRune rune2,
                                  LexTokenKind token_kind1,
                                  LexTokenKind token_kind2,
                                  PgAllocator *allocator) {

  {
    PgRuneResult rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune1 != rune_next_res.res) {
      return false;
    }

    lexer->it.idx += pg_utf8_rune_bytes_count(rune1);
    lex_advance(lexer, rune1);
  }

  PgRuneResult rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
  if (rune2 != rune_next_res.res) {
    lex_add_token(lexer, token_kind1, allocator);
    return true;
  } else {
    lex_add_token(lexer, token_kind2, allocator);
    lex_advance(lexer, rune2);
    return true;
  }
}

static void lex_add_error(Lexer *lexer, ErrorKind error_kind,
                          PgAllocator *allocator) {
  *PG_DYN_PUSH(&lexer->errors, allocator) = (Error){
      .kind = error_kind,
      .origin =
          {
              .file_path = lexer->file_path,
              .line = lexer->line,
              .column = lexer->column,
              .file_offset = (u32)lexer->it.idx,
          },
  };

  lexer->err_mode = true;
}

static bool lex_identifier(PgUtf8Iterator *it, LexTokenDyn *tokens,
                           ErrorDyn *errors, PgString file_path, u32 line,
                           u32 *column, PgAllocator *allocator) {
  u32 column_start = *column;

  u64 idx_start = it->idx;

  for (u64 _i = 0; _i < it->s.len; _i++) {
    if (it->idx >= it->s.len) {
      return false;
    }
    u64 idx_prev = it->idx;

    PgRuneResult rune_res = pg_utf8_iterator_next(it);
    if (rune_res.err || 0 == rune_res.res) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_LEX_INVALID_UTF8,
          .origin =
              {
                  .file_path = file_path,
                  .line = line,
                  .column = *column,
                  .file_offset = (u32)it->idx,
              },
      };
      return false;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    if (!('_' == rune || pg_rune_is_alphanumeric(rune))) {
      it->idx = idx_prev;
      break;
    }

    *column += 1;
  }

  PgString lit = PG_SLICE_RANGE(it->s, idx_start, it->idx);
  if (0 == lit.len) {
    it->idx = idx_start;
    *column = column_start;
    return false;
  }

  *PG_DYN_PUSH(tokens, allocator) = (LexToken){
      .kind = LEX_TOKEN_KIND_IDENTIFIER,
      .s = lit,
      .origin =
          {
              .file_path = file_path,
              .line = line,
              .column = column_start,
              .file_offset = (u32)idx_start,
          },
  };

  return true;
}

static bool lex_keyword(PgUtf8Iterator *it, LexTokenDyn *tokens,
                        ErrorDyn *errors, PgString file_path, u32 line,
                        u32 *column, PgAllocator *allocator) {

  u32 column_start = *column;
  u64 idx_start = it->idx;

  for (u64 _i = 0; _i < it->s.len; _i++) {
    if (it->idx >= it->s.len) {
      return false;
    }
    u64 idx_prev = it->idx;

    PgRuneResult rune_res = pg_utf8_iterator_next(it);
    if (rune_res.err || 0 == rune_res.res) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_LEX_INVALID_UTF8,
          .origin =
              {
                  .file_path = file_path,
                  .line = line,
                  .column = *column,
                  .file_offset = (u32)it->idx,
              },
      };
      return false;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    if (!('_' == rune || pg_rune_is_alphanumeric(rune))) {
      it->idx = idx_prev;
      break;
    }

    *column += 1;
  }

  PgString lit = PG_SLICE_RANGE(it->s, idx_start, it->idx);
  if (0 == lit.len) {
    goto end;
  }

#if 0
  if (pg_string_eq(lit, PG_S("syscall"))) {
    *PG_DYN_PUSH(tokens, allocator) = (LexToken){
        .kind = LEX_TOKEN_KIND_KEYWORD_SYSCALL,
        .origin =
            {
                .file_path = file_path,
                .line = line,
                .column = column_start,
                .file_offset = (u32)idx_start,
            },
    };
    return true;
  }
#endif
  if (pg_string_eq(lit, PG_S("if"))) {
    *PG_DYN_PUSH(tokens, allocator) = (LexToken){
        .kind = LEX_TOKEN_KIND_KEYWORD_IF,
        .origin =
            {
                .file_path = file_path,
                .line = line,
                .column = column_start,
                .file_offset = (u32)idx_start,
            },
    };
    return true;
  }
  if (pg_string_eq(lit, PG_S("else"))) {
    *PG_DYN_PUSH(tokens, allocator) = (LexToken){
        .kind = LEX_TOKEN_KIND_KEYWORD_ELSE,
        .origin =
            {
                .file_path = file_path,
                .line = line,
                .column = column_start,
                .file_offset = (u32)idx_start,
            },
    };
    return true;
  }

end:
  // Reset .
  it->idx = idx_start;
  *column = column_start;
  return false;
}

static void lex_literal_number(Lexer *lexer, PgAllocator *allocator) {
  u64 idx_start = lexer->it.idx;

  for (u64 _i = 0; _i < lexer->it.s.len; _i++) {
    if (lexer->it.idx >= lexer->it.s.len) {
      return;
    }
    u64 idx_prev = lexer->it.idx;

    PgRuneResult rune_res = pg_utf8_iterator_next(&lexer->it);
    if (rune_res.err || 0 == rune_res.res) {
      lex_add_error(lexer, ERROR_KIND_LEX_INVALID_UTF8, allocator);
      return;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    if (!pg_rune_is_numeric(rune)) {
      lexer->it.idx = idx_prev;
      break;
    }

    lex_advance(lexer, rune);
  }

  PgString lit = PG_SLICE_RANGE(lexer->it.s, idx_start, lexer->it.idx);
  PG_ASSERT(lit.len > 0);

  if (1 > lit.len && '0' == PG_SLICE_AT(lit, 0)) {
    lex_add_error(lexer, ERROR_KIND_LEX_INVALID_LITERAL_NUMBER, allocator);
    return;
  }

  lex_add_token(lexer, LEX_TOKEN_KIND_LITERAL_U64, allocator);
  PG_DYN_LAST_PTR(&lexer->tokens)->s = lit;
}

[[nodiscard]]
static Lexer lex_make_lexer(PgString file_path, PgString src) {
  Lexer lexer = {0};
  lexer.file_path = file_path;
  lexer.src = src;
  lexer.line = 1;
  lexer.column = 1;
  lexer.it = pg_make_utf8_iterator(src);

  return lexer;
}

static void lex(Lexer *lexer, PgAllocator *allocator) {
  for (u64 _i = 0; _i < lexer->src.len; _i++) {
    if (lexer->it.idx >= lexer->src.len) {
      return;
    }
    u64 idx_prev = lexer->it.idx;

    PgRuneResult rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err || 0 == rune_res.res) {
      lex_add_error(lexer, ERROR_KIND_LEX_INVALID_UTF8, allocator);
      return;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    // Skip to the next newline if in error mode.
    // TODO: memchr?
    if ('\n' != rune && lexer->err_mode) {
      lex_advance(lexer, rune);
      continue;
    }

    switch (rune) {
    case '\n':
      lex_advance(lexer, rune);
      lexer->err_mode = false;
      break;
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9': {
      lex_literal_number(lexer, allocator);
    } break;

    case '+': {
      lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_PLUS, allocator);
    } break;

    case '&': {
      lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_AMPERSAND, allocator);
    } break;

    case '(': {
      lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_PAREN_LEFT, allocator);
    } break;

    case ')': {
      lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_PAREN_RIGHT, allocator);
    } break;

    case '{': {
      lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_CURLY_LEFT, allocator);
    } break;

    case '}': {
      lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_CURLY_RIGHT, allocator);
    } break;

    case ',': {
      lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_COMMA, allocator);
    } break;

    case ':': {
      if (!lex_match_rune_1_and_2(lexer, ':', '=', LEX_TOKEN_KIND_COLON_EQUAL,
                                  allocator)) {
        lex_add_error(lexer, ERROR_KIND_LEX_UNKNOWN_TOKEN, allocator);
      }

    } break;

    case '=': {
      if (!lex_match_rune_1_or_2(lexer, '=', '=', LEX_TOKEN_KIND_EQUAL,
                                 LEX_TOKEN_KIND_EQUAL_EQUAL, allocator)) {
        lex_add_error(lexer, ERROR_KIND_LEX_UNKNOWN_TOKEN, allocator);
      }
    } break;

    case ' ': {
      lex_advance(lexer, rune);
      break;
    }

    default: {
      if (lex_keyword(lexer, allocator)) {
        break;
      }

      if (lex_identifier(lexer, allocator)) {
        break;
      }

      lex_add_error(lexer, ERROR_KIND_LEX_UNKNOWN_TOKEN, allocator);
    } break;
    }
  }
}

static void lex_tokens_print(LexTokenSlice tokens) {
  for (u64 i = 0; i < tokens.len; i++) {
    LexToken token = PG_SLICE_AT(tokens, i);
    origin_print(token.origin);
    putchar(' ');

    switch (token.kind) {
    case LEX_TOKEN_KIND_NONE:
      PG_ASSERT(0);
    case LEX_TOKEN_KIND_LITERAL_U64:
      printf("LiteralU64 %.*s\n", (i32)token.s.len, token.s.data);
      break;
    case LEX_TOKEN_KIND_PLUS:
      printf("+\n");
      break;
    case LEX_TOKEN_KIND_PAREN_LEFT:
      printf("(\n");
      break;
    case LEX_TOKEN_KIND_PAREN_RIGHT:
      printf(")\n");
      break;
    case LEX_TOKEN_KIND_CURLY_LEFT:
      printf("{\n");
      break;
    case LEX_TOKEN_KIND_CURLY_RIGHT:
      printf("}\n");
      break;
    case LEX_TOKEN_KIND_COMMA:
      printf(",\n");
      break;
#if 0
    case LEX_TOKEN_KIND_KEYWORD_SYSCALL:
      printf("syscall\n");
      break;
#endif
    case LEX_TOKEN_KIND_KEYWORD_IF:
      printf("if\n");
      break;
    case LEX_TOKEN_KIND_KEYWORD_ELSE:
      printf("else\n");
      break;
    case LEX_TOKEN_KIND_KEYWORD_ASSERT:
      printf("assert\n");
      break;
    case LEX_TOKEN_KIND_COLON_EQUAL:
      printf(":=\n");
      break;
    case LEX_TOKEN_KIND_EQUAL_EQUAL:
      printf("==\n");
      break;
    case LEX_TOKEN_KIND_EQUAL:
      printf("=\n");
      break;
    case LEX_TOKEN_KIND_AMPERSAND:
      printf("&\n");
      break;
    case LEX_TOKEN_KIND_IDENTIFIER:
      printf("Identifier %.*s\n", (i32)token.s.len, token.s.data);
      break;
    default:
      PG_ASSERT(0);
    }
  }
}
