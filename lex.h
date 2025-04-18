#pragma once
#include "error.h"
#include "origin.h"
#include "submodules/cstd/lib.c"

typedef enum {
  LEX_TOKEN_KIND_NONE,
  LEX_TOKEN_KIND_LITERAL_U64,
  LEX_TOKEN_KIND_PLUS,
  LEX_TOKEN_KIND_KEYWORD_SYSCALL,
  LEX_TOKEN_KIND_PAREN_LEFT,
  LEX_TOKEN_KIND_PAREN_RIGHT,
  LEX_TOKEN_KIND_CURLY_LEFT,
  LEX_TOKEN_KIND_CURLY_RIGHT,
  LEX_TOKEN_KIND_COMMA,
  LEX_TOKEN_KIND_COLON_EQUAL,
  LEX_TOKEN_KIND_IDENTIFIER,
  LEX_TOKEN_KIND_AMPERSAND,
  LEX_TOKEN_KIND_KEYWORD_IF,
  LEX_TOKEN_KIND_KEYWORD_ELSE,
} LexTokenKind;

typedef struct {
  LexTokenKind kind;
  Origin origin;
  PgString s;
} LexToken;
PG_SLICE(LexToken) LexTokenSlice;
PG_DYN(LexToken) LexTokenDyn;

static bool lex_identifier(PgUtf8Iterator *it, LexTokenDyn *tokens,
                           ErrorDyn *errors, PgString file_name, u32 line,
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
                  .file_name = file_name,
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
              .file_name = file_name,
              .line = line,
              .column = column_start,
              .file_offset = (u32)idx_start,
          },
  };

  return true;
}

static bool lex_keyword(PgUtf8Iterator *it, LexTokenDyn *tokens,
                        ErrorDyn *errors, PgString file_name, u32 line,
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
                  .file_name = file_name,
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

  if (pg_string_eq(lit, PG_S("syscall"))) {
    *PG_DYN_PUSH(tokens, allocator) = (LexToken){
        .kind = LEX_TOKEN_KIND_KEYWORD_SYSCALL,
        .origin =
            {
                .file_name = file_name,
                .line = line,
                .column = column_start,
                .file_offset = (u32)idx_start,
            },
    };
    return true;
  }
  if (pg_string_eq(lit, PG_S("if"))) {
    *PG_DYN_PUSH(tokens, allocator) = (LexToken){
        .kind = LEX_TOKEN_KIND_KEYWORD_IF,
        .origin =
            {
                .file_name = file_name,
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
                .file_name = file_name,
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

static void lex_literal_number(PgUtf8Iterator *it, PgRune first_rune,
                               LexTokenDyn *tokens, ErrorDyn *errors,
                               PgString file_name, u32 line, u32 *column,
                               PgAllocator *allocator) {
  PG_ASSERT(pg_rune_is_numeric(first_rune));

  u32 column_start = *column;

  // Unconsume the first rune.
  PG_ASSERT(it->idx > 0);
  it->idx -= 1;

  u64 idx_start = it->idx;

  for (u64 _i = 0; _i < it->s.len; _i++) {
    if (it->idx >= it->s.len) {
      return;
    }
    u64 idx_prev = it->idx;

    PgRuneResult rune_res = pg_utf8_iterator_next(it);
    if (rune_res.err || 0 == rune_res.res) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_LEX_INVALID_UTF8,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = *column,
                  .file_offset = (u32)it->idx,
              },
      };
      return;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    if (!pg_rune_is_numeric(rune)) {
      it->idx = idx_prev;
      break;
    }

    *column += 1;
  }

  PgString lit = PG_SLICE_RANGE(it->s, idx_start, it->idx);
  PG_ASSERT(lit.len > 0);

  if (1 > lit.len && '0' == PG_SLICE_AT(lit, 0)) {
    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_LEX_INVALID_LITERAL_NUMBER,
        .origin =
            {
                .file_name = file_name,
                .line = line,
                .column = *column,
                .file_offset = (u32)it->idx,
            },
    };
    return;
  }

  *PG_DYN_PUSH(tokens, allocator) = (LexToken){
      .kind = LEX_TOKEN_KIND_LITERAL_U64,
      .s = lit,
      .origin =
          {
              .file_name = file_name,
              .line = line,
              .column = column_start,
              .file_offset = (u32)idx_start,
          },
  };
}

static void lex(PgString file_name, PgString src, LexTokenDyn *tokens,
                ErrorDyn *errors, PgAllocator *allocator) {
  PgUtf8Iterator it = pg_make_utf8_iterator(src);

  u32 line = 1, column = 1;
  bool err_mode = false;

  for (u64 _i = 0; _i < src.len; _i++) {
    if (it.idx >= src.len) {
      return;
    }
    u64 idx_prev = it.idx;

    PgRuneResult rune_res = pg_utf8_iterator_next(&it);
    if (rune_res.err || 0 == rune_res.res) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_LEX_INVALID_UTF8,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)it.idx,
              },
      };
      return;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    // Skip to the next newline if in error mode.
    if ('\n' != rune && err_mode) {
      continue;
    }

    switch (rune) {
    case '\n':
      line += 1;
      column = 1;
      err_mode = false;
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
      lex_literal_number(&it, rune, tokens, errors, file_name, line, &column,
                         allocator);
    } break;

    case '+': {
      *PG_DYN_PUSH(tokens, allocator) = (LexToken){
          .kind = LEX_TOKEN_KIND_PLUS,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)idx_prev,
              },
      };

      column += 1;
    } break;

    case '&': {
      *PG_DYN_PUSH(tokens, allocator) = (LexToken){
          .kind = LEX_TOKEN_KIND_AMPERSAND,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)idx_prev,
              },
      };

      column += 1;
    } break;

    case '(': {
      *PG_DYN_PUSH(tokens, allocator) = (LexToken){
          .kind = LEX_TOKEN_KIND_PAREN_LEFT,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)idx_prev,
              },
      };

      column += 1;
    } break;

    case ')': {
      *PG_DYN_PUSH(tokens, allocator) = (LexToken){
          .kind = LEX_TOKEN_KIND_PAREN_RIGHT,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)idx_prev,
              },
      };

      column += 1;
    } break;

    case '{': {
      *PG_DYN_PUSH(tokens, allocator) = (LexToken){
          .kind = LEX_TOKEN_KIND_CURLY_LEFT,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)idx_prev,
              },
      };

      column += 1;
    } break;

    case '}': {
      *PG_DYN_PUSH(tokens, allocator) = (LexToken){
          .kind = LEX_TOKEN_KIND_CURLY_RIGHT,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)idx_prev,
              },
      };

      column += 1;
    } break;

    case ',': {
      *PG_DYN_PUSH(tokens, allocator) = (LexToken){
          .kind = LEX_TOKEN_KIND_COMMA,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)idx_prev,
              },
      };

      column += 1;
    } break;

    case ':': {
      PgUtf8Iterator it_tmp = it;
      PgRuneResult rune_next_res = pg_utf8_iterator_next(&it_tmp);
      if ('=' != rune_next_res.res) {
        *PG_DYN_PUSH(errors, allocator) = (Error){
            .kind = ERROR_KIND_LEX_UNKNOWN_TOKEN,
            .origin =
                {
                    .file_name = file_name,
                    .line = line,
                    .column = column,
                    .file_offset = (u32)it.idx,
                },
        };

        err_mode = true;
      }
      it = it_tmp;

      *PG_DYN_PUSH(tokens, allocator) = (LexToken){
          .kind = LEX_TOKEN_KIND_COLON_EQUAL,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)idx_prev,
              },
      };

      column += 2;

    } break;

    case ' ': {
      column += 1;
      break;
    }

    default: {
      // Unconsume the first rune.
      PG_ASSERT(it.idx > 0);
      it.idx -= 1;

      if (lex_keyword(&it, tokens, errors, file_name, line, &column,
                      allocator)) {
        break;
      }

      if (lex_identifier(&it, tokens, errors, file_name, line, &column,
                         allocator)) {
        break;
      }

      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_LEX_UNKNOWN_TOKEN,
          .origin =
              {
                  .file_name = file_name,
                  .line = line,
                  .column = column,
                  .file_offset = (u32)it.idx,
              },
      };

      err_mode = true;
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
    case LEX_TOKEN_KIND_KEYWORD_SYSCALL:
      printf("syscall\n");
      break;
    case LEX_TOKEN_KIND_KEYWORD_IF:
      printf("if\n");
      break;
    case LEX_TOKEN_KIND_KEYWORD_ELSE:
      printf("else\n");
      break;
    case LEX_TOKEN_KIND_COLON_EQUAL:
      printf(":=\n");
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
