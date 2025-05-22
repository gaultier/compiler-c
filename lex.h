#pragma once
#include "error.h"
#include "origin.h"

typedef enum : u8 {
  LEX_TOKEN_KIND_NONE,
  LEX_TOKEN_KIND_LITERAL_NUMBER,
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
  LEX_TOKEN_KIND_KEYWORD_SYSCALL,
  LEX_TOKEN_KIND_EOF,
} LexTokenKind;

typedef struct {
  LexTokenKind kind;
  Origin origin;
  PgString s;
} LexToken;
PG_DYN(LexToken) LexTokenDyn;

typedef struct {
  PgString file_path;
  PgString src;
  u32 line, column;
  LexTokenDyn tokens;
  PgUtf8Iterator it;

  ErrorDyn *errors;
  bool err_mode;
} Lexer;

[[nodiscard]]
static Origin lex_lexer_origin(Lexer lexer) {
  Origin origin = {
      .column = lexer.column,
      .line = lexer.line,
      .file_path = lexer.file_path,
      .file_offset_start = (u32)lexer.it.idx,
  };
  return origin;
}

static void lex_advance(Lexer *lexer, PgRune rune) {
  lexer->it.idx += pg_utf8_rune_bytes_count(rune);

  if ('\n' == rune) {
    lexer->column = 1;
    lexer->line += 1;
  } else {
    lexer->column += pg_utf8_rune_bytes_count(rune);
  }
}

static void lex_add_token(Lexer *lexer, LexTokenKind token_kind, Origin origin,
                          PgAllocator *allocator) {
  *PG_DYN_PUSH(&lexer->tokens, allocator) = (LexToken){
      .kind = token_kind,
      .origin = origin,
  };
}

[[nodiscard]]
static bool lex_match_rune_1(Lexer *lexer, PgRune rune1,
                             LexTokenKind token_kind1, PgAllocator *allocator) {

  Origin origin = lex_lexer_origin(*lexer);

  PgRuneResult rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
  if (rune1 == rune_next_res.res) {
    lex_add_token(lexer, token_kind1, origin, allocator);
    lex_advance(lexer, rune1);

    return true;
  }

  return false;
}

[[nodiscard]]
static bool lex_match_rune_1_and_2(Lexer *lexer, PgRune rune1, PgRune rune2,
                                   LexTokenKind token_kind,
                                   PgAllocator *allocator) {

  Origin origin = lex_lexer_origin(*lexer);
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

  lex_add_token(lexer, token_kind, origin, allocator);
  lex_advance(lexer, rune2);

  return true;
}

[[nodiscard]]
static bool lex_match_rune_1_or_2(Lexer *lexer, PgRune rune1, PgRune rune2,
                                  LexTokenKind token_kind1,
                                  LexTokenKind token_kind2,
                                  PgAllocator *allocator) {
  Origin origin = lex_lexer_origin(*lexer);

  {
    PgRuneResult rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune1 != rune_next_res.res) {
      return false;
    }

    lex_advance(lexer, rune1);
  }

  PgRuneResult rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
  if (rune2 != rune_next_res.res) {
    lex_add_token(lexer, token_kind1, origin, allocator);
    return true;
  } else {
    lex_add_token(lexer, token_kind2, origin, allocator);
    lex_advance(lexer, rune2);
    return true;
  }
}

static void lex_add_error(Lexer *lexer, ErrorKind error_kind,
                          PgAllocator *allocator) {
  Origin origin = lex_lexer_origin(*lexer);
  *PG_DYN_PUSH(lexer->errors, allocator) = (Error){
      .kind = error_kind,
      .origin = origin,
      .src = lexer->src,
      .src_span = PG_SLICE_RANGE(lexer->src, origin.file_offset_start,
                                 origin.file_offset_start + 1),
  };

  lexer->err_mode = true;
}

static bool lex_identifier(Lexer *lexer, PgAllocator *allocator) {
  Origin origin = lex_lexer_origin(*lexer);

  for (u64 _i = 0; _i < lexer->it.s.len; _i++) {
    if (lexer->it.idx >= lexer->it.s.len) {
      return false;
    }

    PgRuneResult rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err || 0 == rune_res.res) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      return false;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    if (!('_' == rune || pg_rune_is_alphanumeric(rune))) {
      break;
    }

    lex_advance(lexer, rune);
  }

  PgString lit =
      PG_SLICE_RANGE(lexer->it.s, origin.file_offset_start, lexer->it.idx);
  if (0 == lit.len) {
    lexer->it.idx = origin.file_offset_start;
    lexer->column = origin.column;
    return false;
  }

  lex_add_token(lexer, LEX_TOKEN_KIND_IDENTIFIER, origin, allocator);
  PG_DYN_LAST_PTR(&lexer->tokens)->s = lit;

  return true;
}

static bool lex_keyword(Lexer *lexer, PgAllocator *allocator) {
  Origin origin = lex_lexer_origin(*lexer);

  for (u64 _i = 0; _i < lexer->it.s.len; _i++) {
    if (lexer->it.idx >= lexer->it.s.len) {
      return false;
    }

    PgRuneResult rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err || 0 == rune_res.res) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      return false;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    if (!('_' == rune || pg_rune_is_alphanumeric(rune))) {
      break;
    }

    lex_advance(lexer, rune);
  }

  PgString lit =
      PG_SLICE_RANGE(lexer->it.s, origin.file_offset_start, lexer->it.idx);
  if (0 == lit.len) {
    goto end;
  }

  if (pg_string_eq(lit, PG_S("syscall"))) {
    lex_add_token(lexer, LEX_TOKEN_KIND_KEYWORD_SYSCALL, origin, allocator);
    return true;
  }
  if (pg_string_eq(lit, PG_S("if"))) {
    lex_add_token(lexer, LEX_TOKEN_KIND_KEYWORD_IF, origin, allocator);
    return true;
  }
  if (pg_string_eq(lit, PG_S("else"))) {
    lex_add_token(lexer, LEX_TOKEN_KIND_KEYWORD_ELSE, origin, allocator);
    return true;
  }
  if (pg_string_eq(lit, PG_S("assert"))) {
    lex_add_token(lexer, LEX_TOKEN_KIND_KEYWORD_ASSERT, origin, allocator);
    return true;
  }

end:
  // Reset .
  lexer->it.idx = origin.file_offset_start;
  lexer->column = origin.column;
  return false;
}

static void lex_literal_number(Lexer *lexer, PgAllocator *allocator) {
  Origin origin = lex_lexer_origin(*lexer);

  for (u64 _i = 0; _i < lexer->it.s.len; _i++) {
    if (lexer->it.idx >= lexer->it.s.len) {
      return;
    }

    PgRuneResult rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err || 0 == rune_res.res) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      return;
    }

    PgRune rune = rune_res.res;
    PG_ASSERT(0 != rune);

    if (!pg_rune_is_numeric(rune)) {
      break;
    }

    lex_advance(lexer, rune);
  }

  PgString lit =
      PG_SLICE_RANGE(lexer->it.s, origin.file_offset_start, lexer->it.idx);
  PG_ASSERT(lit.len > 0);

  bool starts_with_zero = '0' == PG_SLICE_AT(lit, 0);
  if (starts_with_zero) {
    lex_add_error(lexer, ERROR_KIND_INVALID_LITERAL_NUMBER, allocator);
    PG_DYN_LAST(*lexer->errors).src_span = lit;
    return;
  }

  lex_add_token(lexer, LEX_TOKEN_KIND_LITERAL_NUMBER, origin, allocator);
  PG_DYN_LAST_PTR(&lexer->tokens)->s = lit;
}

[[nodiscard]]
static Lexer lex_make_lexer(PgString file_path, PgString src,
                            ErrorDyn *errors) {
  Lexer lexer = {0};
  lexer.file_path = file_path;
  lexer.src = src;
  lexer.line = 1;
  lexer.column = 1;
  lexer.it = pg_make_utf8_iterator(src);
  lexer.errors = errors;

  return lexer;
}

static void lex(Lexer *lexer, PgAllocator *allocator) {
  for (u64 _i = 0; _i < lexer->src.len; _i++) {
    if (lexer->it.idx >= lexer->src.len) {
      break;
    }

    PgRuneResult rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err || 0 == rune_res.res) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
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
      PG_ASSERT(lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_PLUS, allocator));
    } break;

    case '&': {
      PG_ASSERT(
          lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_AMPERSAND, allocator));
    } break;

    case '(': {
      PG_ASSERT(
          lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_PAREN_LEFT, allocator));
    } break;

    case ')': {
      PG_ASSERT(
          lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_PAREN_RIGHT, allocator));
    } break;

    case '{': {
      PG_ASSERT(
          lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_CURLY_LEFT, allocator));
    } break;

    case '}': {
      PG_ASSERT(
          lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_CURLY_RIGHT, allocator));
    } break;

    case ',': {
      PG_ASSERT(lex_match_rune_1(lexer, rune, LEX_TOKEN_KIND_COMMA, allocator));
    } break;

    case ':': {
      if (!lex_match_rune_1_and_2(lexer, ':', '=', LEX_TOKEN_KIND_COLON_EQUAL,
                                  allocator)) {
        lex_add_error(lexer, ERROR_KIND_UNKNOWN_TOKEN, allocator);
        PG_DYN_LAST(*lexer->errors).src_span =
            PG_SLICE_RANGE(lexer->src, lexer->it.idx, lexer->it.idx + 1);
      }

    } break;

    case '=': {
      if (!lex_match_rune_1_or_2(lexer, '=', '=', LEX_TOKEN_KIND_EQUAL,
                                 LEX_TOKEN_KIND_EQUAL_EQUAL, allocator)) {
        lex_add_error(lexer, ERROR_KIND_UNKNOWN_TOKEN, allocator);
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

      lex_add_error(lexer, ERROR_KIND_UNKNOWN_TOKEN, allocator);
    } break;
    }
  }
  lex_add_token(lexer, LEX_TOKEN_KIND_EOF, (Origin){0}, allocator);
}

static void lex_tokens_print(LexTokenDyn tokens) {
  for (u64 i = 0; i < tokens.len; i++) {
    LexToken token = PG_SLICE_AT(tokens, i);
    printf("[%lu] ", i);
    origin_print(token.origin);
    printf(": ");

    switch (token.kind) {
    case LEX_TOKEN_KIND_NONE:
      PG_ASSERT(0);
    case LEX_TOKEN_KIND_LITERAL_NUMBER:
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
      printf("Keyword if\n");
      break;
    case LEX_TOKEN_KIND_KEYWORD_ELSE:
      printf("Keyword else\n");
      break;
    case LEX_TOKEN_KIND_KEYWORD_ASSERT:
      printf("Keyword assert\n");
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
    case LEX_TOKEN_KIND_EOF:
      printf("EOF\n");
      break;
    default:
      PG_ASSERT(0);
    }
  }
}
