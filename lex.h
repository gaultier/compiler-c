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
  LEX_TOKEN_KIND_SLASH,
  LEX_TOKEN_KIND_SLASH_SLASH,
  LEX_TOKEN_KIND_KEYWORD_IF,
  LEX_TOKEN_KIND_KEYWORD_ELSE,
  LEX_TOKEN_KIND_KEYWORD_ASSERT,
  LEX_TOKEN_KIND_KEYWORD_SYSCALL,
  LEX_TOKEN_KIND_KEYWORD_PRINTLN,
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

static void lex_add_error(Lexer *lexer, ErrorKind error_kind,
                          PgAllocator *allocator) {
  Origin origin = lex_lexer_origin(*lexer);
  Error error = {
      .kind = error_kind,
      .origin = origin,
      .src = lexer->src,
      .src_span = PG_SLICE_RANGE(lexer->src, origin.file_offset_start,
                                 origin.file_offset_start + 1),
  };
  PG_DYN_PUSH(lexer->errors, error, allocator);

  lexer->err_mode = true;
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

static void lex_advance_rune_res(Lexer *lexer, PgRuneUtf8Result rune_res,
                                 PgAllocator *allocator) {
  if (rune_res.err) {
    lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
    lexer->column += 1;
    lexer->it.idx += 1;
    return;
  }
  if (rune_res.end) {
    return;
  }

  lex_advance(lexer, rune_res.rune);
}

static void lex_advance_until_rune_excl(Lexer *lexer, PgRune needle,
                                        PgAllocator *allocator) {
  for (u64 _i = lexer->it.idx; _i < lexer->src.len; _i++) {
    PgRuneUtf8Result rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_next_res.err) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      lexer->column += 1;
      lexer->it.idx += 1;
      return;
    }
    if (rune_next_res.end) {
      return;
    }
    if (needle == rune_next_res.rune) {
      return;
    }

    lex_advance_rune_res(lexer, rune_next_res, allocator);
  }
}

static void lex_add_token(Lexer *lexer, LexTokenKind token_kind, Origin origin,
                          PgAllocator *allocator) {
  PG_DYN_PUSH(&lexer->tokens,
              ((LexToken){
                  .kind = token_kind,
                  .origin = origin,
              }),
              allocator);
}

// FIXME: Report all UTF8 errors from `pg_utf8_iterator_peek_next`!!!
[[nodiscard]]
static bool lex_match_rune_1(Lexer *lexer, PgRune rune1,
                             LexTokenKind token_kind1, PgAllocator *allocator) {

  Origin origin = lex_lexer_origin(*lexer);

  PgRuneUtf8Result rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
  if (rune_next_res.err) {
    lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
    lexer->column += 1;
    lexer->it.idx += 1;
    return false;
  }
  if (rune_next_res.end) {
    return false;
  }

  if (rune1 == rune_next_res.rune) {
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
    PgRuneUtf8Result rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_next_res.err) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      lexer->column += 1;
      lexer->it.idx += 1;
      return false;
    }
    if (rune_next_res.end) {
      return false;
    }
    if (rune1 != rune_next_res.rune) {
      return false;
    }
  }

  PgUtf8Iterator it_tmp = lexer->it;
  lex_advance(lexer, rune1);

  {
    PgRuneUtf8Result rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_next_res.err) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      lexer->column += 1;
      lexer->it.idx += 1;
      return false;
    }
    if (rune_next_res.end) {
      return false;
    }
    if (rune2 != rune_next_res.rune) {
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
    PgRuneUtf8Result rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_next_res.err) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      lexer->column += 1;
      lexer->it.idx += 1;
      return false;
    }
    if (rune_next_res.end) {
      return false;
    }
    if (rune1 != rune_next_res.rune) {
      return false;
    }

    lex_advance(lexer, rune1);
  }

  PgRuneUtf8Result rune_next_res = pg_utf8_iterator_peek_next(lexer->it);
  if (rune_next_res.err) {
    lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
    lexer->column += 1;
    lexer->it.idx += 1;
    return false;
  }
  if (rune_next_res.end || rune2 != rune_next_res.rune) {
    lex_add_token(lexer, token_kind1, origin, allocator);
    return true;
  } else {
    lex_add_token(lexer, token_kind2, origin, allocator);
    lex_advance(lexer, rune2);
    return true;
  }
}

static bool lex_identifier(Lexer *lexer, PgAllocator *allocator) {
  Origin origin = lex_lexer_origin(*lexer);

  for (u64 _i = 0; _i < lexer->it.s.len; _i++) {
    if (lexer->it.idx >= lexer->it.s.len) {
      return false;
    }

    PgRuneUtf8Result rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      return false;
    }
    if (rune_res.end) {
      break;
    }

    PgRune rune = rune_res.rune;

    if (!('_' == rune || pg_rune_ascii_is_alphanumeric(rune))) {
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
  PG_SLICE_LAST_PTR(&lexer->tokens)->s = lit;

  return true;
}

static bool lex_keyword(Lexer *lexer, PgAllocator *allocator) {
  Origin origin = lex_lexer_origin(*lexer);

  for (u64 _i = 0; _i < lexer->it.s.len; _i++) {
    if (lexer->it.idx >= lexer->it.s.len) {
      return false;
    }

    PgRuneUtf8Result rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      return false;
    }
    if (rune_res.end) {
      break;
    }

    PgRune rune = rune_res.rune;

    if (!('_' == rune || pg_rune_ascii_is_alphanumeric(rune))) {
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
  if (pg_string_eq(lit, PG_S("println"))) {
    lex_add_token(lexer, LEX_TOKEN_KIND_KEYWORD_PRINTLN, origin, allocator);
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

    PgRuneUtf8Result rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      return;
    }
    if (rune_res.end) {
      break;
    }

    PgRune rune = rune_res.rune;
    PG_ASSERT(0 != rune);

    if (!pg_rune_ascii_is_numeric(rune)) {
      break;
    }

    lex_advance(lexer, rune);
  }

  PgString lit =
      PG_SLICE_RANGE(lexer->it.s, origin.file_offset_start, lexer->it.idx);
  PG_ASSERT(lit.len > 0);

  bool starts_with_zero = '0' == PG_SLICE_AT(lit, 0);
  if (starts_with_zero && 1 > lit.len) {
    lex_add_error(lexer, ERROR_KIND_INVALID_LITERAL_NUMBER, allocator);
    PG_SLICE_LAST(*lexer->errors).src_span = lit;
    return;
  }

  lex_add_token(lexer, LEX_TOKEN_KIND_LITERAL_NUMBER, origin, allocator);
  PG_SLICE_LAST_PTR(&lexer->tokens)->s = lit;
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

    PgRuneUtf8Result rune_res = pg_utf8_iterator_peek_next(lexer->it);
    if (rune_res.err) {
      lex_add_error(lexer, ERROR_KIND_INVALID_UTF8, allocator);
      return;
    }
    if (rune_res.end) {
      break;
    }

    PgRune rune = rune_res.rune;
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
        PG_SLICE_LAST(*lexer->errors).src_span =
            PG_SLICE_RANGE(lexer->src, lexer->it.idx, lexer->it.idx + 1);
      }

    } break;

    case '=': {
      if (!lex_match_rune_1_or_2(lexer, '=', '=', LEX_TOKEN_KIND_EQUAL,
                                 LEX_TOKEN_KIND_EQUAL_EQUAL, allocator)) {
        lex_add_error(lexer, ERROR_KIND_UNKNOWN_TOKEN, allocator);
      }
    } break;

    case '/': {
      if (!lex_match_rune_1_or_2(lexer, '/', '/', LEX_TOKEN_KIND_SLASH,
                                 LEX_TOKEN_KIND_SLASH_SLASH, allocator)) {
        lex_add_error(lexer, ERROR_KIND_UNKNOWN_TOKEN, allocator);
      }

      LexToken matched = PG_SLICE_LAST(lexer->tokens);
      if (LEX_TOKEN_KIND_SLASH_SLASH == matched.kind) {
        lex_advance_until_rune_excl(lexer, '\n', allocator);
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
  lex_add_token(lexer, LEX_TOKEN_KIND_EOF, lex_lexer_origin(*lexer), allocator);
}

static void lex_tokens_print(LexTokenDyn tokens, PgWriter *w,
                             PgAllocator *allocator) {
  for (u64 i = 0; i < tokens.len; i++) {
    LexToken token = PG_SLICE_AT(tokens, i);

    (void)pg_writer_write_full(w, PG_S("["), allocator);
    (void)pg_writer_write_u64_as_string(w, i, allocator);
    (void)pg_writer_write_full(w, PG_S("]"), allocator);

    origin_write(w, token.origin, allocator);
    (void)pg_writer_write_full(w, PG_S(": "), allocator);

    switch (token.kind) {
    case LEX_TOKEN_KIND_NONE:
      PG_ASSERT(0);
    case LEX_TOKEN_KIND_LITERAL_NUMBER:
      (void)pg_writer_write_full(w, PG_S("LiteralU64 "), allocator);
      (void)pg_writer_write_full(w, token.s, allocator);
      break;
    case LEX_TOKEN_KIND_PLUS:
      (void)pg_writer_write_full(w, PG_S("+"), allocator);
      break;
    case LEX_TOKEN_KIND_PAREN_LEFT:
      (void)pg_writer_write_full(w, PG_S("("), allocator);
      break;
    case LEX_TOKEN_KIND_PAREN_RIGHT:
      (void)pg_writer_write_full(w, PG_S(")"), allocator);
      break;
    case LEX_TOKEN_KIND_CURLY_LEFT:
      (void)pg_writer_write_full(w, PG_S("{"), allocator);
      break;
    case LEX_TOKEN_KIND_CURLY_RIGHT:
      (void)pg_writer_write_full(w, PG_S("}"), allocator);
      break;
    case LEX_TOKEN_KIND_COMMA:
      (void)pg_writer_write_full(w, PG_S(","), allocator);
      break;
    case LEX_TOKEN_KIND_KEYWORD_SYSCALL:
      (void)pg_writer_write_full(w, PG_S("syscall"), allocator);
      break;
    case LEX_TOKEN_KIND_KEYWORD_PRINTLN:
      (void)pg_writer_write_full(w, PG_S("println"), allocator);
      break;
    case LEX_TOKEN_KIND_KEYWORD_IF:
      (void)pg_writer_write_full(w, PG_S("Keyword if"), allocator);
      break;
    case LEX_TOKEN_KIND_KEYWORD_ELSE:
      (void)pg_writer_write_full(w, PG_S("Keyword else"), allocator);
      break;
    case LEX_TOKEN_KIND_KEYWORD_ASSERT:
      (void)pg_writer_write_full(w, PG_S("Keyword assert"), allocator);
      break;
    case LEX_TOKEN_KIND_COLON_EQUAL:
      (void)pg_writer_write_full(w, PG_S(":="), allocator);
      break;
    case LEX_TOKEN_KIND_EQUAL_EQUAL:
      (void)pg_writer_write_full(w, PG_S("=="), allocator);
      break;
    case LEX_TOKEN_KIND_EQUAL:
      (void)pg_writer_write_full(w, PG_S("="), allocator);
      break;
    case LEX_TOKEN_KIND_SLASH_SLASH:
      (void)pg_writer_write_full(w, PG_S("//"), allocator);
      break;
    case LEX_TOKEN_KIND_SLASH:
      (void)pg_writer_write_full(w, PG_S("/"), allocator);
      break;
    case LEX_TOKEN_KIND_AMPERSAND:
      (void)pg_writer_write_full(w, PG_S("&"), allocator);
      break;
    case LEX_TOKEN_KIND_IDENTIFIER:
      (void)pg_writer_write_full(w, PG_S("Identifier "), allocator);
      (void)pg_writer_write_full(w, token.s, allocator);
      break;
    case LEX_TOKEN_KIND_EOF:
      (void)pg_writer_write_full(w, PG_S("EOF"), allocator);
      break;
    default:
      PG_ASSERT(0);
    }
    (void)pg_writer_write_full(w, PG_S("\n"), allocator);
  }
  (void)pg_writer_flush(w, allocator);
}

static void lex_trim_comments(LexTokenDyn *tokens) {
  for (u64 i = 0; i < tokens->len;) {
    LexToken token = PG_SLICE_AT(*tokens, i);
    if (LEX_TOKEN_KIND_SLASH_SLASH == token.kind) {
      PG_SLICE_REMOVE_AT(tokens, i);
    } else {
      i++;
    }
  }
}
