#pragma once
#include "lex.h"

typedef enum {
  AST_NODE_KIND_NONE,
  AST_NODE_KIND_NUMBER,
  AST_NODE_KIND_IDENTIFIER,
  AST_NODE_KIND_ADD,
  AST_NODE_KIND_BLOCK,
  AST_NODE_KIND_VAR_DEFINITION,
  AST_NODE_KIND_ADDRESS_OF,
  AST_NODE_KIND_JUMP_IF_FALSE,
  AST_NODE_KIND_JUMP,
  AST_NODE_KIND_COMPARISON,
  AST_NODE_KIND_BUILTIN_ASSERT,
  AST_NODE_KIND_SYSCALL,
  AST_NODE_KIND_FN_DEFINITION,
} AstNodeKind;

typedef struct AstNode AstNode;
PG_DYN(AstNode) AstNodeDyn;

typedef enum [[clang::flag_enum]] {
  AST_NODE_FLAG_NONE = 0,
  AST_NODE_FLAG_GLOBAL = 1 << 0,
  AST_NODE_FLAG_FN_NO_FRAME_POINTERS = 1 << 1,
} AstNodeFlag;

struct AstNode {
  AstNodeKind kind;
  union {
    u64 n64;             // NUmber literal.
    PgString identifier; // Variable name.
    u64 args_count;      // Function.
  } u;
  Origin origin;
  LexTokenKind token_kind;
  AstNodeFlag flags;
};

typedef struct {
  Lexer lexer;
  u64 tokens_consumed;
  ErrorDyn *errors;
  AstNodeDyn nodes;
} AstParser;

static void ast_add_error(AstParser *parser, ErrorKind error_kind,
                          Origin origin, PgAllocator *allocator) {
  *PG_DYN_PUSH(parser->errors, allocator) = (Error){
      .kind = error_kind,
      .origin = origin,
      .src = parser->lexer.src,
      // FIXME
      .src_span = PG_SLICE_RANGE(parser->lexer.src, origin.file_offset_start,
                                 origin.file_offset_start + 1),
  };

  // Skip to the next newline to avoid having cascading errors.

  for (; parser->tokens_consumed < parser->lexer.tokens.len;
       parser->tokens_consumed++) {
    LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
    if (token.origin.line > origin.line) {
      break;
    }
  }
}

// Best effort to find the closest token when doing error reporting.
[[nodiscard]]
static LexToken ast_current_or_last_token(AstParser parser) {
  LexToken res = {0};

  if (parser.tokens_consumed >= parser.lexer.tokens.len) {
    return PG_DYN_LAST(parser.lexer.tokens);
  }

  res = PG_SLICE_AT(parser.lexer.tokens, parser.tokens_consumed);
  if (res.kind) {
    return res;
  }

  return PG_SLICE_AT(parser.lexer.tokens,
                     parser.tokens_consumed ? parser.tokens_consumed - 1 : 0);
}

static void ast_push(AstParser *parser, AstNode node, PgAllocator *allocator) {
  *PG_DYN_PUSH(&parser->nodes, allocator) = node;
}

[[nodiscard]]
static AstNode ast_peek_first(AstNodeDyn nodes) {
  AstNode res = {0};

  if (0 == nodes.len) {
    return res;
  }

  return PG_SLICE_AT(nodes, 0);
}

[[maybe_unused]] // TODO
[[nodiscard]]
static AstNode ast_pop_first(AstNodeDyn nodes, u64 *idx) {
  PG_ASSERT(idx);

  AstNode res = {0};

  if (*idx >= nodes.len) {
    return res;
  }

  res = PG_SLICE_AT(nodes, *idx);
  *idx += 1;

  return res;
}

static void ast_print(AstNodeDyn nodes, u32 left_width) {
  for (u64 i = 0; i < nodes.len; i++) {
    AstNode node = PG_SLICE_AT(nodes, i);

    for (u64 j = 0; j < left_width; j++) {
      putchar(' ');
    }
    origin_print(node.origin);
    putchar(' ');

    switch (node.kind) {
    case AST_NODE_KIND_NUMBER:
      printf("U64(%" PRIu64 ")\n", node.u.n64);
      break;
    case AST_NODE_KIND_IDENTIFIER:
      printf("Identifier(%.*s)\n", (i32)node.u.identifier.len,
             node.u.identifier.data);
      break;
    case AST_NODE_KIND_ADDRESS_OF:
      printf("AddressOf\n");
      break;
    case AST_NODE_KIND_BUILTIN_ASSERT:
      printf("Assert\n");
      break;
    case AST_NODE_KIND_ADD:
      printf("Add\n");
      break;
    case AST_NODE_KIND_COMPARISON:
      printf("Comparison\n");
      break;
    case AST_NODE_KIND_SYSCALL: {
      printf("Syscall\n");
    } break;
    case AST_NODE_KIND_BLOCK: {
      printf("Block\n");
    } break;
    case AST_NODE_KIND_VAR_DEFINITION:
      printf("VarDecl %.*s\n", (i32)node.u.identifier.len,
             node.u.identifier.data);
      break;
    case AST_NODE_KIND_JUMP_IF_FALSE:
      printf("JumpIfFalse\n");
      break;
    case AST_NODE_KIND_JUMP:
      printf("Jump\n");
      break;
    case AST_NODE_KIND_FN_DEFINITION:
      printf("FnDefinition %.*s\n", (i32)node.u.identifier.len,
             node.u.identifier.data);
      break;
    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }
}

[[nodiscard]]
static LexToken ast_match_token_kind(AstParser *parser, LexTokenKind kind) {
  LexToken res = {0};

  if (parser->tokens_consumed >= parser->lexer.tokens.len) {
    return res;
  }

  LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
  if (kind != token.kind) {
    return res;
  }

  parser->tokens_consumed += 1;
  res = token;
  return res;
}

[[nodiscard]]
static LexToken ast_match_token_kind1_or_kind2(AstParser *parser,
                                               LexTokenKind kind1,
                                               LexTokenKind kind2) {
  LexToken res = {0};

  if (parser->tokens_consumed >= parser->lexer.tokens.len) {
    return res;
  }

  LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
  if (!(kind1 == token.kind || kind2 == token.kind)) {
    return res;
  }

  parser->tokens_consumed += 1;
  res = token;
  return res;
}

[[nodiscard]]
static bool ast_parse_expr(AstParser *parser, PgAllocator *allocator);
[[nodiscard]]
static bool ast_parse_statement(AstParser *parser, PgAllocator *allocator);
[[nodiscard]]
static bool ast_parse_declaration(AstParser *parser, PgAllocator *allocator);
[[nodiscard]]
static bool ast_parse_syscall(AstParser *parser, PgAllocator *allocator);

[[nodiscard]]
static bool ast_parse_var_decl(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_IDENTIFIER);
  if (!token_first.kind) {
    return false;
  }
  PG_ASSERT(!pg_string_is_empty(token_first.s));

  LexToken token_colon_equal =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_COLON_EQUAL);
  if (!token_colon_equal.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (!ast_parse_expr(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.kind = AST_NODE_KIND_VAR_DEFINITION;
  node.origin = token_first.origin;
  node.u.identifier = token_first.s;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_primary(AstParser *parser, PgAllocator *allocator) {
  LexToken first = ast_match_token_kind1_or_kind2(
      parser, LEX_TOKEN_KIND_LITERAL_NUMBER, LEX_TOKEN_KIND_IDENTIFIER);

  if (LEX_TOKEN_KIND_LITERAL_NUMBER == first.kind) {
    AstNode node = {0};
    node.origin = first.origin;
    node.kind = AST_NODE_KIND_NUMBER;
    PgParseNumberResult parse_res = pg_string_parse_u64(first.s);
    PG_ASSERT(parse_res.present);
    PG_ASSERT(pg_string_is_empty(parse_res.remaining));
    node.u.n64 = parse_res.n;
    ast_push(parser, node, allocator);

    return true;
  }

  if (LEX_TOKEN_KIND_IDENTIFIER == first.kind) {
    AstNode node = {0};
    node.origin = first.origin;
    node.kind = AST_NODE_KIND_IDENTIFIER;
    node.u.identifier = first.s;
    ast_push(parser, node, allocator);

    return true;
  }

  return false;
}

[[nodiscard]]
static bool ast_parse_call(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_primary(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_unary(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first = ast_match_token_kind(parser, LEX_TOKEN_KIND_AMPERSAND);
  if (!token_first.kind) {
    return ast_parse_call(parser, allocator);
  }

  if (!ast_parse_unary(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_UNARY_MISSING_RHS,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (AST_NODE_KIND_IDENTIFIER != ast_peek_first(parser->nodes).kind) {
    ast_add_error(parser, ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.origin = token_first.origin;
  node.kind = AST_NODE_KIND_ADDRESS_OF;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_factor(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_unary(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_term(AstParser *parser, PgAllocator *allocator) {
  if (!ast_parse_factor(parser, allocator)) {
    return false;
  }

  for (u64 _i = parser->tokens_consumed; _i < parser->lexer.tokens.len; _i++) {
    LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_PLUS);
    if (!token.kind) {
      return true;
    }

    if (!ast_parse_factor(parser, allocator)) {
      ast_add_error(parser, ERROR_KIND_PARSE_FACTOR_MISSING_RHS,
                    ast_current_or_last_token(*parser).origin, allocator);
      return false;
    }
    AstNode node = {0};
    node.origin = token.origin;
    node.kind = AST_NODE_KIND_ADD;
    ast_push(parser, node, allocator);
  }
  return false;
}

[[nodiscard]]
static bool ast_parse_comparison(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_term(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_equality(AstParser *parser, PgAllocator *allocator) {
  if (!ast_parse_comparison(parser, allocator)) {
    return false;
  }

  for (u64 _i = parser->tokens_consumed; _i < parser->lexer.tokens.len; _i++) {
    LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_EQUAL_EQUAL);
    // TODO: `!=`.
    if (!token.kind) {
      return true;
    }
    if (!ast_parse_comparison(parser, allocator)) {
      ast_add_error(parser, ERROR_KIND_PARSE_EQUALITY_MISSING_RHS,
                    ast_current_or_last_token(*parser).origin, allocator);
      return false;
    }

    AstNode node = {0};
    node.origin = token.origin;
    node.kind = AST_NODE_KIND_COMPARISON;
    node.token_kind = token.kind;
    ast_push(parser, node, allocator);
  }
  return false;
}

[[nodiscard]]
static bool ast_parse_logic_and(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_equality(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_logic_or(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_logic_and(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_assignment(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_logic_or(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_expr(AstParser *parser, PgAllocator *allocator) {
  if (ast_parse_syscall(parser, allocator)) {
    return true;
  }

  if (ast_parse_assignment(parser, allocator)) {
    return true;
  }

  return false;
}

[[nodiscard]]
static bool ast_parse_syscall(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_SYSCALL);
  if (!token_first.kind) {
    return false;
  }

  LexToken token_left_paren =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_LEFT);
  if (!token_left_paren.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_LEFT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  LexToken token_after = {0};

  u64 args_count = 0;

  while (parser->tokens_consumed < parser->lexer.tokens.len) {
    LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
    if (LEX_TOKEN_KIND_PAREN_RIGHT == token.kind) {
      break;
    }

    if (!ast_parse_expr(parser, allocator)) {
      ast_add_error(parser, ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND,
                    ast_current_or_last_token(*parser).origin, allocator);
      return false;
    }

    args_count += 1;

    token_after = ast_match_token_kind1_or_kind2(
        parser, LEX_TOKEN_KIND_PAREN_RIGHT, LEX_TOKEN_KIND_COMMA);
    if (LEX_TOKEN_KIND_PAREN_RIGHT == token_after.kind) {
      break;
    }
    if (LEX_TOKEN_KIND_COMMA == token_after.kind) {
      continue;
    }

    ast_add_error(parser, ERROR_KIND_PARSE_SYSCALL_MISSING_COMMA,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (LEX_TOKEN_KIND_PAREN_RIGHT != token_after.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_RIGHT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.origin = token_first.origin;
  node.kind = AST_NODE_KIND_SYSCALL;
  node.u.args_count = args_count;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_block(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_CURLY_LEFT);
  if (!token_first.kind) {
    return false;
  }

  u64 args_count = 0;

  for (u64 _i = parser->tokens_consumed; _i < parser->lexer.tokens.len; _i++) {
    LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_CURLY_RIGHT);
    if (token.kind) {
      AstNode node = {0};
      node.origin = token_first.origin;
      node.kind = AST_NODE_KIND_BLOCK;
      node.u.args_count = args_count;
      return true;
    }

    if (!ast_parse_declaration(parser, allocator)) {
      break; // EOF?
    }
  }

  ast_add_error(parser, ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT,
                ast_current_or_last_token(*parser).origin, allocator);
  return false;
}

[[nodiscard]]
static bool ast_parse_statement_if(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_IF);
  if (!token_first.kind) {
    return false;
  }

  if (!ast_parse_expr(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_IF_MISSING_CONDITION,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (!ast_parse_block(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK,
                  token_first.origin, allocator);
    return false;
  }

  // TODO: optional else.

  AstNode node = {0};
  node.origin = token_first.origin;
  node.kind = AST_NODE_KIND_JUMP_IF_FALSE;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_statement_assert(AstParser *parser,
                                       PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_ASSERT);
  if (!token_first.kind) {
    return false;
  }

  LexToken token_paren_left =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_LEFT);
  if (!token_paren_left.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_LEFT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (!ast_parse_expr(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_ASSERT_MISSING_EXPRESSION,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  LexToken token_paren_right =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_RIGHT);
  if (!token_paren_right.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_RIGHT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.origin = token_first.origin;
  node.kind = AST_NODE_KIND_BUILTIN_ASSERT;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_statement(AstParser *parser, PgAllocator *allocator) {
  if (ast_parse_statement_if(parser, allocator)) {
    return true;
  }

  if (ast_parse_statement_assert(parser, allocator)) {
    return true;
  }

  if (ast_parse_expr(parser, allocator)) {
    return true;
  }

  return false;
}

[[nodiscard]]
static bool ast_parse_declaration(AstParser *parser, PgAllocator *allocator) {
  if (ast_parse_var_decl(parser, allocator)) {
    return true;
  }

  return ast_parse_statement(parser, allocator);
}

static void ast_emit_program_epilog(AstParser *parser, PgAllocator *allocator) {
  {
    AstNode fn = {0};
    fn.kind = AST_NODE_KIND_FN_DEFINITION;
    fn.u.identifier = PG_S("__builtin_exit");
    fn.flags = AST_NODE_FLAG_FN_NO_FRAME_POINTERS;
    ast_push(parser, fn, allocator);

    AstNode op0 = {0};
    op0.kind = AST_NODE_KIND_NUMBER;
    op0.u.n64 = 60; // FIXME: Only on Linux amd64.
    ast_push(parser, op0, allocator);

    AstNode op1 = {0};
    op1.kind = AST_NODE_KIND_NUMBER;
    op1.u.n64 = 0;
    ast_push(parser, op1, allocator);

    AstNode syscall = {0};
    syscall.kind = AST_NODE_KIND_SYSCALL;
    ast_push(parser, syscall, allocator);
  }
  {
    AstNode fn = {0};
    fn.kind = AST_NODE_KIND_FN_DEFINITION;
    fn.u.identifier = PG_S("__builtin_die");
    fn.flags = AST_NODE_FLAG_FN_NO_FRAME_POINTERS;
    ast_push(parser, fn, allocator);

    AstNode op0 = {0};
    op0.kind = AST_NODE_KIND_NUMBER;
    op0.u.n64 = 60; // FIXME: Only on Linux amd64.
    ast_push(parser, op0, allocator);

    AstNode op1 = {0};
    op1.kind = AST_NODE_KIND_NUMBER;
    op1.u.n64 = 1;
    ast_push(parser, op1, allocator);

    AstNode syscall = {0};
    syscall.kind = AST_NODE_KIND_SYSCALL;
    ast_push(parser, syscall, allocator);
  }
}

static void ast_emit(AstParser *parser, PgAllocator *allocator) {
  AstNode fn_start = {0};
  fn_start.kind = AST_NODE_KIND_FN_DEFINITION;
  fn_start.u.identifier = PG_S("_start");
  fn_start.flags = AST_NODE_FLAG_GLOBAL;
  // TODO: Do not define this function to avoid recursive calls to it.
  ast_push(parser, fn_start, allocator);

  for (u64 _i = 0; _i < parser->lexer.tokens.len;) {
    if (parser->tokens_consumed >= parser->lexer.tokens.len) {
      break;
    }

    if (!ast_parse_declaration(parser, allocator)) {
      continue;
    }
  }

  ast_emit_program_epilog(parser, allocator);
}
