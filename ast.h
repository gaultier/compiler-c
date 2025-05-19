#pragma once
#include "error.h"
#include "lex.h"
#include "origin.h"
#include "submodules/cstd/lib.c"

typedef enum {
  AST_NODE_KIND_NONE,
  AST_NODE_KIND_U64,
  AST_NODE_KIND_IDENTIFIER,
  AST_NODE_KIND_ADD,
  AST_NODE_KIND_BLOCK,
  AST_NODE_KIND_VAR_DEFINITION,
  AST_NODE_KIND_ADDRESS_OF,
  AST_NODE_KIND_IF,
  AST_NODE_KIND_COMPARISON,
  AST_NODE_KIND_BUILTIN_ASSERT,
  AST_NODE_KIND_SYSCALL,
  AST_NODE_KIND_FN_DEFINITION,
} AstNodeKind;

typedef struct AstNode AstNode;
PG_SLICE(AstNode) AstNodeSlice;
PG_DYN(AstNode) AstNodeDyn;

typedef enum [[clang::flag_enum]] {
  AST_NODE_FLAG_NONE = 0,
  AST_NODE_FLAG_GLOBAL = 1 << 0,
  AST_NODE_FLAG_FN_NO_FRAME_POINTERS = 1 << 1,
} AstNodeFlag;

struct AstNode {
  AstNodeKind kind;
  AstNodeDyn operands;
  union {
    u64 n64;
    PgString identifier;
  } u;
  Origin origin;
  LexTokenKind token_kind;
  AstNodeFlag flags;
};

typedef struct {
  Lexer lexer;
  u64 tokens_consumed;
  ErrorDyn *errors;
  AstNode *root;
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

static void ast_print(AstNode node, u32 left_width) {
  for (u64 i = 0; i < left_width; i++) {
    putchar(' ');
  }
  origin_print(node.origin);
  putchar(' ');

  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64:
    printf("U64(%" PRIu64 ")\n", node.u.n64);
    break;
  case AST_NODE_KIND_IDENTIFIER:
    printf("Identifier(%.*s)\n", (i32)node.u.identifier.len,
           node.u.identifier.data);
    break;
  case AST_NODE_KIND_ADDRESS_OF:
    printf("AddressOf(\n");
    PG_ASSERT(1 == node.operands.len);
    ast_print(PG_SLICE_AT(node.operands, 0), left_width + 2);
    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
    break;
  case AST_NODE_KIND_BUILTIN_ASSERT:
    printf("Assert(\n");
    PG_ASSERT(1 == node.operands.len);
    ast_print(PG_SLICE_AT(node.operands, 0), left_width + 2);
    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
    break;
  case AST_NODE_KIND_ADD:
    printf("Add(\n");
    PG_ASSERT(2 == node.operands.len);
    ast_print(PG_SLICE_AT(node.operands, 0), left_width + 2);
    ast_print(PG_SLICE_AT(node.operands, 1), left_width + 2);

    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
    break;
  case AST_NODE_KIND_COMPARISON:
    printf("Comparison(\n");
    PG_ASSERT(2 == node.operands.len);
    ast_print(PG_SLICE_AT(node.operands, 0), left_width + 2);
    ast_print(PG_SLICE_AT(node.operands, 1), left_width + 2);

    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
    break;
  case AST_NODE_KIND_SYSCALL: {
    PG_ASSERT(node.operands.len > 0);
    printf("Syscall(\n");
    for (u64 i = 0; i < node.operands.len; i++) {
      ast_print(PG_SLICE_AT(node.operands, i), left_width + 2);
    }

    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
  } break;
  case AST_NODE_KIND_BLOCK: {
    printf("Block\n");
    for (u64 i = 0; i < node.operands.len; i++) {
      ast_print(PG_SLICE_AT(node.operands, i), left_width + 2);
    }
  } break;
  case AST_NODE_KIND_VAR_DEFINITION:
    PG_ASSERT(1 == node.operands.len);

    printf("VarDecl(%.*s\n", (i32)node.u.identifier.len,
           node.u.identifier.data);
    ast_print(PG_SLICE_AT(node.operands, 0), left_width + 2);
    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
    break;
  case AST_NODE_KIND_IF:
    PG_ASSERT(2 == node.operands.len);
    printf("If(\n");
    ast_print(PG_SLICE_AT(node.operands, 0), left_width + 2);
    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(",\n");

    ast_print(PG_SLICE_AT(node.operands, 1), left_width + 2);

    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
    break;

  case AST_NODE_KIND_FN_DEFINITION:
    printf("FnDefinition(%.*s,\n", (i32)node.u.identifier.len,
           node.u.identifier.data);
    for (u64 i = 0; i < node.operands.len; i++) {
      ast_print(PG_SLICE_AT(node.operands, i), left_width + 2);
    }
    break;

  default:
    PG_ASSERT(0);
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

static AstNode *ast_parse_expr(AstParser *parser, PgAllocator *allocator);
static AstNode *ast_parse_statement(AstParser *parser, PgAllocator *allocator);
static AstNode *ast_parse_declaration(AstParser *parser,
                                      PgAllocator *allocator);
static AstNode *ast_parse_syscall(AstParser *parser, PgAllocator *allocator);
static AstNode *ast_parse_var_decl(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_IDENTIFIER);
  if (!token_first.kind) {
    return nullptr;
  }
  PG_ASSERT(!pg_string_is_empty(token_first.s));

  LexToken token_colon_equal =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_COLON_EQUAL);
  if (!token_colon_equal.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNode *rhs = ast_parse_expr(parser, allocator);
  if (!rhs) {
    ast_add_error(parser, ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->kind = AST_NODE_KIND_VAR_DEFINITION;
  res->origin = token_first.origin;
  res->u.identifier = token_first.s;
  *PG_DYN_PUSH(&res->operands, allocator) = *rhs;

  return res;
}

static AstNode *ast_parse_primary(AstParser *parser, PgAllocator *allocator) {
  LexToken first = ast_match_token_kind1_or_kind2(
      parser, LEX_TOKEN_KIND_LITERAL_U64, LEX_TOKEN_KIND_IDENTIFIER);

  if (LEX_TOKEN_KIND_LITERAL_U64 == first.kind) {
    AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    res->origin = first.origin;
    res->kind = AST_NODE_KIND_U64;
    PgParseNumberResult parse_res = pg_string_parse_u64(first.s);
    PG_ASSERT(parse_res.present);
    PG_ASSERT(pg_string_is_empty(parse_res.remaining));
    res->u.n64 = parse_res.n;

    return res;
  }

  if (LEX_TOKEN_KIND_IDENTIFIER == first.kind) {
    AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    res->origin = first.origin;
    res->kind = AST_NODE_KIND_IDENTIFIER;
    res->u.identifier = first.s;

    return res;
  }

  return nullptr;
}

static AstNode *ast_parse_call(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_primary(parser, allocator);
}

static AstNode *ast_parse_unary(AstParser *parser, PgAllocator *allocator) {

  LexToken token_first = ast_match_token_kind(parser, LEX_TOKEN_KIND_AMPERSAND);
  if (!token_first.kind) {
    return ast_parse_call(parser, allocator);
  }

  AstNode *rhs = ast_parse_unary(parser, allocator);
  if (!rhs) {
    ast_add_error(parser, ERROR_KIND_PARSE_UNARY_MISSING_RHS,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  if (AST_NODE_KIND_IDENTIFIER != rhs->kind) {
    ast_add_error(parser, ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = token_first.origin;
  res->kind = AST_NODE_KIND_ADDRESS_OF;
  *PG_DYN_PUSH(&res->operands, allocator) = *rhs;
  return res;
}

static AstNode *ast_parse_factor(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_unary(parser, allocator);
}

static AstNode *ast_parse_term(AstParser *parser, PgAllocator *allocator) {
  AstNode *lhs = ast_parse_factor(parser, allocator);
  if (!lhs) {
    return nullptr;
  }

  LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_PLUS);
  if (!token.kind) {
    return lhs;
  }

  AstNode *rhs = ast_parse_term(parser, allocator);
  if (!rhs) {
    ast_add_error(parser, ERROR_KIND_PARSE_FACTOR_MISSING_RHS,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = lhs->origin;
  res->kind = AST_NODE_KIND_ADD;
  *PG_DYN_PUSH(&res->operands, allocator) = *lhs;
  *PG_DYN_PUSH(&res->operands, allocator) = *rhs;

  return res;
}

static AstNode *ast_parse_comparison(AstParser *parser,
                                     PgAllocator *allocator) {
  return ast_parse_term(parser, allocator);
}

static AstNode *ast_parse_equality(AstParser *parser, PgAllocator *allocator) {
  AstNode *lhs = ast_parse_comparison(parser, allocator);
  if (!lhs) {
    return nullptr;
  }

  LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_EQUAL_EQUAL);
  // TODO: `!=`.
  if (!token.kind) {
    return lhs;
  }

  AstNode *rhs = ast_parse_equality(parser, allocator);
  if (!rhs) {
    ast_add_error(parser, ERROR_KIND_PARSE_EQUALITY_MISSING_RHS,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = token.origin;
  res->kind = AST_NODE_KIND_COMPARISON;
  res->token_kind = token.kind;
  *PG_DYN_PUSH(&res->operands, allocator) = *lhs;
  *PG_DYN_PUSH(&res->operands, allocator) = *rhs;

  return res;
}

static AstNode *ast_parse_logic_and(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_equality(parser, allocator);
}

static AstNode *ast_parse_logic_or(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_logic_and(parser, allocator);
}

static AstNode *ast_parse_assignment(AstParser *parser,
                                     PgAllocator *allocator) {
  return ast_parse_logic_or(parser, allocator);
}

static AstNode *ast_parse_expr(AstParser *parser, PgAllocator *allocator) {
  AstNode *res = nullptr;

  if ((res = ast_parse_syscall(parser, allocator))) {
    return res;
  }

  if ((res = ast_parse_assignment(parser, allocator))) {
    return res;
  }
  return nullptr;
}

static AstNode *ast_parse_syscall(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_SYSCALL);
  if (!token_first.kind) {
    return nullptr;
  }

  LexToken token_left_paren =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_LEFT);
  if (!token_left_paren.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_LEFT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNodeDyn operands = {0};

  LexToken token_after = {0};

  while (parser->tokens_consumed < parser->lexer.tokens.len) {
    LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
    if (LEX_TOKEN_KIND_PAREN_RIGHT == token.kind) {
      break;
    }

    AstNode *operand = ast_parse_expr(parser, allocator);
    if (!operand) {
      ast_add_error(parser, ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND,
                    ast_current_or_last_token(*parser).origin, allocator);
      return nullptr;
    }
    *PG_DYN_PUSH(&operands, allocator) = *operand;

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
    return nullptr;
  }

  if (LEX_TOKEN_KIND_PAREN_RIGHT != token_after.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_RIGHT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = token_first.origin;
  res->kind = AST_NODE_KIND_SYSCALL;
  res->operands = operands;

  return res;
}

static AstNode *ast_parse_block(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_CURLY_LEFT);
  if (!token_first.kind) {
    return nullptr;
  }

  AstNodeDyn operands = {0};
  for (u64 _i = parser->tokens_consumed; _i < parser->lexer.tokens.len; _i++) {
    LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_CURLY_RIGHT);
    if (token.kind) {
      AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
      res->origin = token_first.origin;
      res->kind = AST_NODE_KIND_BLOCK;
      res->operands = operands;
      return res;
    }

    AstNode *operand = ast_parse_declaration(parser, allocator);
    if (!operand) {
      break; // EOF?
    }
    *PG_DYN_PUSH(&operands, allocator) = *operand;
  }

  ast_add_error(parser, ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT,
                ast_current_or_last_token(*parser).origin, allocator);
  return nullptr;
}

static AstNode *ast_parse_statement_if(AstParser *parser,
                                       PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_IF);
  if (!token_first.kind) {
    return nullptr;
  }

  AstNodeDyn operands = {0};

  AstNode *cond = ast_parse_expr(parser, allocator);
  if (!cond) {
    ast_add_error(parser, ERROR_KIND_PARSE_IF_MISSING_CONDITION,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }
  *PG_DYN_PUSH(&operands, allocator) = *cond;

  AstNode *if_body = ast_parse_block(parser, allocator);
  if (!if_body) {
    ast_add_error(parser, ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK,
                  token_first.origin, allocator);
    return nullptr;
  }
  *PG_DYN_PUSH(&operands, allocator) = *if_body;

  // TODO: optional else.

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = token_first.origin;
  res->kind = AST_NODE_KIND_IF;
  res->operands = operands;

  return res;
}

static AstNode *ast_parse_statement_assert(AstParser *parser,
                                           PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_ASSERT);
  if (!token_first.kind) {
    return nullptr;
  }

  LexToken token_paren_left =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_LEFT);
  if (!token_paren_left.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_LEFT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNodeDyn operands = {0};

  AstNode *expr = ast_parse_expr(parser, allocator);
  if (!expr) {
    ast_add_error(parser, ERROR_KIND_PARSE_ASSERT_MISSING_EXPRESSION,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }
  *PG_DYN_PUSH(&operands, allocator) = *expr;

  LexToken token_paren_right =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_RIGHT);
  if (!token_paren_right.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_RIGHT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = token_first.origin;
  res->kind = AST_NODE_KIND_BUILTIN_ASSERT;
  res->operands = operands;

  return res;
}

static AstNode *ast_parse_statement(AstParser *parser, PgAllocator *allocator) {
  AstNode *res = nullptr;

  if ((res = ast_parse_statement_if(parser, allocator))) {
    return res;
  }

  if ((res = ast_parse_statement_assert(parser, allocator))) {
    return res;
  }

  if ((res = ast_parse_expr(parser, allocator))) {
    return res;
  }

  return res;
}

static AstNode *ast_parse_declaration(AstParser *parser,
                                      PgAllocator *allocator) {
  AstNode *res = nullptr;
  if ((res = ast_parse_var_decl(parser, allocator))) {
    return res;
  }

  return ast_parse_statement(parser, allocator);
}

static void ast_emit_program_epilog(AstNode *parent, PgAllocator *allocator) {

  {
    AstNode *fn_exit =
        pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    fn_exit->kind = AST_NODE_KIND_FN_DEFINITION;
    fn_exit->u.identifier = PG_S("__builtin_exit");
    fn_exit->flags = AST_NODE_FLAG_FN_NO_FRAME_POINTERS;

    AstNode *syscall =
        pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    syscall->kind = AST_NODE_KIND_SYSCALL;

    AstNode *op0 = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    op0->kind = AST_NODE_KIND_U64;
    op0->u.n64 = 60; // FIXME: Only on Linux amd64.
    *PG_DYN_PUSH(&syscall->operands, allocator) = *op0;

    AstNode *op1 = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    op1->kind = AST_NODE_KIND_U64;
    op1->u.n64 = 0;
    *PG_DYN_PUSH(&syscall->operands, allocator) = *op1;

    *PG_DYN_PUSH(&fn_exit->operands, allocator) = *syscall;

    *PG_DYN_PUSH(&parent->operands, allocator) = *fn_exit;
  }
  {
    AstNode *fn_die =
        pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    fn_die->kind = AST_NODE_KIND_FN_DEFINITION;
    fn_die->u.identifier = PG_S("__builtin_die");
    fn_die->flags = AST_NODE_FLAG_FN_NO_FRAME_POINTERS;

    AstNode *syscall =
        pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    syscall->kind = AST_NODE_KIND_SYSCALL;

    AstNode *op0 = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    op0->kind = AST_NODE_KIND_U64;
    op0->u.n64 = 60; // FIXME: Only on Linux amd64.
    *PG_DYN_PUSH(&syscall->operands, allocator) = *op0;

    AstNode *op1 = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    op1->kind = AST_NODE_KIND_U64;
    op1->u.n64 = 1;
    *PG_DYN_PUSH(&syscall->operands, allocator) = *op1;

    *PG_DYN_PUSH(&fn_die->operands, allocator) = *syscall;

    *PG_DYN_PUSH(&parent->operands, allocator) = *fn_die;
  }
}

static void ast_emit(AstParser *parser, PgAllocator *allocator) {
  parser->root = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  parser->root->kind = AST_NODE_KIND_BLOCK;

  AstNode *fn_start =
      pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  fn_start->kind = AST_NODE_KIND_FN_DEFINITION;
  fn_start->u.identifier = PG_S("_start");
  fn_start->flags = AST_NODE_FLAG_GLOBAL;

  for (u64 _i = 0; _i < parser->lexer.tokens.len;) {
    if (parser->tokens_consumed >= parser->lexer.tokens.len) {
      break;
    }

    AstNode *statement = ast_parse_declaration(parser, allocator);

    if (!statement) {
      break;
    }

    PG_ASSERT(statement);

    *PG_DYN_PUSH(&fn_start->operands, allocator) = *statement;
  }

  *PG_DYN_PUSH(&parser->root->operands, allocator) = *fn_start;

  ast_emit_program_epilog(parser->root, allocator);
}
