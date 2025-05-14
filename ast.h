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
  AST_NODE_KIND_VAR_DECL,
  AST_NODE_KIND_ADDRESS_OF,
  AST_NODE_KIND_IF,
  AST_NODE_KIND_COMPARISON,
  AST_NODE_KIND_BUILTIN_ASSERT,
#if 0
  AST_NODE_KIND_SYSCALL,
#endif
} AstNodeKind;

typedef struct AstNode AstNode;
PG_SLICE(AstNode) AstNodeSlice;
PG_DYN(AstNode) AstNodeDyn;

struct AstNode {
  AstNodeKind kind;
  AstNodeDyn operands;
  u64 n64;
  PgString identifier;
  Origin origin;
  LexTokenKind token_kind;
};

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
    printf("U64(%" PRIu64 ")\n", node.n64);
    break;
  case AST_NODE_KIND_IDENTIFIER:
    printf("Identifier(%.*s)\n", (i32)node.identifier.len,
           node.identifier.data);
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
#if 0
  case AST_NODE_KIND_SYSCALL: {
    printf("Syscall(\n");
    for (u64 i = 0; i < node.operands.len; i++) {
      ast_print(PG_SLICE_AT(node.operands, i), left_width + 2);
    }

    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
  } break;
#endif
  case AST_NODE_KIND_BLOCK: {
    printf("Block\n");
    for (u64 i = 0; i < node.operands.len; i++) {
      ast_print(PG_SLICE_AT(node.operands, i), left_width + 2);
    }
  } break;
  case AST_NODE_KIND_VAR_DECL:
    PG_ASSERT(1 == node.operands.len);

    printf("VarDecl(%.*s\n", (i32)node.identifier.len, node.identifier.data);
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

  default:
    PG_ASSERT(0);
  }
}

static AstNode *ast_parse_expr(LexTokenSlice tokens, ErrorDyn *errors,
                               u64 *tokens_consumed, PgAllocator *allocator);
static AstNode *ast_parse_statement(LexTokenSlice tokens, ErrorDyn *errors,
                                    u64 *tokens_consumed,
                                    PgAllocator *allocator);
static AstNode *ast_parse_declaration(LexTokenSlice tokens, ErrorDyn *errors,
                                      u64 *tokens_consumed,
                                      PgAllocator *allocator);
#if 0
static AstNode *ast_parse_syscall(LexTokenSlice tokens, ErrorDyn *errors,
                                  u64 *tokens_consumed, PgAllocator *allocator);
#endif

static AstNode *ast_parse_var_decl(LexTokenSlice tokens, ErrorDyn *errors,
                                   u64 *tokens_consumed,
                                   PgAllocator *allocator) {

  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  LexToken token_first = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_IDENTIFIER != token_first.kind) {
    return nullptr;
  }
  PG_ASSERT(!pg_string_is_empty(token_first.s));

  *tokens_consumed += 1;

  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }
  LexToken token_colon_equal = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_COLON_EQUAL != token_colon_equal.kind) {
    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL,
        .origin = token_colon_equal.origin,
    };
    return nullptr;
  }

  *tokens_consumed += 1;

  AstNode *rhs = ast_parse_expr(tokens, errors, tokens_consumed, allocator);
  if (!rhs) {
    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE,
        .origin = token_colon_equal.origin,
    };
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->kind = AST_NODE_KIND_VAR_DECL;
  res->origin = token_first.origin;
  res->identifier = token_first.s;
  *PG_DYN_PUSH(&res->operands, allocator) = *rhs;

  return res;
}

static AstNode *ast_parse_primary(LexTokenSlice tokens, ErrorDyn *errors,
                                  u64 *tokens_consumed,
                                  PgAllocator *allocator) {
  (void)errors;

  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  LexToken first = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_LITERAL_U64 == first.kind) {
    AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    res->origin = first.origin;
    res->kind = AST_NODE_KIND_U64;
    PgParseNumberResult parse_res = pg_string_parse_u64(first.s);
    PG_ASSERT(parse_res.present);
    PG_ASSERT(pg_string_is_empty(parse_res.remaining));
    res->n64 = parse_res.n;

    *tokens_consumed += 1;

    return res;
  }

  if (LEX_TOKEN_KIND_IDENTIFIER == first.kind) {
    AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
    res->origin = first.origin;
    res->kind = AST_NODE_KIND_IDENTIFIER;
    res->identifier = first.s;

    *tokens_consumed += 1;

    return res;
  }

  return nullptr;
}

static AstNode *ast_parse_call(LexTokenSlice tokens, ErrorDyn *errors,
                               u64 *tokens_consumed, PgAllocator *allocator) {
  return ast_parse_primary(tokens, errors, tokens_consumed, allocator);
}

static AstNode *ast_parse_unary(LexTokenSlice tokens, ErrorDyn *errors,
                                u64 *tokens_consumed, PgAllocator *allocator) {

  if (*tokens_consumed < tokens.len) {
    LexToken token_first = PG_SLICE_AT(tokens, *tokens_consumed);
    if (LEX_TOKEN_KIND_AMPERSAND == token_first.kind) {
      *tokens_consumed += 1;

      AstNode *rhs =
          ast_parse_unary(tokens, errors, tokens_consumed, allocator);
      if (!rhs) {
        *PG_DYN_PUSH(errors, allocator) = (Error){
            .kind = ERROR_KIND_PARSE_UNARY_MISSING_RHS,
            .origin = token_first.origin,
        };
        return nullptr;
      }

      if (AST_NODE_KIND_IDENTIFIER != rhs->kind) {
        *PG_DYN_PUSH(errors, allocator) = (Error){
            .kind = ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER,
            .origin = token_first.origin,
        };
        return nullptr;
      }

      AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
      res->origin = token_first.origin;
      res->kind = AST_NODE_KIND_ADDRESS_OF;
      *PG_DYN_PUSH(&res->operands, allocator) = *rhs;
      return res;
    }
  }

  return ast_parse_call(tokens, errors, tokens_consumed, allocator);
}

static AstNode *ast_parse_factor(LexTokenSlice tokens, ErrorDyn *errors,
                                 u64 *tokens_consumed, PgAllocator *allocator) {
  return ast_parse_unary(tokens, errors, tokens_consumed, allocator);
}

static AstNode *ast_parse_term(LexTokenSlice tokens, ErrorDyn *errors,
                               u64 *tokens_consumed, PgAllocator *allocator) {
  AstNode *lhs = ast_parse_factor(tokens, errors, tokens_consumed, allocator);
  if (!lhs) {
    // TODO: Err?
    return nullptr;
  }

  if (*tokens_consumed >= tokens.len) {
    return lhs;
  }

  LexToken op = PG_SLICE_AT(tokens, *tokens_consumed);
  if (!(LEX_TOKEN_KIND_PLUS == op.kind)) {
    return lhs;
  }

  *tokens_consumed += 1;
  AstNode *rhs = ast_parse_term(tokens, errors, tokens_consumed, allocator);
  if (!rhs) {
    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_PARSE_FACTOR_MISSING_RHS,
        .origin = op.origin,
    };
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = lhs->origin;
  res->kind = AST_NODE_KIND_ADD;
  *PG_DYN_PUSH(&res->operands, allocator) = *lhs;
  *PG_DYN_PUSH(&res->operands, allocator) = *rhs;

  return res;
}

static AstNode *ast_parse_comparison(LexTokenSlice tokens, ErrorDyn *errors,
                                     u64 *tokens_consumed,
                                     PgAllocator *allocator) {
  return ast_parse_term(tokens, errors, tokens_consumed, allocator);
}

static AstNode *ast_parse_equality(LexTokenSlice tokens, ErrorDyn *errors,
                                   u64 *tokens_consumed,
                                   PgAllocator *allocator) {
  AstNode *lhs =
      ast_parse_comparison(tokens, errors, tokens_consumed, allocator);
  if (!lhs) {
    return nullptr;
  }

  if (*tokens_consumed >= tokens.len) {
    return lhs;
  }

  LexToken op = PG_SLICE_AT(tokens, *tokens_consumed);
  // TODO: `!=`.
  if (!(LEX_TOKEN_KIND_EQUAL_EQUAL == op.kind)) {
    return lhs;
  }

  *tokens_consumed += 1;
  AstNode *rhs = ast_parse_equality(tokens, errors, tokens_consumed, allocator);
  if (!rhs) {
    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_PARSE_EQUALITY_MISSING_RHS,
        .origin = op.origin,
    };
    return nullptr;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = op.origin;
  res->kind = AST_NODE_KIND_COMPARISON;
  res->token_kind = op.kind;
  *PG_DYN_PUSH(&res->operands, allocator) = *lhs;
  *PG_DYN_PUSH(&res->operands, allocator) = *rhs;

  return res;
}

static AstNode *ast_parse_logic_and(LexTokenSlice tokens, ErrorDyn *errors,
                                    u64 *tokens_consumed,
                                    PgAllocator *allocator) {
  return ast_parse_equality(tokens, errors, tokens_consumed, allocator);
}

static AstNode *ast_parse_logic_or(LexTokenSlice tokens, ErrorDyn *errors,
                                   u64 *tokens_consumed,
                                   PgAllocator *allocator) {
  return ast_parse_logic_and(tokens, errors, tokens_consumed, allocator);
}

static AstNode *ast_parse_assignment(LexTokenSlice tokens, ErrorDyn *errors,
                                     u64 *tokens_consumed,
                                     PgAllocator *allocator) {
  return ast_parse_logic_or(tokens, errors, tokens_consumed, allocator);
}

static AstNode *ast_parse_expr(LexTokenSlice tokens, ErrorDyn *errors,
                               u64 *tokens_consumed, PgAllocator *allocator) {
  AstNode *res = nullptr;

#if 0
  if ((res = ast_parse_syscall(tokens, errors, tokens_consumed, allocator))) {
    return res;
  }
#endif

  if ((res =
           ast_parse_assignment(tokens, errors, tokens_consumed, allocator))) {
    return res;
  }
  return nullptr;
}

#if 0
static AstNode *ast_parse_syscall(LexTokenSlice tokens, ErrorDyn *errors,
                                  u64 *tokens_consumed,
                                  PgAllocator *allocator) {
  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  LexToken token_first = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_KEYWORD_SYSCALL != token_first.kind) {
    return nullptr;
  }

  *tokens_consumed += 1;

  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  {
    LexToken token_left_paren = PG_SLICE_AT(tokens, *tokens_consumed);
    if (LEX_TOKEN_KIND_PAREN_LEFT != token_left_paren.kind) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_PARSE_SYSCALL_MISSING_LEFT_PAREN,
          .origin = token_left_paren.origin,
      };
      return nullptr;
    }

    *tokens_consumed += 1;

    if (*tokens_consumed >= tokens.len) {
      return nullptr;
    }
  }

  AstNodeDyn operands = {0};

  while (*tokens_consumed < tokens.len) {
    LexToken token = PG_SLICE_AT(tokens, *tokens_consumed);
    if (LEX_TOKEN_KIND_PAREN_RIGHT == token.kind) {
      break;
    }

    AstNode *operand =
        ast_parse_expr(tokens, errors, tokens_consumed, allocator);
    if (!operand) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND,
          .origin = token.origin,
      };
      return nullptr;
    }
    *PG_DYN_PUSH(&operands, allocator) = *operand;

    LexToken token_after = PG_SLICE_AT(tokens, *tokens_consumed);
    if (LEX_TOKEN_KIND_PAREN_RIGHT == token_after.kind) {
      break;
    }
    if (LEX_TOKEN_KIND_COMMA == token_after.kind) {
      *tokens_consumed += 1;
      continue;
    }

    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_PARSE_SYSCALL_MISSING_COMMA,
        .origin = token_after.origin,
    };
    return nullptr;
  }

  {
    LexToken token_right_paren = PG_SLICE_AT(tokens, *tokens_consumed);
    if (LEX_TOKEN_KIND_PAREN_RIGHT != token_right_paren.kind) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_PARSE_SYSCALL_MISSING_RIGHT_PAREN,
          .origin = token_right_paren.origin,
      };
      return nullptr;
    }

    *tokens_consumed += 1;
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = token_first.origin;
  res->kind = AST_NODE_KIND_SYSCALL;
  res->operands = operands;

  return res;
}
#endif

static AstNode *ast_parse_block(LexTokenSlice tokens, ErrorDyn *errors,
                                u64 *tokens_consumed, PgAllocator *allocator) {
  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  LexToken token_first = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_CURLY_LEFT != token_first.kind) {
    return nullptr;
  }

  *tokens_consumed += 1;

  AstNodeDyn operands = {0};
  for (u64 _i = *tokens_consumed; _i < tokens.len; _i++) {
    LexToken token = PG_SLICE_AT(tokens, *tokens_consumed);
    if (LEX_TOKEN_KIND_CURLY_RIGHT == token.kind) {
      *tokens_consumed += 1;

      AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
      res->origin = token_first.origin;
      res->kind = AST_NODE_KIND_BLOCK;
      res->operands = operands;
      return res;
    }

    AstNode *operand =
        ast_parse_declaration(tokens, errors, tokens_consumed, allocator);
    if (!operand) {
      break; // EOF?
    }
    *PG_DYN_PUSH(&operands, allocator) = *operand;
  }

  *PG_DYN_PUSH(errors, allocator) = (Error){
      .kind = ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT,
      .origin = token_first.origin,
  };
  return nullptr;
}

static AstNode *ast_parse_statement_if(LexTokenSlice tokens, ErrorDyn *errors,
                                       u64 *tokens_consumed,
                                       PgAllocator *allocator) {
  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  LexToken token_first = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_KEYWORD_IF != token_first.kind) {
    return nullptr;
  }

  *tokens_consumed += 1;

  AstNodeDyn operands = {0};

  AstNode *cond = ast_parse_expr(tokens, errors, tokens_consumed, allocator);
  if (!cond) {
    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_PARSE_IF_MISSING_CONDITION,
        .origin = token_first.origin,
    };
    return nullptr;
  }
  *PG_DYN_PUSH(&operands, allocator) = *cond;

  AstNode *if_body =
      ast_parse_block(tokens, errors, tokens_consumed, allocator);
  if (!if_body) {
    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK,
        .origin = token_first.origin,
    };
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

static AstNode *ast_parse_statement_assert(LexTokenSlice tokens,
                                           ErrorDyn *errors,
                                           u64 *tokens_consumed,
                                           PgAllocator *allocator) {
  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  LexToken token_first = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_KEYWORD_ASSERT != token_first.kind) {
    return nullptr;
  }
  *tokens_consumed += 1;

  LexToken token_paren_left = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_PAREN_LEFT != token_paren_left.kind) {
    error_add(errors, ERROR_KIND_PARSE_MISSING_PAREN_LEFT, token_first.origin,
              allocator);
    return nullptr;
  }
  *tokens_consumed += 1;

  AstNodeDyn operands = {0};

  AstNode *expr = ast_parse_expr(tokens, errors, tokens_consumed, allocator);
  if (!expr) {
    error_add(errors, ERROR_KIND_PARSE_ASSERT_MISSING_EXPRESSION,
              token_paren_left.origin, allocator);
    return nullptr;
  }
  *PG_DYN_PUSH(&operands, allocator) = *expr;

  LexToken token_paren_right = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_PAREN_RIGHT != token_paren_right.kind) {
    error_add(errors, ERROR_KIND_PARSE_MISSING_PAREN_RIGHT, token_first.origin,
              allocator);
    return nullptr;
  }
  *tokens_consumed += 1;

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = token_first.origin;
  res->kind = AST_NODE_KIND_BUILTIN_ASSERT;
  res->operands = operands;

  return res;
}

static AstNode *ast_parse_statement(LexTokenSlice tokens, ErrorDyn *errors,
                                    u64 *tokens_consumed,
                                    PgAllocator *allocator) {
  AstNode *res = nullptr;

  if ((res = ast_parse_statement_if(tokens, errors, tokens_consumed,
                                    allocator))) {
    return res;
  }

  if ((res = ast_parse_statement_assert(tokens, errors, tokens_consumed,
                                        allocator))) {
    return res;
  }

  if ((res = ast_parse_expr(tokens, errors, tokens_consumed, allocator))) {
    return res;
  }

  return res;
}

static AstNode *ast_parse_declaration(LexTokenSlice tokens, ErrorDyn *errors,
                                      u64 *tokens_consumed,
                                      PgAllocator *allocator) {
  AstNode *res = nullptr;
  if ((res = ast_parse_var_decl(tokens, errors, tokens_consumed, allocator))) {
    return res;
  }

  return ast_parse_statement(tokens, errors, tokens_consumed, allocator);
}

static AstNode *ast_emit(LexTokenSlice tokens, ErrorDyn *errors,
                         PgAllocator *allocator) {

  AstNode *root = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  root->kind = AST_NODE_KIND_BLOCK;

  for (u64 tokens_idx = 0; tokens_idx < tokens.len;) {
    LexTokenSlice remaining = PG_SLICE_RANGE_START(tokens, tokens_idx);
    if (PG_SLICE_IS_EMPTY(remaining)) {
      break;
    }

    u64 tokens_consumed = 0;
    AstNode *statement =
        ast_parse_declaration(remaining, errors, &tokens_consumed, allocator);

    if (!statement) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_PARSE_STATEMENT,
          .origin = PG_SLICE_AT(remaining, 0).origin,
      };
      break;
    }

    PG_ASSERT(statement);

    *PG_DYN_PUSH(&root->operands, allocator) = *statement;

    tokens_idx += tokens_consumed;
  }

  return root;
}
