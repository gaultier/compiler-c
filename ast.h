#pragma once
#include "lex.h"
#include "origin.h"
#include "submodules/cstd/lib.c"

typedef enum {
  AST_NODE_KIND_NONE,
  AST_NODE_KIND_U64,
  AST_NODE_KIND_ADD,
  AST_NODE_KIND_SYSCALL,
  AST_NODE_KIND_BLOCK,
} AstNodeKind;

typedef struct AstNode AstNode;
PG_SLICE(AstNode) AstNodeSlice;
PG_DYN(AstNode) AstNodeDyn;

struct AstNode {
  AstNodeKind kind;
  AstNodeDyn operands;
  u64 n64;
  Origin origin;
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
  case AST_NODE_KIND_ADD:
    printf("Add(\n");
    PG_ASSERT(2 == node.operands.len);
    ast_print(PG_SLICE_AT(node.operands, 0), left_width + 2);

    for (u64 i = 0; i < left_width + 2; i++) {
      putchar(' ');
    }
    printf(",\n");

    ast_print(PG_SLICE_AT(node.operands, 1), left_width + 2);

    for (u64 i = 0; i < left_width; i++) {
      putchar(' ');
    }
    printf(")\n");
    break;
  case AST_NODE_KIND_SYSCALL: {
    printf("Syscall(\n");
    for (u64 i = 0; i < node.operands.len; i++) {
      ast_print(PG_SLICE_AT(node.operands, i), left_width + 2);
      for (u64 j = 0; j < left_width + 2; j++) {
        putchar(' ');
      }
      printf(",\n");
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

    printf("\n");
  } break;
  default:
    PG_ASSERT(0);
  }
}

static AstNode *ast_parse_expr(LexTokenSlice tokens, ErrorDyn *errors,
                               u64 *tokens_consumed, PgAllocator *allocator);

static AstNode *ast_parse_literal(LexTokenSlice tokens, ErrorDyn *errors,
                                  u64 *tokens_consumed,
                                  PgAllocator *allocator) {
  (void)errors;

  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  LexToken first = PG_SLICE_AT(tokens, 0);
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

  return nullptr;
}

static AstNode *ast_parse_add(LexTokenSlice tokens, ErrorDyn *errors,
                              u64 *tokens_consumed, PgAllocator *allocator) {
  AstNode *res = nullptr;
  AstNode *lhs = ast_parse_literal(tokens, errors, tokens_consumed, allocator);
  if (!lhs) {
    return nullptr;
  }

  if (*tokens_consumed >= tokens.len) {
    return lhs;
  }

  LexToken op = PG_SLICE_AT(tokens, *tokens_consumed);
  if (LEX_TOKEN_KIND_PLUS != op.kind) {
    return lhs;
  }

  *tokens_consumed += 1;
  AstNode *rhs = ast_parse_expr(tokens, errors, tokens_consumed, allocator);
  if (!rhs) {
    *PG_DYN_PUSH(errors, allocator) = (Error){
        .kind = ERROR_KIND_PARSE_BINARY_OP_MISSING_RHS,
        .origin = op.origin,
    };
    return nullptr;
  }

  res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = lhs->origin;
  res->kind = AST_NODE_KIND_ADD;
  *PG_DYN_PUSH(&res->operands, allocator) = *lhs;
  *PG_DYN_PUSH(&res->operands, allocator) = *rhs;

  return res;
}

static AstNode *ast_parse_expr(LexTokenSlice tokens, ErrorDyn *errors,
                               u64 *tokens_consumed, PgAllocator *allocator) {
  AstNode *res = nullptr;
  if ((res = ast_parse_add(tokens, errors, tokens_consumed, allocator))) {
    return res;
  }
  return nullptr;
}

static AstNode *ast_parse_syscall(LexTokenSlice tokens, ErrorDyn *errors,
                                  u64 *tokens_consumed,
                                  PgAllocator *allocator) {
  if (*tokens_consumed >= tokens.len) {
    return nullptr;
  }

  LexToken token_first = PG_SLICE_AT(tokens, 0);
  if (LEX_TOKEN_KIND_SYSCALL != token_first.kind) {
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

  // TODO: parse operands;

  {
    LexToken token_right_paren = PG_SLICE_AT(tokens, *tokens_consumed);
    if (LEX_TOKEN_KIND_PAREN_RIGHT != token_right_paren.kind) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_PARSE_SYSCALL_MISSING_RIGHT_PAREN,
          .origin = token_right_paren.origin,
      };
      return nullptr;
    }
  }

  AstNode *res = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  res->origin = token_first.origin;
  res->kind = AST_NODE_KIND_SYSCALL;
  res->operands = operands;

  return res;
}

static AstNode *ast_parse_statement(LexTokenSlice tokens, ErrorDyn *errors,
                                    u64 *tokens_consumed,
                                    PgAllocator *allocator) {
  AstNode *res = nullptr;

  if ((res = ast_parse_syscall(tokens, errors, tokens_consumed, allocator))) {
    return res;
  }

  if ((res = ast_parse_expr(tokens, errors, tokens_consumed, allocator))) {
    return res;
  }

  return res;
}

static AstNode *lex_to_ast(LexTokenSlice tokens, ErrorDyn *errors,
                           PgAllocator *allocator) {
  AstNode *root = pg_alloc(allocator, sizeof(AstNode), _Alignof(AstNode), 1);
  root->kind = AST_NODE_KIND_BLOCK;
  root->origin.synthetic = true;

  for (u64 tokens_idx = 0; tokens_idx < tokens.len;) {
    LexTokenSlice remaining = PG_SLICE_RANGE_START(tokens, tokens_idx);
    if (PG_SLICE_IS_EMPTY(remaining)) {
      break;
    }

    u64 tokens_consumed = 0;
    AstNode *statement =
        ast_parse_statement(remaining, errors, &tokens_consumed, allocator);

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
