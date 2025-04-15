#pragma once
#include "origin.h"
#include "submodules/cstd/lib.c"

typedef enum {
  AST_NODE_KIND_NONE,
  AST_NODE_KIND_U64,
  AST_NODE_KIND_ADD,
  AST_NODE_KIND_SYSCALL,
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
  default:
    PG_ASSERT(0);
  }
}
