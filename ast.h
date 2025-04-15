#pragma once
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
};
