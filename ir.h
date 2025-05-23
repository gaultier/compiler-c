#pragma once
#include "ast.h"

typedef enum : u8 {
  IR_INSTRUCTION_KIND_NONE,
  IR_INSTRUCTION_KIND_NUMBER,
  IR_INSTRUCTION_KIND_IDENTIFIER,
  IR_INSTRUCTION_KIND_ADD,
  IR_INSTRUCTION_KIND_BLOCK,
  IR_INSTRUCTION_KIND_VAR_DEFINITION,
  IR_INSTRUCTION_KIND_ADDRESS_OF,
  IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
  IR_INSTRUCTION_KIND_JUMP,
  IR_INSTRUCTION_KIND_COMPARISON,
  IR_INSTRUCTION_KIND_BUILTIN_ASSERT,
  IR_INSTRUCTION_KIND_SYSCALL,
  IR_INSTRUCTION_KIND_FN_DEFINITION,
  IR_INSTRUCTION_KIND_LABEL_DEFINITION,
  IR_INSTRUCTION_KIND_LABEL,
  IR_INSTRUCTION_KIND_BUILTIN_TRAP,
} IrInstructionKind;

typedef struct {
  IrInstructionKind kind;
  union {
    u64 n64;             // Number literal.
    PgString identifier; // Variable name.
    u32 args_count;      // Function, syscall, etc.
    Label label;
  } u;
  Origin origin;
  MetadataIndex meta_idx;
  // TODO: Review.
  VirtualRegister res, lhs, rhs;
} IrInstruction;
PG_DYN(IrInstruction) IrInstructionDyn;

[[nodiscard]] static IrInstructionDyn ir_emit_from_ast(AstNodeDyn nodes,
                                                       PgAllocator *allocator) {
  IrInstructionDyn res = {0};
  PG_DYN_ENSURE_CAP(&res, nodes.len * 2, allocator);

  AstNodeDyn stack = {0};
  PG_DYN_ENSURE_CAP(&stack, 512, allocator);

  for (u32 i = 0; i < nodes.len; i++) {
    AstNode node = PG_SLICE_AT(nodes, i);

    switch (node.kind) {
    case AST_NODE_KIND_NUMBER: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_NUMBER;
      ins.origin = node.origin;
      ins.u.n64 = node.u.n64;
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_IDENTIFIER: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_IDENTIFIER;
      ins.origin = node.origin;
      ins.u.identifier = node.u.identifier;
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_ADD: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_ADD;
      ins.origin = node.origin;
      ins.lhs.value = i - 2;
      ins.rhs.value = i - 1;

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;
    case AST_NODE_KIND_BLOCK: {
      PG_ASSERT(0 && "todo");
    } break;
    case AST_NODE_KIND_VAR_DEFINITION: {
    } break;
    case AST_NODE_KIND_ADDRESS_OF:
    case AST_NODE_KIND_BRANCH:
    case AST_NODE_KIND_JUMP:
    case AST_NODE_KIND_COMPARISON:
    case AST_NODE_KIND_BUILTIN_ASSERT:
    case AST_NODE_KIND_SYSCALL:
    case AST_NODE_KIND_FN_DEFINITION:
    case AST_NODE_KIND_LABEL_DEFINITION:
    case AST_NODE_KIND_LABEL:
    case AST_NODE_KIND_BUILTIN_TRAP:
      break;
    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

  return res;
}
