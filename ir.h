#pragma once
#include "ast.h"

typedef enum : u8 {
  IR_INSTRUCTION_KIND_NONE,
  IR_INSTRUCTION_KIND_NUMBER,
  IR_INSTRUCTION_KIND_IDENTIFIER,
  IR_INSTRUCTION_KIND_ADD,
  IR_INSTRUCTION_KIND_MOV,
  IR_INSTRUCTION_KIND_LOAD_ADDRESS,
  IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
  IR_INSTRUCTION_KIND_JUMP,
  IR_INSTRUCTION_KIND_COMPARISON,
  IR_INSTRUCTION_KIND_SYSCALL,
  IR_INSTRUCTION_KIND_FN_DEFINITION,
  IR_INSTRUCTION_KIND_LABEL_DEFINITION,
  IR_INSTRUCTION_KIND_TRAP,
} IrInstructionKind;

#define IR_FLAG_GLOBAL (1 << 0)

typedef struct {
  IrInstructionKind kind;
  u16 flags;
  union {
    u64 n64;        // Number literal.
    PgString s;     // Variable name.
    u32 args_count; // Function, syscall, etc.
    Label label;
  } u;
  Origin origin;
  MetadataIndex meta_idx;
  VirtualRegister lhs, rhs;
} IrInstruction;
PG_DYN(IrInstruction) IrInstructionDyn;

typedef struct {
  u32 label_id;
} IrEmitter;

[[nodiscard]]
static IrInstruction ir_node_number(u64 n) {
  IrInstruction res = {.kind = IR_INSTRUCTION_KIND_NUMBER, .u.n64 = n};
  return res;
}

[[nodiscard]] static Label ir_make_synth_label(u32 *label_current,
                                               PgAllocator *allocator) {
  Label res = {0};
  res.value = pg_u64_to_string(++(*label_current), allocator);
  return res;
}

[[nodiscard]] static IrInstructionDyn
ir_emit_from_ast(IrEmitter *emitter, AstNodeDyn nodes, PgAllocator *allocator) {
  (void)emitter; // FIXME

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
      ins.u.s = node.u.s;
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_ADD: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_ADD;
      ins.origin = node.origin;
      PG_ASSERT(res.len >= 2);
      ins.lhs.value = (u32)res.len - 2;
      ins.rhs.value = (u32)res.len - 1;

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_COMPARISON: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_COMPARISON;
      ins.origin = node.origin;
      PG_ASSERT(res.len >= 2);
      ins.lhs.value = (u32)res.len - 2;
      ins.rhs.value = (u32)res.len - 1;

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_BLOCK: {
      PG_ASSERT(0 && "todo");
    } break;

    case AST_NODE_KIND_VAR_DEFINITION: {
      PG_ASSERT(res.len > 0);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_MOV;
      ins.origin = node.origin;
      ins.lhs.value = (u32)res.len - 1;
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_ADDRESS_OF: {
      PG_ASSERT(res.len >= 1);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_LOAD_ADDRESS;
      ins.origin = node.origin;
      ins.lhs.value = (u32)res.len - 1;
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_BRANCH: {
      PG_ASSERT(res.len >= 1);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE;
      ins.origin = node.origin;
      PG_ASSERT(0 && "todo");
    } break;

    case AST_NODE_KIND_JUMP: {
      PG_ASSERT(res.len > 0);

      AstNode op = PG_SLICE_AT(nodes, i - 1);
      PG_ASSERT(AST_NODE_KIND_LABEL == op.kind);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_JUMP;
      ins.origin = node.origin;
      ins.u.label = op.u.label;
      *PG_DYN_PUSH(&res, allocator) = ins;

    } break;

    case AST_NODE_KIND_LABEL:
      break;

    case AST_NODE_KIND_BUILTIN_TRAP: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_TRAP;
      ins.origin = node.origin;
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_FN_DEFINITION: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_FN_DEFINITION;
      ins.origin = node.origin;
      ins.u.s = node.u.s;

      if (node.flags & AST_NODE_FLAG_GLOBAL) {
        ins.flags = IR_FLAG_GLOBAL;
      }

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_SYSCALL: {
      PG_ASSERT(node.u.args_count > 0);
      PG_ASSERT(node.u.args_count <= max_syscall_args_count);

      for (u64 j = 0; j < node.u.args_count; j++) {
        u64 idx = i - node.u.args_count + j;
        AstNode op = PG_SLICE_AT(nodes, idx);
        PG_ASSERT(ast_node_is_expr(op));

        IrInstruction ins = {0};
        ins.kind = IR_INSTRUCTION_KIND_MOV;
        ins.origin = node.origin;
        ins.lhs.value = (u32)idx;
        *PG_DYN_PUSH(&res, allocator) = ins;
      }

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_SYSCALL;
      ins.origin = node.origin;

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_LABEL_DEFINITION: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION;
      ins.origin = node.origin;
      ins.u.label = ir_make_synth_label(&emitter->label_id, allocator);

      *PG_DYN_PUSH(&res, allocator) = ins;

    } break;

    case AST_NODE_KIND_BUILTIN_ASSERT:
      PG_ASSERT(0 && "todo");
      break;

    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

  return res;
}

static void ir_print_instructions(IrInstructionDyn instructions) {
  for (u32 i = 0; i < instructions.len; i++) {
    printf("[%u] ", i);
    IrInstruction ins = PG_SLICE_AT(instructions, i);

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_NUMBER:
      printf("Num %lu", ins.u.n64);
      break;
    case IR_INSTRUCTION_KIND_IDENTIFIER:
      printf("Identifier %.*s", (i32)ins.u.s.len, ins.u.s.data);
      break;
    case IR_INSTRUCTION_KIND_ADD:
      PG_ASSERT(ins.lhs.value);
      PG_ASSERT(ins.rhs.value);

      printf("Add v%u, v%u, v%u", i, ins.lhs.value, ins.rhs.value);
      break;
    case IR_INSTRUCTION_KIND_COMPARISON:
      PG_ASSERT(ins.lhs.value);
      PG_ASSERT(ins.rhs.value);

      printf("Cmp v%u, v%u, v%u", i, ins.lhs.value, ins.rhs.value);
      break;

    case IR_INSTRUCTION_KIND_MOV:
      PG_ASSERT(ins.lhs.value);
      PG_ASSERT(0 == ins.rhs.value);

      printf("Mov v%u, v%u", i, ins.lhs.value);
      break;

    case IR_INSTRUCTION_KIND_LOAD_ADDRESS:
      PG_ASSERT(ins.lhs.value);
      PG_ASSERT(0 == ins.rhs.value);

      // FIXME: Lhs should be an addr?
      printf("LoadAddr v%u, v%u", i, ins.lhs.value);
      break;

    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE:
      // PG_ASSERT(ins.res.value);
      // PG_ASSERT(ins.lhs.value);
      // PG_ASSERT(ins.rhs.value);

      printf("JumpIfFalse v%u, %u, %u", i, ins.lhs.value, ins.rhs.value);
      break;
    case IR_INSTRUCTION_KIND_JUMP:
      PG_ASSERT(ins.lhs.value);
      PG_ASSERT(ins.rhs.value);

      printf("Jump %.*s", (i32)ins.u.label.value.len, ins.u.label.value.data);
      break;
    case IR_INSTRUCTION_KIND_SYSCALL:
      printf("Syscall");
      break;
    case IR_INSTRUCTION_KIND_FN_DEFINITION:
      PG_ASSERT(0 == ins.lhs.value);
      PG_ASSERT(0 == ins.rhs.value);

      printf("FnDef %.*s", (i32)ins.u.s.len, ins.u.s.data);
      break;
    case IR_INSTRUCTION_KIND_LABEL_DEFINITION:
      PG_ASSERT(0 == ins.lhs.value);
      PG_ASSERT(0 == ins.rhs.value);
      printf("Label %.*s", (i32)ins.u.label.value.len, ins.u.label.value.data);
      break;
    case IR_INSTRUCTION_KIND_TRAP:
      PG_ASSERT(0 == ins.lhs.value);
      PG_ASSERT(0 == ins.rhs.value);
      printf("Trap");
      break;

    case IR_INSTRUCTION_KIND_NONE:
    default:
      break;
    }
    printf("\n");
  }
}
