#pragma once
#include "ast.h"

typedef enum : u8 {
  IR_INSTRUCTION_KIND_NONE,
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

typedef enum {
  IR_OPERAND_KIND_NONE,
  IR_OPERAND_KIND_NUM,
  IR_OPERAND_KIND_LABEL,
  IR_OPERAND_KIND_VREG,
} IrOperandKind;

typedef struct {
  IrOperandKind kind;

  union {
    Label label;
    VirtualRegister vreg;
    u64 u64;
  } u;
} IrOperand;

typedef struct {
  IrInstructionKind kind;
  u16 flags;
  union {
    PgString s;     // Variable name.
    u32 args_count; // Function, syscall, etc.
  } u;
  Origin origin;
  MetadataIndex meta_idx;
  IrOperand lhs, rhs;
} IrInstruction;
PG_DYN(IrInstruction) IrInstructionDyn;

typedef struct {
  u32 label_id;
} IrEmitter;

[[nodiscard]] static IrOperand ir_make_synth_label(u32 *label_current,
                                                   PgAllocator *allocator) {
  IrOperand res = {0};
  res.kind = IR_OPERAND_KIND_LABEL;
  res.u.label.value = pg_u64_to_string(++(*label_current), allocator);
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
      ins.kind = IR_INSTRUCTION_KIND_MOV;
      ins.origin = node.origin;
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_NUM,
          .u.u64 = node.u.n64,
      };
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
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 2,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_COMPARISON: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_COMPARISON;
      ins.origin = node.origin;
      PG_ASSERT(res.len >= 2);
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 2,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };

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
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_ADDRESS_OF: {
      PG_ASSERT(res.len >= 1);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_LOAD_ADDRESS;
      ins.origin = node.origin;
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };
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
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = op.u.label,
      };
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

      // TODO: Simply set constraint on existing args vregs?
      for (u64 j = 0; j < node.u.args_count; j++) {
        u64 idx = i - node.u.args_count + j;
        PG_ASSERT(idx <= UINT32_MAX);

        AstNode op = PG_SLICE_AT(nodes, idx);
        PG_ASSERT(ast_node_is_expr(op));

        IrInstruction ins = {0};
        ins.kind = IR_INSTRUCTION_KIND_MOV;
        ins.origin = node.origin;
        ins.lhs = (IrOperand){
            .kind = IR_OPERAND_KIND_VREG,
            .u.vreg.value = (u32)idx,
        };
        *PG_DYN_PUSH(&res, allocator) = ins;
      }

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_SYSCALL;
      ins.origin = node.origin;
      ins.u.args_count = node.u.args_count;

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_LABEL_DEFINITION: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION;
      ins.origin = node.origin;
      ins.lhs = ir_make_synth_label(&emitter->label_id, allocator);

      *PG_DYN_PUSH(&res, allocator) = ins;

    } break;

    case AST_NODE_KIND_BUILTIN_ASSERT: {
      PG_ASSERT(res.len >= 1);

      IrInstruction ins_cmp = {0};
      ins_cmp.kind = IR_INSTRUCTION_KIND_COMPARISON;
      ins_cmp.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_NUM,
          .u.u64 = 0,
      };
      ins_cmp.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };
      *PG_DYN_PUSH(&res, allocator) = ins_cmp;

      IrInstruction ins_jmp = {0};
      ins_jmp.kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE;
      ins_jmp.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };
      *PG_DYN_PUSH(&res, allocator) = ins_cmp;
    } break;

    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

  return res;
}

static void ir_print_operand(IrOperand operand) {
  switch (operand.kind) {
  case IR_OPERAND_KIND_NUM:
    printf("%lu", operand.u.u64);
    break;

  case IR_OPERAND_KIND_LABEL:
    PG_ASSERT(operand.u.label.value.len);
    printf("%.*s", (i32)operand.u.label.value.len, operand.u.label.value.data);
    break;

  case IR_OPERAND_KIND_VREG:
    PG_ASSERT(operand.u.vreg.value);
    printf("v%u", operand.u.vreg.value);
    break;

  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void ir_print_instructions(IrInstructionDyn instructions) {
  for (u32 i = 0; i < instructions.len; i++) {
    printf("[%u] ", i);
    IrInstruction ins = PG_SLICE_AT(instructions, i);
    origin_print(ins.origin);
    printf(": ");

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_IDENTIFIER:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Identifier %.*s", (i32)ins.u.s.len, ins.u.s.data);
      break;

    case IR_INSTRUCTION_KIND_ADD:
      printf("Add v%u, ", i);
      ir_print_operand(ins.lhs);
      printf(", ");
      ir_print_operand(ins.rhs);
      break;

    case IR_INSTRUCTION_KIND_COMPARISON:
      printf("Cmp v%u, ", i);
      ir_print_operand(ins.lhs);
      printf(", ");
      ir_print_operand(ins.rhs);
      break;

    case IR_INSTRUCTION_KIND_MOV:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Mov v%u, ", i);
      ir_print_operand(ins.lhs);
      break;

    case IR_INSTRUCTION_KIND_LOAD_ADDRESS:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("LoadAddr v%u, ", i);
      ir_print_operand(ins.lhs);
      break;

    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE:
      printf("JumpIfFalse v%u, ", i);
      ir_print_operand(ins.lhs);
      printf(", ");
      ir_print_operand(ins.rhs);
      break;

    case IR_INSTRUCTION_KIND_JUMP:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Jump ");
      ir_print_operand(ins.lhs);
      break;

    case IR_INSTRUCTION_KIND_SYSCALL:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);
      PG_ASSERT(ins.u.args_count > 0);
      PG_ASSERT(ins.u.args_count <= max_syscall_args_count);

      printf("Syscall");
      break;

    case IR_INSTRUCTION_KIND_FN_DEFINITION:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("FnDef %.*s", (i32)ins.u.s.len, ins.u.s.data);
      break;
    case IR_INSTRUCTION_KIND_LABEL_DEFINITION:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Label ");
      break;
    case IR_INSTRUCTION_KIND_TRAP:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Trap");
      break;

    case IR_INSTRUCTION_KIND_NONE:
    default:
      break;
    }
    printf("\n");
  }
}
