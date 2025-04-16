#pragma once
#include "ast.h"
#include "submodules/cstd/lib.c"

typedef enum {
  IR_KIND_NONE,
  IR_KIND_ADD,
  IR_KIND_LOAD,
  IR_KIND_SYSCALL,
} IrKind;

typedef struct {
  u32 value;
} IrVar;

typedef enum {
  IR_VALUE_KIND_NONE,
  IR_VALUE_KIND_U64,
  IR_VALUE_KIND_VAR,
} IrValueKind;

typedef struct {
  IrValueKind kind;
  union {
    u64 n64;
    IrVar var;
  };
} IrValue;
PG_SLICE(IrValue) IrValueSlice;
PG_DYN(IrValue) IrValueDyn;

typedef struct {
  IrKind kind;
  IrValueDyn operands;
  Origin origin;
} Ir;
PG_SLICE(Ir) IrSlice;
PG_DYN(Ir) IrDyn;

static void ast_to_ir(AstNode node, IrDyn *irs, PgAllocator *allocator) {
  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64: {
    Ir ir = {
        .kind = IR_KIND_LOAD,
        .origin = node.origin,
    };
    *PG_DYN_PUSH(&ir.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_U64,
        .n64 = node.n64,
    };

    *PG_DYN_PUSH(irs, allocator) = ir;
  } break;
  case AST_NODE_KIND_ADD: {
    // `2 + 3 + 4`:  +
    //              / \
    //             2  +
    //               / \
    //               3  4
    // =>
    // x1 = 2
    // x2 = 3 + 4
    // x3 = x2 + x1
    PG_ASSERT(2 == node.operands.len);
    ast_to_ir(PG_SLICE_AT(node.operands, 0), irs, allocator);
    IrVar lhs = (IrVar){(u32)irs->len - 1};
    ast_to_ir(PG_SLICE_AT(node.operands, 1), irs, allocator);
    IrVar rhs = (IrVar){(u32)irs->len - 1};

    Ir ir = {
        .kind = IR_KIND_ADD,
        .origin = node.origin,
    };
    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = lhs};
    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = rhs};

    *PG_DYN_PUSH(irs, allocator) = ir;
  } break;

  case AST_NODE_KIND_SYSCALL: {
    Ir ir = {
        .kind = IR_KIND_SYSCALL,
        .origin = node.origin,
    };

    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      ast_to_ir(child, irs, allocator);
      IrVar operand = (IrVar){(u32)irs->len - 1};
      *PG_DYN_PUSH(&ir.operands, allocator) =
          (IrValue){.kind = IR_VALUE_KIND_VAR, .var = operand};
    }

    *PG_DYN_PUSH(irs, allocator) = ir;
  } break;
  case AST_NODE_KIND_BLOCK: {
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      ast_to_ir(child, irs, allocator);
    }
  } break;

  default:
    PG_ASSERT(0);
  }
}

static void ir_print_value(IrValue value) {
  switch (value.kind) {
  case IR_VALUE_KIND_NONE:
    PG_ASSERT(0);
  case IR_VALUE_KIND_U64:
    printf("%" PRIu64, value.n64);
    break;
  case IR_VALUE_KIND_VAR:
    printf("x%" PRIu32, value.var.value);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void ir_print(IrSlice irs, u32 i) {
  Ir ir = PG_SLICE_AT(irs, i);
  origin_print(ir.origin);
  printf(": ");

  switch (ir.kind) {
  case IR_KIND_NONE:
    PG_ASSERT(0);
  case IR_KIND_ADD:
    PG_ASSERT(2 == ir.operands.len);
    printf("%u: x%u := ", i, i);
    ir_print_value(PG_SLICE_AT(ir.operands, 0));
    printf(" + ");
    ir_print_value(PG_SLICE_AT(ir.operands, 1));
    printf("\n");
    break;
  case IR_KIND_LOAD:
    PG_ASSERT(1 == ir.operands.len);
    printf("%u: x%u := ", i, i);
    ir_print_value(PG_SLICE_AT(ir.operands, 0));
    printf("\n");
    break;
  case IR_KIND_SYSCALL: {
    printf("%u: x%u := syscall(", i, i);
    for (u64 j = 0; j < ir.operands.len; j++) {
      IrValue val = PG_SLICE_AT(ir.operands, j);
      ir_print_value(val);

      if (j + 1 < ir.operands.len) {
        printf(", ");
      }
    }
    printf(")\n");
  } break;
  default:
    PG_ASSERT(0);
  }
}

static void irs_print(IrSlice irs) {
  for (u64 i = 0; i < irs.len; i++) {
    ir_print(irs, (u32)i);
  }
}
