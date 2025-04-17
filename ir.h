#pragma once
#include "ast.h"
#include "submodules/cstd/lib.c"

typedef enum {
  IR_KIND_NONE,
  IR_KIND_ADD,
  IR_KIND_LOAD,
  IR_KIND_SYSCALL,
  IR_KIND_ADDRESS_OF,
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
  u32 num;
} Ir;
PG_SLICE(Ir) IrSlice;
PG_DYN(Ir) IrDyn;

typedef struct {
  PgString identifier;
  IrVar var;
} IrIdentifierToVar;
PG_DYN(IrIdentifierToVar) IrIdentifierToVarDyn;

static void ir_add_identifier_to_var(IrIdentifierToVarDyn *identifier_to_vars,
                                     PgString identifier, IrVar var,
                                     PgAllocator *allocator) {
  // TODO: Detect variable shadowing i.e. entry already present for this
  // identifier?

  *PG_DYN_PUSH(identifier_to_vars, allocator) = (IrIdentifierToVar){
      .identifier = identifier,
      .var = var,
  };
}

static IrIdentifierToVar *
ir_find_identifier_to_var_by_identifier(IrIdentifierToVarDyn identifier_to_vars,
                                        PgString identifier) {
  IrIdentifierToVar *res = nullptr;

  for (u64 i = 0; i < identifier_to_vars.len; i++) {
    IrIdentifierToVar *elem = PG_SLICE_AT_PTR(&identifier_to_vars, i);
    if (pg_string_eq(elem->identifier, identifier)) {
      res = elem;
      break;
    }
  }

  return res;
}

static IrVar ast_to_ir(AstNode node, IrDyn *irs, u32 *ir_num,
                       IrIdentifierToVarDyn *identifier_to_vars,
                       ErrorDyn *errors, PgAllocator *allocator) {
  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64: {
    Ir ir = {
        .kind = IR_KIND_LOAD,
        .origin = node.origin,
        .num = (*ir_num)++,
    };
    *PG_DYN_PUSH(&ir.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_U64,
        .n64 = node.n64,
    };

    *PG_DYN_PUSH(irs, allocator) = ir;
    return (IrVar){ir.num};
  }
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
    IrVar lhs = ast_to_ir(PG_SLICE_AT(node.operands, 0), irs, ir_num,
                          identifier_to_vars, errors, allocator);
    IrVar rhs = ast_to_ir(PG_SLICE_AT(node.operands, 1), irs, ir_num,
                          identifier_to_vars, errors, allocator);

    Ir ir = {
        .kind = IR_KIND_ADD,
        .origin = node.origin,
        .num = (*ir_num)++,
    };
    PG_ASSERT(lhs.value < ir.num);
    PG_ASSERT(rhs.value < ir.num);

    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = lhs};
    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = rhs};

    *PG_DYN_PUSH(irs, allocator) = ir;
    return (IrVar){ir.num};
  }

  case AST_NODE_KIND_SYSCALL: {
    IrValueDyn operands = {0};
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      IrVar operand =
          ast_to_ir(child, irs, ir_num, identifier_to_vars, errors, allocator);

      *PG_DYN_PUSH(&operands, allocator) =
          (IrValue){.kind = IR_VALUE_KIND_VAR, .var = operand};
    }

    Ir ir = {
        .kind = IR_KIND_SYSCALL,
        .origin = node.origin,
        .num = (*ir_num)++,
        .operands = operands,
    };
    for (u64 i = 0; i < node.operands.len; i++) {
      PG_ASSERT(IR_VALUE_KIND_VAR == PG_SLICE_AT(ir.operands, i).kind);
      PG_ASSERT(PG_SLICE_AT(ir.operands, i).var.value < ir.num);
    }

    *PG_DYN_PUSH(irs, allocator) = ir;
    return (IrVar){ir.num};
  }
  case AST_NODE_KIND_BLOCK: {
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      ast_to_ir(child, irs, ir_num, identifier_to_vars, errors, allocator);
    }
    return (IrVar){0}; // TODO: Should a block return a value?
  }
  case AST_NODE_KIND_VAR_DECL: {
    PG_ASSERT(1 == node.operands.len);
    PG_ASSERT(!pg_string_is_empty(node.identifier));

    IrVar rhs = ast_to_ir(PG_SLICE_AT(node.operands, 0), irs, ir_num,
                          identifier_to_vars, errors, allocator);
    Ir ir = {
        .kind = IR_KIND_LOAD,
        .origin = node.origin,
        .num = (*ir_num)++,
    };
    PG_ASSERT(rhs.value < ir.num);

    *PG_DYN_PUSH(&ir.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_VAR,
        .var = rhs,
    };

    *PG_DYN_PUSH(irs, allocator) = ir;

    ir_add_identifier_to_var(identifier_to_vars, node.identifier, rhs,
                             allocator);
    return (IrVar){ir.num};
  }

  case AST_NODE_KIND_IDENTIFIER: {
    IrIdentifierToVar *identifier_to_var =
        ir_find_identifier_to_var_by_identifier(*identifier_to_vars,
                                                node.identifier);

    if (!identifier_to_var) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_UNDEFINED_VAR,
          .origin = node.origin,
      };
      return (IrVar){0};
    }
    return identifier_to_var->var;
  }

  case AST_NODE_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == node.operands.len);
    AstNode operand = PG_SLICE_AT(node.operands, 0);
    PG_ASSERT(AST_NODE_KIND_IDENTIFIER == operand.kind);

    IrVar rhs =
        ast_to_ir(operand, irs, ir_num, identifier_to_vars, errors, allocator);
    Ir ir = {
        .kind = IR_KIND_ADDRESS_OF,
        .origin = node.origin,
        .num = (*ir_num)++,
    };
    PG_ASSERT(rhs.value < ir.num);

    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = rhs};
    *PG_DYN_PUSH(irs, allocator) = ir;
    return (IrVar){ir.num};
  }

  default:
    PG_ASSERT(0);
  }
}

// TODO: Constant folding.
static void irs_simplify(IrDyn *irs) {
  for (u64 i = 0; i < irs->len;) {
    Ir ir = PG_SLICE_AT(*irs, i);

    // `x1 := x0`: Remove.
    if (IR_KIND_LOAD == ir.kind && 1 == ir.operands.len &&
        IR_VALUE_KIND_VAR == PG_SLICE_AT(ir.operands, 0).kind) {
      PG_DYN_REMOVE_AT(irs, i);
      u32 ir_num_to_remove = ir.num;

      for (u64 j = i + 1; j < irs->len; j++) {
        Ir ir_to_fix = PG_SLICE_AT(*irs, j);

        for (u64 k = 0; k < ir_to_fix.operands.len; k++) {
          IrValue *operand = PG_SLICE_AT_PTR(&ir_to_fix.operands, k);
          if (IR_VALUE_KIND_VAR == operand->kind &&
              operand->var.value == ir_num_to_remove) {
            operand->var.value = PG_SLICE_AT(ir.operands, 0).var.value;
          }
        }
      }

      continue;
    }

    i += 1;
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
    printf("[%u] x%u := ", i, ir.num);
    ir_print_value(PG_SLICE_AT(ir.operands, 0));
    printf(" + ");
    ir_print_value(PG_SLICE_AT(ir.operands, 1));
    printf("\n");
    break;
  case IR_KIND_LOAD:
    PG_ASSERT(1 == ir.operands.len);
    printf("[%u] x%u := ", i, ir.num);
    ir_print_value(PG_SLICE_AT(ir.operands, 0));
    printf("\n");
    break;
  case IR_KIND_ADDRESS_OF:
    PG_ASSERT(1 == ir.operands.len);
    printf("[%u] x%u := &", i, ir.num);
    ir_print_value(PG_SLICE_AT(ir.operands, 0));
    printf("\n");
    break;
  case IR_KIND_SYSCALL: {
    printf("[%u] x%u := syscall(", i, ir.num);
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
