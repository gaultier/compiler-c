#pragma once
#include "ast.h"
#include "submodules/cstd/lib.c"

typedef enum {
  IR_KIND_NONE,
  IR_KIND_ADD,
  IR_KIND_LOAD,
  IR_KIND_SYSCALL,
  IR_KIND_ADDRESS_OF,
  IR_KIND_JUMP_IF_FALSE,
  IR_KIND_JUMP,
  IR_KIND_LABEL,
} IrKind;

typedef struct {
  u32 value;
} IrVarId;

typedef struct {
  u32 value;
} IrId;

typedef struct {
  IrVarId id;
  PgString identifier;
} IrVar;

typedef enum {
  IR_VALUE_KIND_NONE,
  IR_VALUE_KIND_U64,
  IR_VALUE_KIND_VAR,
  IR_VALUE_KIND_LABEL,
} IrValueKind;

typedef struct {
  u32 value;
} IrLabelId;

typedef struct {
  IrValueKind kind;
  union {
    u64 n64;
    IrVar var;
    IrLabelId label;
  };
} IrValue;
PG_SLICE(IrValue) IrValueSlice;
PG_DYN(IrValue) IrValueDyn;

typedef struct {
  IrKind kind;
  IrValueDyn operands;
  Origin origin;
  IrId id;
  // Out var.
  IrVar var;

  bool tombstone;
} Ir;
PG_SLICE(Ir) IrSlice;
PG_DYN(Ir) IrDyn;

typedef struct {
  IrVar var;
  // Inclusive, inclusive.
  IrId start, end;
  IrVar ref; // In case of `IR_KIND_ADDRESS_OF`.

  bool tombstone;
} IrVarLifetime;
PG_SLICE(IrVarLifetime) IrVarLifetimeSlice;
PG_DYN(IrVarLifetime) IrVarLifetimeDyn;

typedef struct {
  IrDyn irs;
  IrId ir_id;
  IrLabelId label_id;
  IrVarId var_id;
  IrVarLifetimeDyn var_lifetimes;
} IrEmitter;

[[nodiscard]]
static IrId ir_emitter_next_ir_id(IrEmitter *emitter) {
  IrId id = emitter->ir_id;
  emitter->ir_id.value += 1;
  return id;
}

[[nodiscard]]
static IrLabelId ir_emitter_next_label_id(IrEmitter *emitter) {
  IrLabelId id = emitter->label_id;
  emitter->label_id.value += 1;
  return id;
}

[[nodiscard]]
static IrVarId ir_emitter_next_var_id(IrEmitter *emitter) {
  IrVarId id = emitter->var_id;
  emitter->var_id.value += 1;
  return id;
}

static IrVarLifetime *
ir_find_var_lifetime_by_var_id(IrVarLifetimeDyn var_lifetimes, IrVarId var_id) {
  if (0 == var_id.value) {
    return nullptr;
  }

  for (u64 i = 0; i < var_lifetimes.len; i++) {
    IrVarLifetime *var_lifetime = PG_SLICE_AT_PTR(&var_lifetimes, i);
    if (var_lifetime->var.id.value == var_id.value) {
      return var_lifetime;
    }
  }
  return nullptr;
}

static IrVarLifetime *
ir_find_var_lifetime_by_var_identifier(IrVarLifetimeDyn var_lifetimes,
                                       PgString identifier) {
  for (u64 i = 0; i < var_lifetimes.len; i++) {
    IrVarLifetime *var_lifetime = PG_SLICE_AT_PTR(&var_lifetimes, i);
    if (pg_string_eq(var_lifetime->var.identifier, identifier)) {
      return var_lifetime;
    }
  }
  return nullptr;
}

static void ir_var_extend_lifetime_on_var_use(IrVarLifetimeDyn var_lifetimes,
                                              IrVar var, IrId ir_id) {
  IrVarLifetime *lifetime_var =
      ir_find_var_lifetime_by_var_id(var_lifetimes, var.id);
  PG_ASSERT(lifetime_var);
  lifetime_var->end = ir_id;

  // Variable pointed to needs to live at least as long as the pointer to it.
  if (lifetime_var->ref.id.value != 0) {
    IrVarLifetime *lifetime_var_ref =
        ir_find_var_lifetime_by_var_id(var_lifetimes, lifetime_var->ref.id);
    PG_ASSERT(lifetime_var_ref);
    lifetime_var_ref->end = ir_id;
  }
}

static IrVar ast_to_ir(AstNode node, IrEmitter *emitter, ErrorDyn *errors,
                       PgAllocator *allocator) {
  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64: {
    Ir ir = {
        .kind = IR_KIND_LOAD,
        .origin = node.origin,
        .id = ir_emitter_next_ir_id(emitter),
        .var.id = ir_emitter_next_var_id(emitter),
    };
    *PG_DYN_PUSH(&ir.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_U64,
        .n64 = node.n64,
    };

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
    };
    return ir.var;
  }
  case AST_NODE_KIND_ADD: {
    // `2 + 3 + 4`:  +
    //              / \
    //             2  +
    //               / \
    //               3  4
    // =>
    // %1 = 2
    // %2 = 3 + 4
    // %3 = %2 + %1
    PG_ASSERT(2 == node.operands.len);
    IrVar lhs =
        ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors, allocator);
    IrVar rhs =
        ast_to_ir(PG_SLICE_AT(node.operands, 1), emitter, errors, allocator);

    Ir ir = {0};
    ir.kind = IR_KIND_ADD;
    ir.origin = node.origin;
    ir.id = ir_emitter_next_ir_id(emitter);
    ir.var.id = ir_emitter_next_var_id(emitter);

    PG_ASSERT(lhs.id.value < ir.id.value);
    PG_ASSERT(rhs.id.value < ir.id.value);

    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = lhs};
    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = rhs};

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
    };

    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, lhs, ir.id);
    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs, ir.id);

    return ir.var;
  }

  case AST_NODE_KIND_SYSCALL: {
    IrValueDyn operands = {0};
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      IrVar operand = ast_to_ir(child, emitter, errors, allocator);

      *PG_DYN_PUSH(&operands, allocator) =
          (IrValue){.kind = IR_VALUE_KIND_VAR, .var = operand};
    }

    Ir ir = {0};
    ir.kind = IR_KIND_SYSCALL;
    ir.origin = node.origin;
    ir.id = ir_emitter_next_ir_id(emitter);
    ir.operands = operands;
    ir.var.id = ir_emitter_next_var_id(emitter);

    for (u64 i = 0; i < node.operands.len; i++) {
      IrValue val = PG_SLICE_AT(ir.operands, i);
      PG_ASSERT(IR_VALUE_KIND_VAR == val.kind);
      IrVar var = val.var;

      ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, var, ir.id);
    }

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
    };

    return ir.var;
  }
  case AST_NODE_KIND_BLOCK: {
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      ast_to_ir(child, emitter, errors, allocator);
    }
    return (IrVar){0};
  }
  case AST_NODE_KIND_VAR_DECL: {
    PG_ASSERT(1 == node.operands.len);
    PG_ASSERT(!pg_string_is_empty(node.identifier));

    AstNode rhs_node = PG_SLICE_AT(node.operands, 0);
    IrVar rhs = ast_to_ir(rhs_node, emitter, errors, allocator);

    Ir ir = {0};
    ir.kind = IR_KIND_LOAD;
    ir.origin = node.origin;
    ir.id = ir_emitter_next_ir_id(emitter);
    ir.var.id = ir_emitter_next_var_id(emitter);
    ir.var.identifier = node.identifier;

    *PG_DYN_PUSH(&ir.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_VAR,
        .var = rhs,
    };
    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs, ir.id);

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
    };

    return ir.var;
  }

  case AST_NODE_KIND_IDENTIFIER: {
    IrVarLifetime *lifetime = ir_find_var_lifetime_by_var_identifier(
        emitter->var_lifetimes, node.identifier);

    if (!lifetime) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_UNDEFINED_VAR,
          .origin = node.origin,
      };
      return (IrVar){0};
    }

    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, lifetime->var,
                                      emitter->ir_id);

    return lifetime->var;
  }

  case AST_NODE_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == node.operands.len);
    AstNode operand = PG_SLICE_AT(node.operands, 0);
    PG_ASSERT(AST_NODE_KIND_IDENTIFIER == operand.kind);

    IrVar rhs = ast_to_ir(operand, emitter, errors, allocator);
    Ir ir = {0};
    ir.kind = IR_KIND_ADDRESS_OF;
    ir.origin = node.origin;
    ir.id = ir_emitter_next_ir_id(emitter);
    ir.var.id = ir_emitter_next_var_id(emitter);

    PG_ASSERT(rhs.id.value < ir.id.value);

    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = rhs};

    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs, ir.id);

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
        .ref = rhs,
    };

    return ir.var;
  }

  case AST_NODE_KIND_IF: {
    PG_ASSERT(2 == node.operands.len);
    IrVar cond =
        ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors, allocator);
    // TODO: else.

    Ir ir_cond_jump = {
        .kind = IR_KIND_JUMP_IF_FALSE,
        .origin = node.origin,
        .id = ir_emitter_next_ir_id(emitter),
    };
    PG_ASSERT(cond.id.value < ir_cond_jump.id.value);
    *PG_DYN_PUSH(&ir_cond_jump.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_VAR,
        .var = cond,
    };
    *PG_DYN_PUSH(&emitter->irs, allocator) = ir_cond_jump;

    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, cond,
                                      ir_cond_jump.id);

    u64 ir_cond_jump_idx = emitter->irs.len - 1;

    IrLabelId branch_if_cont_label = ir_emitter_next_label_id(emitter);
    IrLabelId branch_else_label = ir_emitter_next_label_id(emitter);

    // 'then' branch.
    {
      ast_to_ir(PG_SLICE_AT(node.operands, 1), emitter, errors, allocator);
      Ir ir_jump = {
          .kind = IR_KIND_JUMP,
          .id = ir_emitter_next_ir_id(emitter),
      };
      *PG_DYN_PUSH(&ir_jump.operands, allocator) = (IrValue){
          .kind = IR_VALUE_KIND_LABEL,
          .label = branch_if_cont_label,
      };
      *PG_DYN_PUSH(&emitter->irs, allocator) = ir_jump;
    }

    // 'else' branch.
    {
      Ir ir_label_else = {
          .kind = IR_KIND_LABEL,
          .id = ir_emitter_next_ir_id(emitter),
      };
      *PG_DYN_PUSH(&ir_label_else.operands, allocator) = (IrValue){
          .kind = IR_VALUE_KIND_LABEL,
          .label = branch_else_label,
      };
      *PG_DYN_PUSH(&emitter->irs, allocator) = ir_label_else;
      if (3 == node.operands.len) {
        ast_to_ir(PG_SLICE_AT(node.operands, 2), emitter, errors, allocator);
      }
    }
    Ir ir_label_if_cont = {
        .kind = IR_KIND_LABEL,
        .id = ir_emitter_next_ir_id(emitter),
    };
    *PG_DYN_PUSH(&ir_label_if_cont.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_LABEL,
        .label = branch_if_cont_label,
    };
    *PG_DYN_PUSH(&emitter->irs, allocator) = ir_label_if_cont;

    Ir *ir_cond_jump_backpatch =
        PG_SLICE_AT_PTR(&emitter->irs, ir_cond_jump_idx);
    *PG_DYN_PUSH(&ir_cond_jump_backpatch->operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_LABEL,
        .label = branch_else_label,
    };

    return (IrVar){0};
  }

  default:
    PG_ASSERT(0);
  }
}

static void irs_simplify_remove_unused_vars(IrDyn *irs,
                                            IrVarLifetimeDyn *var_lifetimes) {
  for (u64 i = 0; i < irs->len; i++) {
    Ir *ir = PG_SLICE_AT_PTR(irs, i);
    if (ir->tombstone) {
      continue;
    }

    // Some IRs do not result in a variable.
    if (0 == ir->var.id.value) {
      continue;
    }

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var_id(*var_lifetimes, ir->var.id);
    PG_ASSERT(var_lifetime);
    PG_ASSERT(!var_lifetime->tombstone);

    PG_ASSERT(var_lifetime->start.value <= var_lifetime->end.value);
    u64 duration = var_lifetime->end.value - var_lifetime->start.value;
    if (duration > 0) {
      // Used: no-op.
      continue;
    }

    var_lifetime->tombstone = true;

    // Possible side-effects: keep this IR but erase the variable.
    if (IR_KIND_SYSCALL == ir->kind) {
      ir->var.id.value = 0;
      continue;
    }

    ir->tombstone = true;
  }
}

// Simplify: `x1 := 1; x2 := x1; x3 := x2 + x2` => `x1 := 1; x3 := x1 + x1`.
static void irs_simplify_remove_trivial_vars(IrDyn *irs,
                                             IrVarLifetimeDyn *var_lifetimes) {
  for (u64 i = 0; i < irs->len; i++) {
    Ir *ir = PG_SLICE_AT_PTR(irs, i);
    if (ir->tombstone) {
      continue;
    }

    if (0 == ir->var.id.value) {
      continue;
    }

    if (1 != ir->operands.len) {
      continue;
    }

    // TODO: Are there other IR kinds candidate to this simplification?
    if (!(IR_KIND_LOAD == ir->kind)) {
      continue;
    }

    IrValue rhs = PG_SLICE_AT(ir->operands, 0);

    // TODO: We could also simplify `x1 := 1; x2 := 2; x3 := x2 + x1` => `x2 :=
    // 2; x3 := x2 + 1`.
    if (!(IR_VALUE_KIND_VAR == rhs.kind)) {
      continue;
    }

    IrVar rhs_var = rhs.var;
    IrVar var_to_rm = ir->var;

    for (u64 j = i + 1; j < irs->len; j++) {
      Ir ir_to_fix = PG_SLICE_AT(*irs, j);
      if (ir_to_fix.tombstone) {
        continue;
      }

      for (u64 k = 0; k < ir_to_fix.operands.len; k++) {
        IrValue *op = PG_SLICE_AT_PTR(&ir_to_fix.operands, k);

        if (IR_VALUE_KIND_VAR == op->kind &&
            op->var.id.value == var_to_rm.id.value) {
          op->var = rhs_var;
        }
      }
    }
    ir->tombstone = true;
    IrVarLifetime *lifetime =
        ir_find_var_lifetime_by_var_id(*var_lifetimes, ir->var.id);
    PG_ASSERT(!lifetime->tombstone);
    lifetime->tombstone = true;
  }
}

static void
irs_simplify_add_rhs_when_immediate(IrDyn *irs,
                                    IrVarLifetimeDyn *var_lifetimes) {
  for (u64 i = 0; i < irs->len; i++) {
    Ir *ir = PG_SLICE_AT_PTR(irs, i);
    if (ir->tombstone) {
      continue;
    }

    if (!(IR_KIND_ADD == ir->kind)) {
      continue;
    }

    PG_ASSERT(2 == ir->operands.len);

    IrValue *rhs = PG_SLICE_AT_PTR(&ir->operands, 1);

    if (!(IR_VALUE_KIND_VAR == rhs->kind)) {
      continue;
    }

    IrVar rhs_var = rhs->var;
    PG_ASSERT(rhs_var.id.value != 0);

    Ir *rhs_ir = nullptr;
    for (u64 j = 0; j < irs->len; j++) {
      Ir *it = PG_SLICE_AT_PTR(irs, j);
      if (it->var.id.value == rhs_var.id.value) {
        rhs_ir = it;
        break;
      }
    }
    PG_ASSERT(rhs_ir);

    if (!(IR_KIND_LOAD == rhs_ir->kind)) {
      continue;
    }

    PG_ASSERT(1 == rhs_ir->operands.len);

    IrValue rhs_ir_op0 = PG_SLICE_AT(rhs_ir->operands, 0);
    if (!(IR_VALUE_KIND_U64 == rhs_ir_op0.kind)) {
      continue;
    }

    *rhs = rhs_ir_op0;
    rhs_ir->tombstone = true;

    PG_ASSERT(rhs_var.id.value == rhs_ir->var.id.value);

    IrVarLifetime *lifetime =
        ir_find_var_lifetime_by_var_id(*var_lifetimes, rhs_ir->var.id);
    PG_ASSERT(!lifetime->tombstone);
    lifetime->tombstone = true;
  }
}

static void irs_simplify(IrDyn *irs, IrVarLifetimeDyn *var_lifetimes) {
  // TODO: Loop until a fixed point (or a limit) is reached.
  // TODO: Recompute var lifetimes after each step?

  irs_simplify_remove_unused_vars(irs, var_lifetimes);
  irs_simplify_remove_trivial_vars(irs, var_lifetimes);
  irs_simplify_add_rhs_when_immediate(irs, var_lifetimes);
  // TODO: Unify constants e.g. `x1 := 1; x2 := 1` => `x1 := 1`.
  // TODO: Constant folding e.g. `x1 := 1; x2 := 2; x3 := x1 + x2` => `x3 := 3`.
  // TODO: Simplify `if(true) { <then> } else { <else> }` => `<then>`
  // TODO: Remove empty labels.
}

static void ir_print_var(IrVar var) {
  if (0 == var.id.value) {
    return;
  }

  if (!pg_string_is_empty(var.identifier)) {
    printf("%.*s%%%" PRIu32, (i32)var.identifier.len, var.identifier.data,
           var.id.value);
  } else {
    printf("%%%" PRIu32, var.id.value);
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
    ir_print_var(value.var);
    break;
  case IR_VALUE_KIND_LABEL:
    printf(".%" PRIu32 "", value.label.value);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void ir_emitter_print_ir(IrEmitter emitter, u32 i) {
  Ir ir = PG_SLICE_AT(emitter.irs, i);

  if (ir.tombstone) {
    printf("\x1B[9m"); // Strikethrough.
  }

  origin_print(ir.origin);
  printf(": [%u] [%u] ", i, ir.id.value);

  switch (ir.kind) {
  case IR_KIND_NONE:
    PG_ASSERT(0);
  case IR_KIND_ADD: {
    PG_ASSERT(2 == ir.operands.len);
    PG_ASSERT(0 != ir.var.id.value);

    ir_print_var(ir.var);
    printf(" := ");
    ir_print_value(PG_SLICE_AT(ir.operands, 0));
    printf(" + ");
    ir_print_value(PG_SLICE_AT(ir.operands, 1));

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var_id(emitter.var_lifetimes, ir.var.id);
    PG_ASSERT(var_lifetime);
    printf(" // lifetime: [%u:%u]\n", var_lifetime->start.value,
           var_lifetime->end.value);
  } break;
  case IR_KIND_LOAD: {
    PG_ASSERT(1 == ir.operands.len);
    PG_ASSERT(0 != ir.var.id.value);

    IrValue rhs = PG_SLICE_AT(ir.operands, 0);
    ir_print_var(ir.var);
    printf(" := ");
    ir_print_value(rhs);

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var_id(emitter.var_lifetimes, ir.var.id);
    PG_ASSERT(var_lifetime);
    printf(" // lifetime: [%u:%u]\n", var_lifetime->start.value,
           var_lifetime->end.value);
  } break;
  case IR_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir.operands.len);
    PG_ASSERT(0 != ir.var.id.value);

    ir_print_var(ir.var);
    printf(" := &");
    ir_print_value(PG_SLICE_AT(ir.operands, 0));

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var_id(emitter.var_lifetimes, ir.var.id);
    PG_ASSERT(var_lifetime);
    printf(" // lifetime: [%u:%u]\n", var_lifetime->start.value,
           var_lifetime->end.value);
  } break;
  case IR_KIND_SYSCALL: {
    ir_print_var(ir.var);
    printf("%ssyscall(", 0 == ir.var.id.value ? "" : " := ");

    for (u64 j = 0; j < ir.operands.len; j++) {
      IrValue val = PG_SLICE_AT(ir.operands, j);
      ir_print_value(val);

      if (j + 1 < ir.operands.len) {
        printf(", ");
      }
    }

    printf(")");

    if (0 != ir.var.id.value) {
      IrVarLifetime *var_lifetime =
          ir_find_var_lifetime_by_var_id(emitter.var_lifetimes, ir.var.id);
      PG_ASSERT(var_lifetime);
      printf("// lifetime: [%u:%u]", var_lifetime->start.value,
             var_lifetime->end.value);
    }
    printf("\n");
  } break;
  case IR_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ir.operands.len);
    PG_ASSERT(0 == ir.var.id.value);

    IrValue cond = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == cond.kind);

    IrValue branch_else = PG_SLICE_AT(ir.operands, 1);

    printf("jump_if_false(");
    ir_print_value(cond);
    printf(", ");
    ir_print_value(branch_else);
    printf(")\n");
  } break;
  case IR_KIND_JUMP: {
    PG_ASSERT(1 == ir.operands.len);
    PG_ASSERT(0 == ir.var.id.value);

    IrValue label = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_LABEL == label.kind);
    printf("jump .%u\n", label.label.value);
  } break;

  case IR_KIND_LABEL: {
    PG_ASSERT(1 == ir.operands.len);
    PG_ASSERT(0 == ir.var.id.value);

    IrValue label = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_LABEL == label.kind);

    printf(".%u:\n", label.label.value);
  } break;
  default:
    PG_ASSERT(0);
  }
  if (ir.tombstone) {
    printf("\x1B[0m"); // Reset.
  }
}

static void ir_emitter_print_irs(IrEmitter emitter) {
  for (u64 i = 0; i < emitter.irs.len; i++) {
    ir_emitter_print_ir(emitter, (u32)i);
  }
}

static void ir_emitter_print_var_lifetimes(IrEmitter emitter) {
  for (u64 i = 0; i < emitter.var_lifetimes.len; i++) {
    IrVarLifetime var_lifetime = PG_SLICE_AT(emitter.var_lifetimes, i);
    if (var_lifetime.tombstone) {
      printf("\x1B[9m"); // Strikethrough.
    }

    printf("[%lu] ", i);
    ir_print_var(var_lifetime.var);
    printf(" lifetime: [%u:%u]\n", var_lifetime.start.value,
           var_lifetime.end.value);

    if (var_lifetime.tombstone) {
      printf("\x1B[0m"); // Strikethrough.
    }
  }
}
