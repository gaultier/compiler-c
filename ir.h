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
    ir_var_extend_lifetime_on_var_use(var_lifetimes, lifetime_var->ref, ir_id);
    // FIXME: If there are multiple aliases to the same pointer, all aliases
    // should have their lifetime extended to this point!
  }
}

static IrValue ast_to_ir(AstNode node, IrEmitter *emitter, ErrorDyn *errors,
                         bool is_immediate_ok, PgAllocator *allocator) {
  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64: {
    if (is_immediate_ok) {
      return (IrValue){.kind = IR_VALUE_KIND_U64, .n64 = node.n64};
    }
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
    return (IrValue){.kind = IR_VALUE_KIND_VAR, .var = ir.var};
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
    IrValue lhs = ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors,
                            true, allocator);
    IrValue rhs = ast_to_ir(PG_SLICE_AT(node.operands, 1), emitter, errors,
                            true, allocator);

    Ir ir = {0};
    ir.kind = IR_KIND_ADD;
    ir.origin = node.origin;
    ir.id = ir_emitter_next_ir_id(emitter);
    ir.var.id = ir_emitter_next_var_id(emitter);

    *PG_DYN_PUSH(&ir.operands, allocator) = lhs;
    *PG_DYN_PUSH(&ir.operands, allocator) = rhs;

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
    };

    if (IR_VALUE_KIND_VAR == lhs.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, lhs.var, ir.id);
    }
    if (IR_VALUE_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs.var, ir.id);
    }

    return (IrValue){.kind = IR_VALUE_KIND_VAR, .var = ir.var};
  }

  case AST_NODE_KIND_SYSCALL: {
    IrValueDyn operands = {0};
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      IrValue operand = ast_to_ir(child, emitter, errors, true, allocator);

      *PG_DYN_PUSH(&operands, allocator) = operand;
    }

    Ir ir = {0};
    ir.kind = IR_KIND_SYSCALL;
    ir.origin = node.origin;
    ir.id = ir_emitter_next_ir_id(emitter);
    ir.operands = operands;
    ir.var.id = ir_emitter_next_var_id(emitter);

    for (u64 i = 0; i < node.operands.len; i++) {
      IrValue val = PG_SLICE_AT(ir.operands, i);
      if (IR_VALUE_KIND_VAR == val.kind) {
        IrVar var = val.var;
        ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, var, ir.id);
      }
    }

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
    };

    return (IrValue){.kind = IR_VALUE_KIND_VAR, .var = ir.var};
  }
  case AST_NODE_KIND_BLOCK: {
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      ast_to_ir(child, emitter, errors, false, allocator);
    }
    // TODO: Label?
    return (IrValue){0};
  }
  case AST_NODE_KIND_VAR_DECL: {
    PG_ASSERT(1 == node.operands.len);
    PG_ASSERT(!pg_string_is_empty(node.identifier));

    AstNode rhs_node = PG_SLICE_AT(node.operands, 0);
    IrValue rhs = ast_to_ir(rhs_node, emitter, errors, true, allocator);

    Ir ir = {0};
    ir.kind = IR_KIND_LOAD;
    ir.origin = node.origin;
    ir.id = ir_emitter_next_ir_id(emitter);
    ir.var.id = ir_emitter_next_var_id(emitter);
    ir.var.identifier = node.identifier;

    *PG_DYN_PUSH(&ir.operands, allocator) = rhs;
    IrVarLifetime *rhs_lifetime = nullptr;
    if (IR_VALUE_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs.var, ir.id);
      rhs_lifetime =
          ir_find_var_lifetime_by_var_id(emitter->var_lifetimes, rhs.var.id);
      PG_ASSERT(rhs_lifetime);
    }

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    IrVarLifetime lifetime = {
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
        .ref = rhs_lifetime ? rhs_lifetime->var : (IrVar){0},
    };
    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = lifetime;

    return (IrValue){.kind = IR_VALUE_KIND_VAR, .var = ir.var};
  }

  case AST_NODE_KIND_IDENTIFIER: {
    IrVarLifetime *lifetime = ir_find_var_lifetime_by_var_identifier(
        emitter->var_lifetimes, node.identifier);

    if (!lifetime) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_UNDEFINED_VAR,
          .origin = node.origin,
      };
      return (IrValue){0};
    }

    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, lifetime->var,
                                      emitter->ir_id);

    return (IrValue){
        .kind = IR_VALUE_KIND_VAR,
        .var = lifetime->var,
    };
  }

  case AST_NODE_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == node.operands.len);
    AstNode operand = PG_SLICE_AT(node.operands, 0);
    PG_ASSERT(AST_NODE_KIND_IDENTIFIER == operand.kind);

    IrValue rhs = ast_to_ir(operand, emitter, errors, false, allocator);
    Ir ir = {0};
    ir.kind = IR_KIND_ADDRESS_OF;
    ir.origin = node.origin;
    ir.id = ir_emitter_next_ir_id(emitter);
    ir.var.id = ir_emitter_next_var_id(emitter);

    *PG_DYN_PUSH(&ir.operands, allocator) = rhs;

    if (IR_VALUE_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs.var, ir.id);
    } else {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER,
          .origin = node.origin,
      };
      return (IrValue){0};
    }

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir.var,
        .start = ir.id,
        .end = ir.id,
        .ref = rhs.var,
    };

    return (IrValue){.kind = IR_VALUE_KIND_VAR, .var = ir.var};
  }

  case AST_NODE_KIND_IF: {
    PG_ASSERT(2 == node.operands.len);
    IrValue cond = ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors,
                             false, allocator);
    // TODO: else.

    Ir ir_cond_jump = {
        .kind = IR_KIND_JUMP_IF_FALSE,
        .origin = node.origin,
        .id = ir_emitter_next_ir_id(emitter),
    };
    *PG_DYN_PUSH(&ir_cond_jump.operands, allocator) = cond;
    *PG_DYN_PUSH(&emitter->irs, allocator) = ir_cond_jump;

    if (IR_VALUE_KIND_VAR == cond.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, cond.var,
                                        ir_cond_jump.id);
    }

    u64 ir_cond_jump_idx = emitter->irs.len - 1;

    IrLabelId branch_if_cont_label = ir_emitter_next_label_id(emitter);
    IrLabelId branch_else_label = ir_emitter_next_label_id(emitter);

    // 'then' branch.
    {
      ast_to_ir(PG_SLICE_AT(node.operands, 1), emitter, errors, false,
                allocator);
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
        ast_to_ir(PG_SLICE_AT(node.operands, 2), emitter, errors, false,
                  allocator);
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

    return (IrValue){0};
  }

  default:
    PG_ASSERT(0);
  }
}

static void irs_recompute_var_lifetimes(IrDyn irs, IrVarLifetimeDyn lifetimes) {
  for (u64 i = 0; i < lifetimes.len; i++) {
    IrVarLifetime *lifetime = PG_SLICE_AT_PTR(&lifetimes, i);
    lifetime->tombstone = true;
    lifetime->end = lifetime->start;
  }

  for (u64 i = 0; i < irs.len; i++) {
    Ir ir = PG_SLICE_AT(irs, i);
    if (ir.tombstone) {
      continue;
    }

    switch (ir.kind) {
    case IR_KIND_ADD:
    case IR_KIND_LOAD:
    case IR_KIND_SYSCALL:
    case IR_KIND_ADDRESS_OF:
    case IR_KIND_JUMP_IF_FALSE: {
      for (u64 j = 0; j < ir.operands.len; j++) {
        IrValue val = PG_SLICE_AT(ir.operands, j);
        if (IR_VALUE_KIND_VAR != val.kind) {
          continue;
        }

        IrVarLifetime *lifetime =
            ir_find_var_lifetime_by_var_id(lifetimes, val.var.id);
        PG_ASSERT(lifetime);
        lifetime->end = ir.id;
        lifetime->tombstone = false;
      }
    } break;
    case IR_KIND_JUMP:
    case IR_KIND_LABEL:
      break;
    case IR_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }
}

[[nodiscard]]
static bool irs_optimize_remove_unused_vars(IrDyn *irs,
                                            IrVarLifetimeDyn *var_lifetimes) {
  bool changed = false;

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
    if (var_lifetime->tombstone) {
      goto do_rm;
    }

    PG_ASSERT(var_lifetime->start.value <= var_lifetime->end.value);
    u64 duration = var_lifetime->end.value - var_lifetime->start.value;
    if (duration > 0) {
      // Used: no-op.
      continue;
    }

  do_rm:

    var_lifetime->tombstone = true;

    // Possible side-effects: keep this IR but erase the variable.
    if (IR_KIND_SYSCALL == ir->kind) {
      ir->var.id.value = 0;
      continue;
    }

    ir->tombstone = true;
    changed = true;
  }
  return changed;
}

// Simplify: `x1 := 1; x2 := x1` => `x2 := 1`
// and update subsequent IRs referencing the old var to use the new var.
[[nodiscard]]
static bool
irs_optimize_remove_trivially_aliased_vars(IrDyn *irs,
                                           IrVarLifetimeDyn *var_lifetimes) {
  bool changed = false;

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
    changed = true;
  }
  return changed;
}

[[nodiscard]] static Ir *irs_find_ir_by_id(IrDyn irs, IrId ir_id) {
  for (u64 i = 0; i < irs.len; i++) {
    Ir *ir = PG_SLICE_AT_PTR(&irs, i);
    if (ir->id.value == ir_id.value) {
      return ir;
    }
  }
  return nullptr;
}

// Replace: `x1 := 1; x2 := 2; x3:= x2 + x1` => `x2 := 2; x3 := x2 + 1`.
[[nodiscard]]
static bool irs_optimize_replace_immediate_vars_by_immediate(
    IrDyn *irs, IrVarLifetimeDyn *var_lifetimes) {
  bool changed = false;
  for (u64 i = 0; i < irs->len; i++) {
    Ir *ir = PG_SLICE_AT_PTR(irs, i);
    if (ir->tombstone) {
      continue;
    }

    if (!(IR_KIND_LOAD == ir->kind || IR_KIND_ADD == ir->kind ||
          IR_KIND_SYSCALL == ir->kind)) {
      continue;
    }

    for (u64 j = 0; j < ir->operands.len; j++) {
      IrValue *val = PG_SLICE_AT_PTR(&ir->operands, j);
      if (!(IR_VALUE_KIND_VAR == val->kind)) {
        continue;
      }

      IrVar var = val->var;
      PG_ASSERT(var.id.value != 0);

      IrVarLifetime *lifetime =
          ir_find_var_lifetime_by_var_id(*var_lifetimes, var.id);
      PG_ASSERT(lifetime);

      IrId var_def_ir_id = lifetime->start;
      Ir *var_def_ir = irs_find_ir_by_id(*irs, var_def_ir_id);
      PG_ASSERT(var_def_ir);
      if (IR_KIND_LOAD != var_def_ir->kind) {
        continue;
      }
      PG_ASSERT(1 == var_def_ir->operands.len);
      IrValue var_def_val = PG_SLICE_AT(var_def_ir->operands, 0);
      bool is_immediate = IR_VALUE_KIND_U64 == var_def_val.kind;
      if (!is_immediate) {
        continue;
      }

      *val = var_def_val;
      changed = true;
    }
  }
  return changed;
}

[[nodiscard]]
static bool irs_optimize_fold_constants(IrDyn *irs) {
  bool changed = false;
  for (u64 i = 0; i < irs->len; i++) {
    Ir *ir = PG_SLICE_AT_PTR(irs, i);
    if (ir->tombstone) {
      continue;
    }

    if (!(IR_KIND_ADD == ir->kind)) {
      continue;
    }

    PG_ASSERT(2 == ir->operands.len);

    IrValue *lhs = PG_SLICE_AT_PTR(&ir->operands, 0);
    IrValue *rhs = PG_SLICE_AT_PTR(&ir->operands, 1);

    if (!(IR_VALUE_KIND_U64 == lhs->kind && IR_VALUE_KIND_U64 == rhs->kind)) {
      continue;
    }

    ir->kind = IR_KIND_LOAD;
    ir->operands.len = 0;
    IrValue val = {
        .kind = IR_VALUE_KIND_U64,
        .n64 = lhs->n64 + rhs->n64,
    };
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ir->operands) = val;
    changed = true;
  }
  return changed;
}

static void irs_optimize(IrDyn *irs, IrVarLifetimeDyn *var_lifetimes) {
  bool changed = false;

  u64 optimization_rounds = 0;
  do {
    changed = false;
    changed |= irs_optimize_remove_unused_vars(irs, var_lifetimes);
    if (changed) {
      irs_recompute_var_lifetimes(*irs, *var_lifetimes);
    }

    changed |= irs_optimize_remove_trivially_aliased_vars(irs, var_lifetimes);
    if (changed) {
      irs_recompute_var_lifetimes(*irs, *var_lifetimes);
    }

    changed |=
        irs_optimize_replace_immediate_vars_by_immediate(irs, var_lifetimes);
    if (changed) {
      irs_recompute_var_lifetimes(*irs, *var_lifetimes);
    }

    changed |= irs_optimize_fold_constants(irs);
    if (changed) {
      irs_recompute_var_lifetimes(*irs, *var_lifetimes);
    }

    optimization_rounds += 1;
  } while (changed);

  // TODO: Unify constants e.g. `x1 := 1; x2 := 1` => `x1 := 1`.
  // TODO: Simplify `if(true) { <then> } else { <else> }` => `<then>`
  // TODO: Remove empty labels.
  // TODO: Simplify syscall IR: replace vars by immediates.

  printf("[D002] %lu\n", optimization_rounds);
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

static void ir_emitter_print_var_lifetime(u64 i, IrVarLifetime var_lifetime) {
  if (var_lifetime.tombstone) {
    printf("\x1B[9m"); // Strikethrough.
  }

  printf("[%lu] ", i);
  ir_print_var(var_lifetime.var);
  printf(" lifetime: [%u:%u]", var_lifetime.start.value,
         var_lifetime.end.value);
  if (var_lifetime.ref.id.value) {
    printf(" ref=%u", var_lifetime.ref.id.value);
  }

  printf("\n");
  if (var_lifetime.tombstone) {
    printf("\x1B[0m"); // Strikethrough.
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
    printf(" // ");
    ir_emitter_print_var_lifetime(i, *var_lifetime);
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
    printf(" // ");
    ir_emitter_print_var_lifetime(i, *var_lifetime);
  } break;
  case IR_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir.operands.len);
    PG_ASSERT(0 != ir.var.id.value);

    ir_print_var(ir.var);
    printf(" := &");
    ir_print_value(PG_SLICE_AT(ir.operands, 0));

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var_id(emitter.var_lifetimes, ir.var.id);
    printf(" // ");
    ir_emitter_print_var_lifetime(i, *var_lifetime);
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
      printf(" // ");
      ir_emitter_print_var_lifetime(i, *var_lifetime);
    }
    printf("\n");
  } break;
  case IR_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ir.operands.len);
    PG_ASSERT(0 == ir.var.id.value);

    IrValue cond = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == cond.kind);

    IrValue branch_else = PG_SLICE_AT(ir.operands, 1);
    PG_ASSERT(IR_VALUE_KIND_LABEL == branch_else.kind);

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
    ir_emitter_print_var_lifetime(i, var_lifetime);
  }
}
