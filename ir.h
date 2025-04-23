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
  u32 value;
} IrId;

typedef struct {
  IrKind kind;
  IrValueDyn operands;
  Origin origin;
  IrId id;
} Ir;
PG_SLICE(Ir) IrSlice;
PG_DYN(Ir) IrDyn;

typedef struct {
  PgString identifier;
  IrVar var;
} IrIdentifierToVar;
PG_DYN(IrIdentifierToVar) IrIdentifierToVarDyn;

typedef struct {
  IrVar var;
  // Inclusive, inclusive.
  IrId start, end;
  IrVar ref; // In case of `IR_KIND_ADDRESS_OF`.
} IrVarLifetime;
PG_SLICE(IrVarLifetime) IrVarLifetimeSlice;
PG_DYN(IrVarLifetime) IrVarLifetimeDyn;

typedef struct {
  IrDyn irs;
  IrId ir_id;
  IrLabelId label_id;
  IrIdentifierToVarDyn identifier_to_vars;
  IrVarLifetimeDyn var_lifetimes;
} IrEmitter;

[[nodiscard]]
static IrVar ir_id_to_var(IrId ir_id) {
  return (IrVar){ir_id.value};
}

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

static IrVarLifetime *
ir_find_var_lifetime_by_var(IrVarLifetimeDyn var_lifetimes, IrVar var) {
  for (u64 i = 0; i < var_lifetimes.len; i++) {
    IrVarLifetime *var_lifetime = PG_SLICE_AT_PTR(&var_lifetimes, i);
    if (var_lifetime->var.value == var.value) {
      return var_lifetime;
    }
  }
  return nullptr;
}

static void ir_var_extend_lifetime_on_var_use(IrVarLifetimeDyn var_lifetimes,
                                              IrVar var, IrId ir_id) {
  IrVarLifetime *lifetime_var = ir_find_var_lifetime_by_var(var_lifetimes, var);
  PG_ASSERT(lifetime_var);
  lifetime_var->end = ir_id;

  // Variable pointed to needs to live at least as long as the pointer to it.
  if (lifetime_var->ref.value != 0) {
    IrVarLifetime *lifetime_var_ref =
        ir_find_var_lifetime_by_var(var_lifetimes, lifetime_var->ref);
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
    };
    *PG_DYN_PUSH(&ir.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_U64,
        .n64 = node.n64,
    };

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir_id_to_var(ir.id),
        .start = ir.id,
        .end = ir.id,
    };
    return ir_id_to_var(ir.id);
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
    IrVar lhs =
        ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors, allocator);
    IrVar rhs =
        ast_to_ir(PG_SLICE_AT(node.operands, 1), emitter, errors, allocator);

    Ir ir = {
        .kind = IR_KIND_ADD,
        .origin = node.origin,
        .id = ir_emitter_next_ir_id(emitter),
    };
    PG_ASSERT(lhs.value < ir.id.value);
    PG_ASSERT(rhs.value < ir.id.value);

    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = lhs};
    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = rhs};

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;
    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir_id_to_var(ir.id),
        .start = ir.id,
        .end = ir.id,
    };

    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, lhs, ir.id);
    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs, ir.id);

    return ir_id_to_var(ir.id);
  }

  case AST_NODE_KIND_SYSCALL: {
    IrValueDyn operands = {0};
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      IrVar operand = ast_to_ir(child, emitter, errors, allocator);

      *PG_DYN_PUSH(&operands, allocator) =
          (IrValue){.kind = IR_VALUE_KIND_VAR, .var = operand};
    }

    Ir ir = {
        .kind = IR_KIND_SYSCALL,
        .origin = node.origin,
        .id = ir_emitter_next_ir_id(emitter),
        .operands = operands,
    };
    for (u64 i = 0; i < node.operands.len; i++) {
      IrValue val = PG_SLICE_AT(ir.operands, i);
      PG_ASSERT(IR_VALUE_KIND_VAR == val.kind);
      IrVar var = val.var;
      PG_ASSERT(var.value < ir.id.value);

      ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, var, ir.id);
    }

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir_id_to_var(ir.id),
        .start = ir.id,
        .end = ir.id,
    };

    return ir_id_to_var(ir.id);
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

    IrVar rhs =
        ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors, allocator);
    Ir ir = {
        .kind = IR_KIND_LOAD,
        .origin = node.origin,
        .id = ir_emitter_next_ir_id(emitter),
    };
    PG_ASSERT(rhs.value < ir.id.value);

    *PG_DYN_PUSH(&ir.operands, allocator) = (IrValue){
        .kind = IR_VALUE_KIND_VAR,
        .var = rhs,
    };
    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs, ir.id);

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    ir_add_identifier_to_var(&emitter->identifier_to_vars, node.identifier, rhs,
                             allocator);

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir_id_to_var(ir.id),
        .start = ir.id,
        .end = ir.id,
    };

    return ir_id_to_var(ir.id);
  }

  case AST_NODE_KIND_IDENTIFIER: {
    IrIdentifierToVar *identifier_to_var =
        ir_find_identifier_to_var_by_identifier(emitter->identifier_to_vars,
                                                node.identifier);

    if (!identifier_to_var) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_UNDEFINED_VAR,
          .origin = node.origin,
      };
      return (IrVar){0};
    }

    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes,
                                      identifier_to_var->var, emitter->ir_id);

    return identifier_to_var->var;
  }

  case AST_NODE_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == node.operands.len);
    AstNode operand = PG_SLICE_AT(node.operands, 0);
    PG_ASSERT(AST_NODE_KIND_IDENTIFIER == operand.kind);

    IrVar rhs = ast_to_ir(operand, emitter, errors, allocator);
    Ir ir = {
        .kind = IR_KIND_ADDRESS_OF,
        .origin = node.origin,
        .id = ir_emitter_next_ir_id(emitter),
    };
    PG_ASSERT(rhs.value < ir.id.value);

    *PG_DYN_PUSH(&ir.operands, allocator) =
        (IrValue){.kind = IR_VALUE_KIND_VAR, .var = rhs};

    ir_var_extend_lifetime_on_var_use(emitter->var_lifetimes, rhs, ir.id);

    *PG_DYN_PUSH(&emitter->irs, allocator) = ir;

    *PG_DYN_PUSH(&emitter->var_lifetimes, allocator) = (IrVarLifetime){
        .var = ir_id_to_var(ir.id),
        .start = ir.id,
        .end = ir.id,
        .ref = rhs,
    };

    return ir_id_to_var(ir.id);
  }

  case AST_NODE_KIND_IF: {
    PG_ASSERT(2 == node.operands.len);
    IrVar cond =
        ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors, allocator);
    // TODO: then, else.

    Ir ir_cond_jump = {
        .kind = IR_KIND_JUMP_IF_FALSE,
        .origin = node.origin,
        .id = ir_emitter_next_ir_id(emitter),
    };
    PG_ASSERT(cond.value < ir_cond_jump.id.value);
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

// TODO: Constant folding.
static void irs_simplify(IrDyn *irs, IrVarLifetimeDyn *var_lifetimes) {
  for (u64 i = 0; i < irs->len;) {
    Ir ir = PG_SLICE_AT(*irs, i);
    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var(*var_lifetimes, ir_id_to_var(ir.id));

    // Some IRs do not result in a variable e.g. if-then-else.
    if (!var_lifetime) {
      i++;
      continue;
    }

    PG_ASSERT(var_lifetime->start.value <= var_lifetime->end.value);
    u64 duration = var_lifetime->end.value - var_lifetime->start.value;
    if (duration > 0) {
      i++;
      continue;
    }

    // Possible side-effects, keep this IR.
    if (IR_KIND_SYSCALL == ir.kind) {
      i++;
      continue;
    }

    PG_DYN_REMOVE_AT(irs, i);
    IrId ir_num_to_remove = ir.id;

    for (u64 j = i + 1; j < irs->len; j++) {
      Ir ir_to_fix = PG_SLICE_AT(*irs, j);

      for (u64 k = 0; k < ir_to_fix.operands.len; k++) {
        IrValue *operand = PG_SLICE_AT_PTR(&ir_to_fix.operands, k);
        if (IR_VALUE_KIND_VAR == operand->kind &&
            operand->var.value == ir_num_to_remove.value) {
          operand->var.value = PG_SLICE_AT(ir.operands, 0).var.value;
        }
      }
    }

    u64 var_lifetime_idx = (u64)(var_lifetime - var_lifetimes->data);
    PG_DYN_REMOVE_AT(var_lifetimes, var_lifetime_idx);
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
  case IR_VALUE_KIND_LABEL:
    printf(".%" PRIu32 "", value.label.value);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void ir_emitter_print_ir(IrEmitter emitter, u32 i) {
  Ir ir = PG_SLICE_AT(emitter.irs, i);
  origin_print(ir.origin);
  printf(": ");

  switch (ir.kind) {
  case IR_KIND_NONE:
    PG_ASSERT(0);
  case IR_KIND_ADD: {
    PG_ASSERT(2 == ir.operands.len);
    printf("[%u] [%u] x%u := ", i, ir.id.value, ir.id.value);
    ir_print_value(PG_SLICE_AT(ir.operands, 0));
    printf(" + ");
    ir_print_value(PG_SLICE_AT(ir.operands, 1));

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var(emitter.var_lifetimes, ir_id_to_var(ir.id));
    PG_ASSERT(var_lifetime);
    printf(" // lifetime: [%u:%u]\n", var_lifetime->start.value,
           var_lifetime->end.value);
  } break;
  case IR_KIND_LOAD: {
    PG_ASSERT(1 == ir.operands.len);
    printf("[%u] [%u] x%u := ", i, ir.id.value, ir.id.value);
    ir_print_value(PG_SLICE_AT(ir.operands, 0));

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var(emitter.var_lifetimes, ir_id_to_var(ir.id));
    PG_ASSERT(var_lifetime);
    printf(" // lifetime: [%u:%u]\n", var_lifetime->start.value,
           var_lifetime->end.value);
  } break;
  case IR_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir.operands.len);
    printf("[%u] [%u] x%u := &", i, ir.id.value, ir.id.value);
    ir_print_value(PG_SLICE_AT(ir.operands, 0));

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var(emitter.var_lifetimes, ir_id_to_var(ir.id));
    PG_ASSERT(var_lifetime);
    printf(" // lifetime: [%u:%u]\n", var_lifetime->start.value,
           var_lifetime->end.value);
  } break;
  case IR_KIND_SYSCALL: {
    printf("[%u] [%u] x%u := syscall(", i, ir.id.value, ir.id.value);
    for (u64 j = 0; j < ir.operands.len; j++) {
      IrValue val = PG_SLICE_AT(ir.operands, j);
      ir_print_value(val);

      if (j + 1 < ir.operands.len) {
        printf(", ");
      }
    }

    IrVarLifetime *var_lifetime =
        ir_find_var_lifetime_by_var(emitter.var_lifetimes, ir_id_to_var(ir.id));
    PG_ASSERT(var_lifetime);
    printf(") // lifetime: [%u:%u]\n", var_lifetime->start.value,
           var_lifetime->end.value);
  } break;
  case IR_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ir.operands.len);
    IrValue cond = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_VAR == cond.kind);

    IrValue branch_else = PG_SLICE_AT(ir.operands, 1);

    printf("[%u] [%u] jump_if_false(", i, ir.id.value);
    ir_print_value(cond);
    printf(", ");
    ir_print_value(branch_else);
    printf(")\n");
  } break;
  case IR_KIND_JUMP: {
    PG_ASSERT(1 == ir.operands.len);
    IrValue label = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_LABEL == label.kind);
    printf("[%u] [%u] jump .%u\n", i, ir.id.value, label.label.value);
  } break;

  case IR_KIND_LABEL: {
    PG_ASSERT(1 == ir.operands.len);
    IrValue label = PG_SLICE_AT(ir.operands, 0);
    PG_ASSERT(IR_VALUE_KIND_LABEL == label.kind);

    printf("[%u] [%u] .%u:\n", i, ir.id.value, label.label.value);
  } break;
  default:
    PG_ASSERT(0);
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
    printf("[%lu] x%u lifetime: [%u:%u]\n", i, var_lifetime.var.value,
           var_lifetime.start.value, var_lifetime.end.value);
  }
}
