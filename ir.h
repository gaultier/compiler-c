#pragma once
#include "ast.h"
#include "submodules/cstd/lib.c"

typedef enum {
  IR_INSTRUCTION_KIND_NONE,
  IR_INSTRUCTION_KIND_ADD,
  IR_INSTRUCTION_KIND_LOAD,
  IR_INSTRUCTION_KIND_ADDRESS_OF,
  IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
  IR_INSTRUCTION_KIND_JUMP,
  IR_INSTRUCTION_KIND_LABEL,
#if 0
  IR_INSTRUCTION_KIND_SYSCALL,
#endif
} IrInstructionKind;

typedef struct {
  u32 value;
} IrVarId;

typedef struct {
  u32 value;
} IrInstructionIndex;

typedef struct {
  IrVarId id;
  PgString identifier;
} IrVar;
PG_SLICE(IrVar) IrVarSlice;
PG_DYN(IrVar) IrVarDyn;

typedef enum {
  IR_OPERAND_KIND_NONE,
  IR_OPERAND_KIND_U64,
  IR_OPERAND_KIND_VAR,
  IR_OPERAND_KIND_LABEL,
} IrOperandKind;

typedef struct {
  u32 value;
} IrLabelId;

typedef struct IrOperand IrOperand;
PG_SLICE(IrOperand) IrOperandSlice;
PG_DYN(IrOperand) IrOperandDyn;

struct IrOperand {
  IrOperandKind kind;
  union {
    u64 n64;
    IrVar var;
    IrLabelId label;
  };
};

typedef struct {
  IrInstructionKind kind;
  IrOperandDyn operands;
  Origin origin;
  // Result var. Not always present.
  IrVar res_var;

  // When optimizing, IRs are not directly removed but instead tombstoned.
  bool tombstone;
} IrInstruction;
PG_SLICE(IrInstruction) IrInstructionSlice;
PG_DYN(IrInstruction) IrInstructionDyn;

typedef struct {
  IrVar var;
  // Inclusive, inclusive.
  // TODO: Revamp when lifetime splitting is implemented.
  IrInstructionIndex start, end;

  // TODO: Probably remove and replace with a proper dataflow analysis (i.e.
  // what var uses which var including pointer aliases to the same var).
  IrVar ref; // In case of `IR_INSTRUCTION_KIND_ADDRESS_OF` or `x1 := x2`.
  // When optimizing, lifetimes are not directly removed but instead tombstoned.
  bool tombstone;
} IrVarLifetime;
PG_SLICE(IrVarLifetime) IrVarLifetimeSlice;
PG_DYN(IrVarLifetime) IrVarLifetimeDyn;

typedef struct {
  IrInstructionDyn instructions;
  // Gets incremented.
  IrLabelId label_id;
  // Gets incremented.
  IrVarId var_id;
  IrVarLifetimeDyn lifetimes;
} IrEmitter;

[[nodiscard]]
static IrLabelId ir_emitter_next_label_id(IrEmitter *emitter) {
  IrLabelId id = {.value = ++emitter->label_id.value};
  return id;
}

[[nodiscard]]
static IrVarId ir_emitter_next_var_id(IrEmitter *emitter) {
  IrVarId id = {.value = ++emitter->var_id.value};
  return id;
}

static IrVarLifetime *ir_find_var_lifetime_by_var_id(IrVarLifetimeDyn lifetimes,
                                                     IrVarId var_id) {
  if (0 == var_id.value) {
    return nullptr;
  }

  for (u64 i = 0; i < lifetimes.len; i++) {
    IrVarLifetime *lifetime = PG_SLICE_AT_PTR(&lifetimes, i);
    if (lifetime->var.id.value == var_id.value) {
      return lifetime;
    }
  }
  return nullptr;
}

static IrVarLifetime *
ir_find_var_lifetime_by_identifier(IrVarLifetimeDyn lifetimes,
                                   PgString identifier) {
  for (u64 i = 0; i < lifetimes.len; i++) {
    IrVarLifetime *lifetime = PG_SLICE_AT_PTR(&lifetimes, i);
    if (pg_string_eq(lifetime->var.identifier, identifier)) {
      return lifetime;
    }
  }
  return nullptr;
}

static void ir_var_extend_lifetime_on_var_use(IrVarLifetimeDyn lifetimes,
                                              IrVar var,
                                              IrInstructionIndex ins_idx) {
  IrVarLifetime *lifetime_var =
      ir_find_var_lifetime_by_var_id(lifetimes, var.id);
  PG_ASSERT(lifetime_var);
  lifetime_var->end = ins_idx;

  // Variable pointed to needs to live at least as long as the pointer to it.
  if (lifetime_var->ref.id.value != 0) {
    ir_var_extend_lifetime_on_var_use(lifetimes, lifetime_var->ref, ins_idx);
    // FIXME: If there are multiple aliases to the same pointer, all aliases
    // should have their lifetime extended to this point!
    // TODO: Dataflow.
  }
}

static IrOperand ast_to_ir(AstNode node, IrEmitter *emitter, ErrorDyn *errors,
                           bool is_immediate_ok, PgAllocator *allocator) {
  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64: {
    if (is_immediate_ok) {
      return (IrOperand){.kind = IR_OPERAND_KIND_U64, .n64 = node.n64};
    }
    IrInstruction ins = {
        .kind = IR_INSTRUCTION_KIND_LOAD,
        .origin = node.origin,
        .res_var.id = ir_emitter_next_var_id(emitter),
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = (IrOperand){
        .kind = IR_OPERAND_KIND_U64,
        .n64 = node.n64,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};

    *PG_DYN_PUSH(&emitter->lifetimes, allocator) = (IrVarLifetime){
        .var = ins.res_var,
        .start = ins_idx,
        .end = ins_idx,
    };
    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
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
    IrOperand lhs = ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors,
                              true, allocator);
    IrOperand rhs = ast_to_ir(PG_SLICE_AT(node.operands, 1), emitter, errors,
                              true, allocator);

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_ADD;
    ins.origin = node.origin;
    ins.res_var.id = ir_emitter_next_var_id(emitter);

    *PG_DYN_PUSH(&ins.operands, allocator) = lhs;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};

    *PG_DYN_PUSH(&emitter->lifetimes, allocator) = (IrVarLifetime){
        .var = ins.res_var,
        .start = ins_idx,
        .end = ins_idx,
    };

    if (IR_OPERAND_KIND_VAR == lhs.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->lifetimes, lhs.var, ins_idx);
    }
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->lifetimes, rhs.var, ins_idx);
    }

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }

#if 0
  case AST_NODE_KIND_SYSCALL: {
    IrOperandDyn operands = {0};
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      IrOperand operand = ast_to_ir(child, emitter, errors, true, allocator);

      *PG_DYN_PUSH(&operands, allocator) = operand;
    }

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_SYSCALL;
    ins.origin = node.origin;
    ins.operands = operands;
    ins.res_var.id = ir_emitter_next_var_id(emitter);
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};

    for (u64 i = 0; i < node.operands.len; i++) {
      IrOperand val = PG_SLICE_AT(ins.operands, i);
      if (IR_OPERAND_KIND_VAR == val.kind) {
        IrVar var = val.var;
        ir_var_extend_lifetime_on_var_use(emitter->lifetimes, var, ins_idx);
      }
    }

    *PG_DYN_PUSH(&emitter->lifetimes, allocator) = (IrVarLifetime){
        .var = ins.res_var,
        .start = ins_idx,
        .end = ins_idx,
    };

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }
#endif
  case AST_NODE_KIND_BLOCK: {
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      ast_to_ir(child, emitter, errors, false, allocator);
    }
    // TODO: Label?
    return (IrOperand){0};
  }
  case AST_NODE_KIND_VAR_DECL: {
    PG_ASSERT(1 == node.operands.len);
    PG_ASSERT(!pg_string_is_empty(node.identifier));

    AstNode rhs_node = PG_SLICE_AT(node.operands, 0);
    IrOperand rhs = ast_to_ir(rhs_node, emitter, errors, true, allocator);

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_LOAD;
    ins.origin = node.origin;
    ins.res_var.id = ir_emitter_next_var_id(emitter);
    ins.res_var.identifier = node.identifier;

    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};

    IrVarLifetime *rhs_lifetime = nullptr;
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->lifetimes, rhs.var, ins_idx);
      rhs_lifetime =
          ir_find_var_lifetime_by_var_id(emitter->lifetimes, rhs.var.id);
      PG_ASSERT(rhs_lifetime);
    }

    IrVarLifetime lifetime = {
        .var = ins.res_var,
        .ref = rhs_lifetime ? rhs_lifetime->var : (IrVar){0},
        .start = ins_idx,
        .end = ins_idx,
    };
    *PG_DYN_PUSH(&emitter->lifetimes, allocator) = lifetime;

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }

  case AST_NODE_KIND_IDENTIFIER: {
    IrVarLifetime *lifetime =
        ir_find_var_lifetime_by_identifier(emitter->lifetimes, node.identifier);

    if (!lifetime) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_UNDEFINED_VAR,
          .origin = node.origin,
      };
      return (IrOperand){0};
    }

    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};
    ir_var_extend_lifetime_on_var_use(emitter->lifetimes, lifetime->var,
                                      ins_idx);

    return (IrOperand){
        .kind = IR_OPERAND_KIND_VAR,
        .var = lifetime->var,
    };
  }

  case AST_NODE_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == node.operands.len);
    AstNode operand = PG_SLICE_AT(node.operands, 0);
    PG_ASSERT(AST_NODE_KIND_IDENTIFIER == operand.kind);

    IrOperand rhs = ast_to_ir(operand, emitter, errors, false, allocator);
    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_ADDRESS_OF;
    ins.origin = node.origin;
    ins.res_var.id = ir_emitter_next_var_id(emitter);
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};

    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->lifetimes, rhs.var, ins_idx);
    } else {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER,
          .origin = node.origin,
      };
      return (IrOperand){0};
    }

    *PG_DYN_PUSH(&emitter->lifetimes, allocator) = (IrVarLifetime){
        .var = ins.res_var,
        .ref = rhs.var,
        .start = ins_idx,
        .end = ins_idx,
    };

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }

  case AST_NODE_KIND_IF: {
    PG_ASSERT(2 == node.operands.len);
    IrOperand cond = ast_to_ir(PG_SLICE_AT(node.operands, 0), emitter, errors,
                               false, allocator);
    // TODO: else.

    IrInstruction ir_cond_jump = {
        .kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
        .origin = node.origin,
    };
    *PG_DYN_PUSH(&ir_cond_jump.operands, allocator) = cond;
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ir_cond_jump;
    IrInstructionIndex ir_cond_jump_idx = {
        (u32)(emitter->instructions.len - 1)};

    if (IR_OPERAND_KIND_VAR == cond.kind) {
      ir_var_extend_lifetime_on_var_use(emitter->lifetimes, cond.var,
                                        ir_cond_jump_idx);
    }

    IrLabelId branch_if_cont_label = ir_emitter_next_label_id(emitter);
    IrLabelId branch_else_label = ir_emitter_next_label_id(emitter);

    // 'then' branch.
    {
      ast_to_ir(PG_SLICE_AT(node.operands, 1), emitter, errors, false,
                allocator);
      IrInstruction ir_jump = {
          .kind = IR_INSTRUCTION_KIND_JUMP,
          .origin = node.origin,
      };
      *PG_DYN_PUSH(&ir_jump.operands, allocator) = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .label = branch_if_cont_label,
      };
      *PG_DYN_PUSH(&emitter->instructions, allocator) = ir_jump;
    }

    // 'else' branch.
    {
      IrInstruction ir_label_else = {
          .kind = IR_INSTRUCTION_KIND_LABEL,
          .origin = node.origin,
      };
      *PG_DYN_PUSH(&ir_label_else.operands, allocator) = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .label = branch_else_label,
      };
      *PG_DYN_PUSH(&emitter->instructions, allocator) = ir_label_else;
      if (3 == node.operands.len) {
        ast_to_ir(PG_SLICE_AT(node.operands, 2), emitter, errors, false,
                  allocator);
      }
    }
    IrInstruction ir_label_if_cont = {
        .kind = IR_INSTRUCTION_KIND_LABEL,
        .origin = node.origin,
    };
    *PG_DYN_PUSH(&ir_label_if_cont.operands, allocator) = (IrOperand){
        .kind = IR_OPERAND_KIND_LABEL,
        .label = branch_if_cont_label,
    };
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ir_label_if_cont;

    IrInstruction *ir_cond_jump_backpatch =
        PG_SLICE_AT_PTR(&emitter->instructions, ir_cond_jump_idx.value);
    *PG_DYN_PUSH(&ir_cond_jump_backpatch->operands, allocator) = (IrOperand){
        .kind = IR_OPERAND_KIND_LABEL,
        .label = branch_else_label,
    };

    return (IrOperand){0};
  }

  default:
    PG_ASSERT(0);
  }
}

static void irs_recompute_var_lifetimes(IrInstructionDyn instructions,
                                        IrVarLifetimeDyn lifetimes) {
  for (u64 i = 0; i < lifetimes.len; i++) {
    IrVarLifetime *lifetime = PG_SLICE_AT_PTR(&lifetimes, i);
    lifetime->tombstone = true;
    lifetime->end = lifetime->start;
  }

  for (u64 i = 0; i < instructions.len; i++) {
    IrInstruction ins = PG_SLICE_AT(instructions, i);
    if (ins.tombstone) {
      continue;
    }

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_ADD:
    case IR_INSTRUCTION_KIND_LOAD:
#if 0
    case IR_INSTRUCTION_KIND_SYSCALL:
#endif
    case IR_INSTRUCTION_KIND_ADDRESS_OF:
    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
      for (u64 j = 0; j < ins.operands.len; j++) {
        IrOperand val = PG_SLICE_AT(ins.operands, j);
        if (IR_OPERAND_KIND_VAR != val.kind) {
          continue;
        }

        IrVarLifetime *lifetime =
            ir_find_var_lifetime_by_var_id(lifetimes, val.var.id);
        PG_ASSERT(lifetime);
        lifetime->end = (IrInstructionIndex){(u32)i};
        lifetime->tombstone = false;
      }
    } break;
    case IR_INSTRUCTION_KIND_JUMP:
    case IR_INSTRUCTION_KIND_LABEL:
      break;
    case IR_INSTRUCTION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }
}

[[nodiscard]]
static bool irs_optimize_remove_unused_vars(IrInstructionDyn *instructions,
                                            IrVarLifetimeDyn *lifetimes) {
  bool changed = false;

  for (u64 i = 0; i < instructions->len; i++) {
    IrInstruction *ins = PG_SLICE_AT_PTR(instructions, i);
    if (ins->tombstone) {
      continue;
    }

    // Some IRs do not result in a variable.
    if (0 == ins->res_var.id.value) {
      continue;
    }

    IrVarLifetime *lifetime =
        ir_find_var_lifetime_by_var_id(*lifetimes, ins->res_var.id);
    PG_ASSERT(lifetime);
    if (lifetime->tombstone) {
      goto do_rm;
    }

    PG_ASSERT(lifetime->start.value <= lifetime->end.value);
    u64 duration = lifetime->end.value - lifetime->start.value;
    if (duration > 0) {
      // Used: no-op.
      continue;
    }

  do_rm:

    lifetime->tombstone = true;

#if 0
    // Possible side-effects: keep this IR but erase the variable.
    if (IR_INSTRUCTION_KIND_SYSCALL == ins->kind) {
      ins->res_var.id.value = 0;
      continue;
    }
#endif

    ins->tombstone = true;
    changed = true;
  }
  return changed;
}

// Simplify: `x1 := 1; x2 := x1` => `x2 := 1`
// and update subsequent IRs referencing the old var to use the new var.
[[nodiscard]]
static bool
irs_optimize_remove_trivially_aliased_vars(IrInstructionDyn *instructions,
                                           IrVarLifetimeDyn *lifetimes) {
  bool changed = false;

  for (u64 i = 0; i < instructions->len; i++) {
    IrInstruction *ins = PG_SLICE_AT_PTR(instructions, i);
    if (ins->tombstone) {
      continue;
    }

    if (0 == ins->res_var.id.value) {
      continue;
    }

    if (1 != ins->operands.len) {
      continue;
    }

    // TODO: Are there other IR kinds candidate to this simplification?
    if (!(IR_INSTRUCTION_KIND_LOAD == ins->kind)) {
      continue;
    }

    IrOperand rhs = PG_SLICE_AT(ins->operands, 0);

    // TODO: We could also simplify `x1 := 1; x2 := 2; x3 := x2 + x1` => `x2 :=
    // 2; x3 := x2 + 1`.
    if (!(IR_OPERAND_KIND_VAR == rhs.kind)) {
      continue;
    }

    IrVar rhs_var = rhs.var;
    IrVar var_to_rm = ins->res_var;

    for (u64 j = i + 1; j < instructions->len; j++) {
      IrInstruction ir_to_fix = PG_SLICE_AT(*instructions, j);
      if (ir_to_fix.tombstone) {
        continue;
      }

      for (u64 k = 0; k < ir_to_fix.operands.len; k++) {
        IrOperand *op = PG_SLICE_AT_PTR(&ir_to_fix.operands, k);

        if (IR_OPERAND_KIND_VAR == op->kind &&
            op->var.id.value == var_to_rm.id.value) {
          op->var = rhs_var;
        }
      }
    }
    ins->tombstone = true;
    IrVarLifetime *lifetime =
        ir_find_var_lifetime_by_var_id(*lifetimes, ins->res_var.id);
    PG_ASSERT(!lifetime->tombstone);
    lifetime->tombstone = true;
    changed = true;
  }
  return changed;
}

[[nodiscard]] static IrInstruction *
irs_find_ir_by_id(IrInstructionDyn instructions, IrInstructionIndex ins_idx) {
  for (u64 i = 0; i < instructions.len; i++) {
    IrInstruction *ins = PG_SLICE_AT_PTR(&instructions, i);
    if (i == ins_idx.value) {
      return ins;
    }
  }
  return nullptr;
}

// Replace: `x1 := 1; x2 := 2; x3:= x2 + x1` => `x2 := 2; x3 := 2 + 1`
// and another optimization pass may then constant fold into `x3 := 3`.
[[nodiscard]]
static bool irs_optimize_replace_immediate_vars_by_immediate_value(
    IrInstructionDyn *instructions, IrVarLifetimeDyn *lifetimes) {
  bool changed = false;
  for (u64 i = 0; i < instructions->len; i++) {
    IrInstruction *ins = PG_SLICE_AT_PTR(instructions, i);
    if (ins->tombstone) {
      continue;
    }

    if (!(IR_INSTRUCTION_KIND_LOAD == ins->kind ||
          IR_INSTRUCTION_KIND_ADD == ins->kind ||
#if 0
          IR_INSTRUCTION_KIND_SYSCALL == ins->kind ||
#endif
          IR_INSTRUCTION_KIND_JUMP_IF_FALSE == ins->kind)) {
      continue;
    }

    for (u64 j = 0; j < ins->operands.len; j++) {
      IrOperand *val = PG_SLICE_AT_PTR(&ins->operands, j);
      if (!(IR_OPERAND_KIND_VAR == val->kind)) {
        continue;
      }

      IrVar var = val->var;
      PG_ASSERT(var.id.value != 0);

      IrVarLifetime *lifetime =
          ir_find_var_lifetime_by_var_id(*lifetimes, var.id);
      PG_ASSERT(lifetime);

      IrInstructionIndex var_def_ins_idx = lifetime->start;
      IrInstruction *var_def_ins =
          irs_find_ir_by_id(*instructions, var_def_ins_idx);
      PG_ASSERT(var_def_ins);
      if (IR_INSTRUCTION_KIND_LOAD != var_def_ins->kind) {
        continue;
      }
      PG_ASSERT(1 == var_def_ins->operands.len);
      IrOperand var_def_val = PG_SLICE_AT(var_def_ins->operands, 0);
      bool is_immediate = IR_OPERAND_KIND_U64 == var_def_val.kind;
      if (!is_immediate) {
        continue;
      }

      *val = var_def_val;
      changed = true;
    }
  }
  return changed;
}

// Replace: `x1 := 1 + 2` => `x1 := 3`.
[[nodiscard]]
static bool irs_optimize_fold_constants(IrInstructionDyn *instructions) {
  bool changed = false;
  for (u64 i = 0; i < instructions->len; i++) {
    IrInstruction *ins = PG_SLICE_AT_PTR(instructions, i);
    if (ins->tombstone) {
      continue;
    }

    if (!(IR_INSTRUCTION_KIND_ADD == ins->kind)) {
      continue;
    }

    PG_ASSERT(2 == ins->operands.len);

    IrOperand *lhs = PG_SLICE_AT_PTR(&ins->operands, 0);
    IrOperand *rhs = PG_SLICE_AT_PTR(&ins->operands, 1);

    if (!(IR_OPERAND_KIND_U64 == lhs->kind &&
          IR_OPERAND_KIND_U64 == rhs->kind)) {
      continue;
    }

    ins->kind = IR_INSTRUCTION_KIND_LOAD;
    ins->operands.len = 0;
    IrOperand val = {
        .kind = IR_OPERAND_KIND_U64,
        .n64 = lhs->n64 + rhs->n64,
    };
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins->operands) = val;
    changed = true;
  }
  return changed;
}

[[nodiscard]]
static bool irs_optimize_remove_trivial_falsy_or_truthy_branches(
    IrInstructionDyn *instructions) {
  bool changed = false;
  for (u64 i = 0; i < instructions->len; i++) {
    IrInstruction *ins = PG_SLICE_AT_PTR(instructions, i);
    if (ins->tombstone) {
      continue;
    }

    if (!(IR_INSTRUCTION_KIND_JUMP_IF_FALSE == ins->kind)) {
      continue;
    }

    PG_ASSERT(2 == ins->operands.len);

    IrOperand cond = PG_SLICE_AT(ins->operands, 0);
    if (IR_OPERAND_KIND_U64 != cond.kind) {
      continue;
    }

    if (cond.n64) { // We will never jump => remove this IR.
      // TODO: Mark IRs coming from <else> branch as tombstoned.
      ins->tombstone = true;
      changed = true;
    } else { // We will always jump => replace this IR by an unconditional jump.
      // TODO: Mark IRs coming from <then> branch as tombstoned.
      ins->kind = IR_INSTRUCTION_KIND_JUMP;

      PG_DYN_SWAP_REMOVE(&ins->operands, 0);
    }
  }
  return changed;
}

static void irs_optimize(IrInstructionDyn *instructions,
                         IrVarLifetimeDyn *lifetimes, bool verbose) {
  bool changed = false;

  u64 optimization_rounds = 0;
  do {
    changed = false;
    changed |= irs_optimize_remove_unused_vars(instructions, lifetimes);
    if (changed) {
      irs_recompute_var_lifetimes(*instructions, *lifetimes);
    }

    changed |=
        irs_optimize_remove_trivially_aliased_vars(instructions, lifetimes);
    if (changed) {
      irs_recompute_var_lifetimes(*instructions, *lifetimes);
    }

    changed |= irs_optimize_replace_immediate_vars_by_immediate_value(
        instructions, lifetimes);
    if (changed) {
      irs_recompute_var_lifetimes(*instructions, *lifetimes);
    }

    changed |= irs_optimize_fold_constants(instructions);
    if (changed) {
      irs_recompute_var_lifetimes(*instructions, *lifetimes);
    }

    changed |=
        irs_optimize_remove_trivial_falsy_or_truthy_branches(instructions);
    if (changed) {
      irs_recompute_var_lifetimes(*instructions, *lifetimes);
    }

    optimization_rounds += 1;
  } while (changed);

  // TODO: Unify constants e.g. `x1 := 1; x2 := 1` => `x1 := 1`.
  // TODO: Simplify `if(true) { <then> } else { <else> }` => `<then>`
  // TODO: Simplify `if(false) { <then> } else { <else> }` => `<else>`
  // TODO: Remove empty labels.

  if (verbose) {
    printf("[D010] optimization_rounds=%lu\n", optimization_rounds);
  }
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

static void ir_print_operand(IrOperand value) {
  switch (value.kind) {
  case IR_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case IR_OPERAND_KIND_U64:
    printf("%" PRIu64, value.n64);
    break;
  case IR_OPERAND_KIND_VAR:
    ir_print_var(value.var);
    break;
  case IR_OPERAND_KIND_LABEL:
    printf(".%" PRIu32 "", value.label.value);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void ir_emitter_print_var_lifetime(u64 i, IrVarLifetime lifetime) {
  if (lifetime.tombstone) {
    printf("\x1B[9m"); // Strikethrough.
  }

  printf("[%lu] ", i);
  ir_print_var(lifetime.var);
  printf(" lifetime: [%u:%u]", lifetime.start.value, lifetime.end.value);
  if (lifetime.ref.id.value) {
    printf(" ref=%u", lifetime.ref.id.value);
  }

  printf("\n");
  if (lifetime.tombstone) {
    printf("\x1B[0m"); // Strikethrough.
  }
}

static void ir_emitter_print_instruction(IrEmitter emitter, u32 i) {
  IrInstruction ins = PG_SLICE_AT(emitter.instructions, i);

  if (ins.tombstone) {
    printf("\x1B[9m"); // Strikethrough.
  }

  origin_print(ins.origin);
  printf(": [%u] ", i);

  switch (ins.kind) {
  case IR_INSTRUCTION_KIND_NONE:
    PG_ASSERT(0);
  case IR_INSTRUCTION_KIND_ADD: {
    PG_ASSERT(2 == ins.operands.len);
    PG_ASSERT(0 != ins.res_var.id.value);

    ir_print_var(ins.res_var);
    printf(" := ");
    ir_print_operand(PG_SLICE_AT(ins.operands, 0));
    printf(" + ");
    ir_print_operand(PG_SLICE_AT(ins.operands, 1));

    IrVarLifetime *lifetime =
        ir_find_var_lifetime_by_var_id(emitter.lifetimes, ins.res_var.id);
    PG_ASSERT(lifetime);
    printf(" // ");
    ir_emitter_print_var_lifetime(i, *lifetime);
  } break;
  case IR_INSTRUCTION_KIND_LOAD: {
    PG_ASSERT(1 == ins.operands.len);
    PG_ASSERT(0 != ins.res_var.id.value);

    IrOperand rhs = PG_SLICE_AT(ins.operands, 0);
    ir_print_var(ins.res_var);
    printf(" := ");
    ir_print_operand(rhs);

    IrVarLifetime *lifetime =
        ir_find_var_lifetime_by_var_id(emitter.lifetimes, ins.res_var.id);
    PG_ASSERT(lifetime);
    printf(" // ");
    ir_emitter_print_var_lifetime(i, *lifetime);
  } break;
  case IR_INSTRUCTION_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ins.operands.len);
    PG_ASSERT(0 != ins.res_var.id.value);

    ir_print_var(ins.res_var);
    printf(" := &");
    ir_print_operand(PG_SLICE_AT(ins.operands, 0));

    IrVarLifetime *lifetime =
        ir_find_var_lifetime_by_var_id(emitter.lifetimes, ins.res_var.id);
    printf(" // ");
    ir_emitter_print_var_lifetime(i, *lifetime);
  } break;
#if 0
  case IR_INSTRUCTION_KIND_SYSCALL: {
    ir_print_var(ins.res_var);
    printf("%ssyscall(", 0 == ins.res_var.id.value ? "" : " := ");

    for (u64 j = 0; j < ins.operands.len; j++) {
      IrOperand val = PG_SLICE_AT(ins.operands, j);
      ir_print_operand(val);

      if (j + 1 < ins.operands.len) {
        printf(", ");
      }
    }

    printf(")");

    if (0 != ins.res_var.id.value) {
      IrVarLifetime *lifetime =
          ir_find_var_lifetime_by_var_id(emitter.lifetimes, ins.res_var.id);
      PG_ASSERT(lifetime);
      printf(" // ");
      ir_emitter_print_var_lifetime(i, *lifetime);
    }
    printf("\n");
  } break;
#endif
  case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ins.operands.len);
    PG_ASSERT(0 == ins.res_var.id.value);

    IrOperand cond = PG_SLICE_AT(ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_VAR == cond.kind ||
              IR_OPERAND_KIND_U64 == cond.kind);

    IrOperand branch_else = PG_SLICE_AT(ins.operands, 1);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == branch_else.kind);

    printf("jump_if_false(");
    ir_print_operand(cond);
    printf(", ");
    ir_print_operand(branch_else);
    printf(")\n");
  } break;
  case IR_INSTRUCTION_KIND_JUMP: {
    PG_ASSERT(1 == ins.operands.len);
    PG_ASSERT(0 == ins.res_var.id.value);

    IrOperand label = PG_SLICE_AT(ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == label.kind);
    printf("jump .%u\n", label.label.value);
  } break;

  case IR_INSTRUCTION_KIND_LABEL: {
    PG_ASSERT(1 == ins.operands.len);
    PG_ASSERT(0 == ins.res_var.id.value);

    IrOperand label = PG_SLICE_AT(ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == label.kind);

    printf(".%u:\n", label.label.value);
  } break;
  default:
    PG_ASSERT(0);
  }
  if (ins.tombstone) {
    printf("\x1B[0m"); // Reset.
  }
}

static void ir_emitter_print_instructions(IrEmitter emitter) {
  for (u64 i = 0; i < emitter.instructions.len; i++) {
    ir_emitter_print_instruction(emitter, (u32)i);
  }
}

static void ir_emitter_print_var_lifetimes(IrEmitter emitter) {
  for (u64 i = 0; i < emitter.lifetimes.len; i++) {
    IrVarLifetime lifetime = PG_SLICE_AT(emitter.lifetimes, i);
    ir_emitter_print_var_lifetime(i, lifetime);
  }
}

static void ir_emitter_trim_tombstone_items(IrEmitter *emitter) {
  for (u64 i = 0; i < emitter->instructions.len;) {
    IrInstruction ins = PG_SLICE_AT(emitter->instructions, i);
    if (ins.tombstone) {
      PG_DYN_REMOVE_AT(&emitter->instructions, i);
      continue;
    }
    i++;
  }

  for (u64 i = 0; i < emitter->lifetimes.len;) {
    IrVarLifetime lifetime = PG_SLICE_AT(emitter->lifetimes, i);
    if (lifetime.tombstone) {
      PG_DYN_REMOVE_AT(&emitter->lifetimes, i);
      continue;
    }
    i++;
  }
}
