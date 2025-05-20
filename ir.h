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
  IR_INSTRUCTION_KIND_LABEL_DEFINITION,
  IR_INSTRUCTION_KIND_COMPARISON,
  IR_INSTRUCTION_KIND_SYSCALL,
} IrInstructionKind;

typedef enum {
  IR_OPERAND_KIND_NONE,
  IR_OPERAND_KIND_NUMBER,
  IR_OPERAND_KIND_VAR,
  IR_OPERAND_KIND_LABEL,
} IrOperandKind;

typedef struct IrOperand IrOperand;
PG_SLICE(IrOperand) IrOperandSlice;
PG_DYN(IrOperand) IrOperandDyn;

struct IrOperand {
  IrOperandKind kind;
  union {
    u64 n64;
    MetadataIndex meta_idx;
    Label label; // IR_OPERAND_KIND_LABEL.
  } u;
};

typedef struct {
  IrInstructionKind kind;
  LexTokenKind token_kind;
  Origin origin;
  // Result var. Not always present.
  MetadataIndex meta_idx;

  // When optimizing, IRs are not directly removed but instead tombstoned.
#if 0
  bool tombstone;
#endif
} IrInstruction;
PG_SLICE(IrInstruction) IrInstructionSlice;
PG_DYN(IrInstruction) IrInstructionDyn;

typedef struct {
  PgString name;
  AstNodeFlag flags;

  // TODO: Arguments.

  IrInstructionDyn instructions;
  MetadataDyn metadata;
} FnDefinition;
PG_DYN(FnDefinition) FnDefinitionDyn;

typedef struct {
  AstParser parser;
  FnDefinitionDyn fn_definitions;

  // Gets incremented.
  u32 label_id;

  u32 node_idx;

  Label label_program_epilog_die;
  Label label_program_epilog_exit;
} IrEmitter;

[[nodiscard]]
static Label ir_emitter_next_label_name(IrEmitter *emitter,
                                        PgAllocator *allocator) {

  Label id = {
      .value = pg_u64_to_string(++emitter->label_id, allocator),
  };
  return id;
}

[[nodiscard]]
static IrOperand ir_emit_ast_node(IrEmitter *emitter, FnDefinition *fn_def,
                                  ErrorDyn *errors, PgAllocator *allocator) {
  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_NUMBER: {
    MetadataIndex meta_idx = metadata_make(&fn_def->metadata, allocator);
    metadata_start_lifetime(fn_def->metadata, meta_idx,
                            (InstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {
        .kind = IR_INSTRUCTION_KIND_LOAD,
        .origin = node.origin,
        .meta_idx = meta_idx,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = (IrOperand){
        .kind = IR_OPERAND_KIND_NUMBER,
        .u.n64 = node.u.n64,
    };

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;
    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
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
    IrOperand lhs = ir_emit_ast_node(PG_SLICE_AT(node.operands, 0), emitter,
                                     fn_def, errors, allocator);
    IrOperand rhs = ir_emit_ast_node(PG_SLICE_AT(node.operands, 1), emitter,
                                     fn_def, errors, allocator);

    MetadataIndex meta_idx = metadata_make(&fn_def->metadata, allocator);
    metadata_start_lifetime(fn_def->metadata, meta_idx,
                            (InstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_ADD;
    ins.origin = node.origin;
    ins.meta_idx = meta_idx;

    *PG_DYN_PUSH(&ins.operands, allocator) = lhs;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;
    InstructionIndex ins_idx =
        PG_SLICE_AT(fn_def->metadata, meta_idx.value).lifetime_start;

    if (IR_OPERAND_KIND_VAR == lhs.kind) {
      metadata_extend_lifetime_on_use(fn_def->metadata, lhs.u.meta_idx,
                                      ins_idx);
    }
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      metadata_extend_lifetime_on_use(fn_def->metadata, rhs.u.meta_idx,
                                      ins_idx);
    }

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
  }

  case AST_NODE_KIND_COMPARISON: {
    PG_ASSERT(2 == node.operands.len);
    IrOperand lhs = ir_emit_ast_node(PG_SLICE_AT(node.operands, 0), emitter,
                                     fn_def, errors, allocator);
    IrOperand rhs = ir_emit_ast_node(PG_SLICE_AT(node.operands, 1), emitter,
                                     fn_def, errors, allocator);
    PG_ASSERT(LEX_TOKEN_KIND_EQUAL_EQUAL == node.token_kind);

    MetadataIndex meta_idx = metadata_make(&fn_def->metadata, allocator);
    metadata_start_lifetime(fn_def->metadata, meta_idx,
                            (InstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_COMPARISON;
    ins.origin = node.origin;
    ins.token_kind = node.token_kind;
    ins.meta_idx = meta_idx;

    *PG_DYN_PUSH(&ins.operands, allocator) = lhs;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

    InstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};

    if (IR_OPERAND_KIND_VAR == lhs.kind) {
      metadata_extend_lifetime_on_use(fn_def->metadata, lhs.u.meta_idx,
                                      ins_idx);
    }
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      metadata_extend_lifetime_on_use(fn_def->metadata, rhs.u.meta_idx,
                                      ins_idx);
    }

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
  }

  case AST_NODE_KIND_SYSCALL: {
    IrOperandDyn operands = {0};
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      IrOperand operand =
          ir_emit_ast_node(child, emitter, fn_def, errors, allocator);

      *PG_DYN_PUSH(&operands, allocator) = operand;
    }

    MetadataIndex meta_idx = metadata_make(&fn_def->metadata, allocator);
    metadata_start_lifetime(fn_def->metadata, meta_idx,
                            (InstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_SYSCALL;
    ins.origin = node.origin;
    ins.operands = operands;
    ins.meta_idx = meta_idx;
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

    InstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};
    for (u64 i = 0; i < node.operands.len; i++) {
      IrOperand val = PG_SLICE_AT(ins.operands, i);
      if (IR_OPERAND_KIND_VAR == val.kind) {
        ir_metadata_extend_lifetime_on_use(fn_def->metadata, val.u.meta_idx,
                                           ins_idx);
      }
    }

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
  }
  case AST_NODE_KIND_BLOCK: {
    if (!pg_string_is_empty(node.u.identifier)) {

      Label label = {.value = node.u.identifier};

      IrInstruction ir_label = {
          .kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION,
          .origin = node.origin,
      };
      *PG_DYN_PUSH(&ir_label.operands, allocator) = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = label,
      };
      *PG_DYN_PUSH(&fn_def->instructions, allocator) = ir_label;
    }

    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      (void)ir_emit_ast_node(child, emitter, fn_def, errors, allocator);
    }
    return (IrOperand){0};
  }
  case AST_NODE_KIND_FN_DEFINITION: {
    PG_ASSERT(!pg_string_is_empty(node.u.identifier));

    PG_ASSERT(!fn_def);
    FnDefinition fn_def_real = (IrFnDefinition){
        .name = node.u.identifier,
        .flags = node.flags,
    };
    fn_def = &fn_def_real;
    *PG_DYN_PUSH(&fn_def->metadata, allocator) = (Metadata){0}; // Dummy.

    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      (void)ir_emit_ast_node(child, emitter, fn_def, errors, allocator);
    }
    // FIXME: Should be done in two-steps to enable recursion.
    *PG_DYN_PUSH(&emitter->fn_definitions, allocator) = *fn_def;
    return (IrOperand){0};
  }
  case AST_NODE_KIND_VAR_DEFINITION: {
    PG_ASSERT(1 == node.operands.len);
    PG_ASSERT(!pg_string_is_empty(node.u.identifier));

    AstNode rhs_node = PG_SLICE_AT(node.operands, 0);
    IrOperand rhs =
        ir_emit_ast_node(rhs_node, emitter, fn_def, errors, allocator);

    MetadataIndex meta_idx = metadata_make(&fn_def->metadata, allocator);
    PG_SLICE_AT(fn_def->metadata, meta_idx.value).identifier =
        node.u.identifier;
    metadata_start_lifetime(fn_def->metadata, meta_idx,
                            (InstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_LOAD;
    ins.origin = node.origin;
    ins.meta_idx = meta_idx;

    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

    InstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      metadata_extend_lifetime_on_use(fn_def->metadata, rhs.u.meta_idx,
                                      ins_idx);
    }

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
  }

  case AST_NODE_KIND_IDENTIFIER: {
    Metadata *meta =
        ir_find_metadata_by_identifier(fn_def->metadata, node.u.identifier);

    if (!meta) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_UNDEFINED_VAR,
          .origin = node.origin,
          .src = emitter->parser.lexer.src,
          .src_span = node.u.identifier,
      };
      return (IrOperand){0};
    }

    MetadataIndex meta_idx = metadata_ptr_to_idx(fn_def->metadata, meta);

    InstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};
    metadata_extend_lifetime_on_use(fn_def->metadata, meta_idx, ins_idx);

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
  }
  case AST_NODE_KIND_BUILTIN_ASSERT: {
    PG_ASSERT(1 == node.operands.len);
    MetadataIndex meta_idx = metadata_make(&fn_def->metadata, allocator);
    metadata_start_lifetime(fn_def->metadata, meta_idx,
                            (InstructionIndex){(u32)fn_def->instructions.len});

    {
      AstNode operand = PG_SLICE_AT(node.operands, 0);

      IrInstruction ins_cmp = {
          .kind = IR_INSTRUCTION_KIND_COMPARISON,
          .origin = node.origin,
          .meta_idx = meta_idx,
          .token_kind = LEX_TOKEN_KIND_EQUAL_EQUAL,
      };
      IrOperand cond =
          ir_emit_ast_node(operand, emitter, fn_def, errors, allocator);
      *PG_DYN_PUSH(&ins_cmp.operands, allocator) = cond;
      *PG_DYN_PUSH(&ins_cmp.operands, allocator) =
          (IrOperand){.kind = IR_OPERAND_KIND_NUMBER, .u.n64 = 0};
      *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins_cmp;
    }

    {
      IrInstruction ins_jump_if_false = {
          .kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
          .origin = node.origin,
      };
      IrOperand jump_target = {
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = emitter->label_program_epilog_die,
      };
      PG_ASSERT(jump_target.u.label.value.len);
      *PG_DYN_PUSH(&ins_jump_if_false.operands, allocator) = jump_target;

      *PG_DYN_PUSH(&ins_jump_if_false.operands, allocator) =
          (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};

      *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins_jump_if_false;
    }

    return (IrOperand){0};
  }

  case AST_NODE_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == node.operands.len);
    AstNode operand = PG_SLICE_AT(node.operands, 0);
    PG_ASSERT(AST_NODE_KIND_IDENTIFIER == operand.kind);

    IrOperand rhs =
        ir_emit_ast_node(operand, emitter, fn_def, errors, allocator);
    MetadataIndex meta_idx = metadata_make(&fn_def->metadata, allocator);
    metadata_start_lifetime(fn_def->metadata, meta_idx,
                            (InstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_ADDRESS_OF;
    ins.origin = node.origin;
    ins.meta_idx = meta_idx;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      InstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};
      metadata_extend_lifetime_on_use(fn_def->metadata, rhs.u.meta_idx,
                                      ins_idx);
    } else {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER,
          .origin = node.origin,
      };
      return (IrOperand){0};
    }

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
  }

  case AST_NODE_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == node.operands.len);
    IrOperand cond = ir_emit_ast_node(PG_SLICE_AT(node.operands, 0), emitter,
                                      fn_def, errors, allocator);
    // TODO: else.

    Label branch_if_cont_label = ir_emitter_next_label_name(emitter, allocator);
    Label branch_else_label = ir_emitter_next_label_name(emitter, allocator);

    IrInstruction ir_cond_jump = {
        .kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
        .origin = node.origin,
    };
    *PG_DYN_PUSH(&ir_cond_jump.operands, allocator) = (IrOperand){
        .kind = IR_OPERAND_KIND_LABEL,
        .u.label = branch_else_label,
    };
    *PG_DYN_PUSH(&ir_cond_jump.operands, allocator) = cond;
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ir_cond_jump;
    InstructionIndex ir_cond_jump_idx = {(u32)(fn_def->instructions.len - 1)};

    if (IR_OPERAND_KIND_VAR == cond.kind) {
      metadata_extend_lifetime_on_use(fn_def->metadata, cond.u.meta_idx,
                                      ir_cond_jump_idx);
    }

    // 'then' branch.
    {
      (void)ir_emit_ast_node(PG_SLICE_AT(node.operands, 1), emitter, fn_def,
                             errors, allocator);
      IrInstruction ir_jump = {
          .kind = IR_INSTRUCTION_KIND_JUMP,
          .origin = node.origin,
      };
      *PG_DYN_PUSH(&ir_jump.operands, allocator) = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = branch_if_cont_label,
      };
      *PG_DYN_PUSH(&fn_def->instructions, allocator) = ir_jump;
    }

    // 'else' branch.
    {
      IrInstruction ir_label_else = {
          .kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION,
          .origin = node.origin,
      };
      *PG_DYN_PUSH(&ir_label_else.operands, allocator) = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = branch_else_label,
      };
      *PG_DYN_PUSH(&fn_def->instructions, allocator) = ir_label_else;
      if (3 == node.operands.len) {
        (void)ir_emit_ast_node(PG_SLICE_AT(node.operands, 2), emitter, fn_def,
                               errors, allocator);
      }
    }
    IrInstruction ir_label_if_cont = {
        .kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION,
        .origin = node.origin,
    };
    *PG_DYN_PUSH(&ir_label_if_cont.operands, allocator) = (IrOperand){
        .kind = IR_OPERAND_KIND_LABEL,
        .u.label = branch_if_cont_label,
    };
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ir_label_if_cont;

    return (IrOperand){0};
  }

  default:
    PG_ASSERT(0);
  }
}

static void ir_emit_program(IrEmitter *emitter, ErrorDyn *errors,
                            PgAllocator *allocator) {
  // TODO: have parser record function names.
  emitter->label_program_epilog_die.value = PG_S("__builtin_die");
  emitter->label_program_epilog_exit.value = PG_S("__builtin_exit");

  for (u64 i = 0; i < emitter->parser.nodes.len) {
    (void)ir_emit_ast_node(emitter, &i, nullptr, errors, allocator);
  }
}

#if 0
static void irs_recompute_var_metadata(IrInstructionDyn instructions,
                                       MetadataDyn metadata) {
  for (u64 i = 0; i < metadata.len; i++) {
    Metadata *meta = PG_SLICE_AT_PTR(&metadata, i);
    meta->tombstone = true;
    meta->lifetime_end = meta->lifetime_start;
  }

  for (u64 i = 0; i < instructions.len; i++) {
    IrInstruction ins = PG_SLICE_AT(instructions, i);
    if (ins.tombstone) {
      continue;
    }

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_COMPARISON:
    case IR_INSTRUCTION_KIND_ADD:
    case IR_INSTRUCTION_KIND_LOAD:
    case IR_INSTRUCTION_KIND_SYSCALL:
    case IR_INSTRUCTION_KIND_ADDRESS_OF:
    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
      for (u64 j = 0; j < ins.operands.len; j++) {
        IrOperand val = PG_SLICE_AT(ins.operands, j);
        if (IR_OPERAND_KIND_VAR != val.kind) {
          continue;
        }

        Metadata *meta = ir_find_metadata_by_var_id(metadata, val.var.id);
        PG_ASSERT(meta);
        meta->lifetime_end = (IrInstructionIndex){(u32)i};
        meta->tombstone = false;
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
#endif

#if 0
[[nodiscard]]
static bool irs_optimize_remove_unused_vars(IrInstructionDyn *instructions,
                                            MetadataDyn *metadata) {
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

    Metadata *meta = ir_find_metadata_by_var_id(*metadata, ins->res_var.id);
    PG_ASSERT(meta);
    if (meta->tombstone) {
      goto do_rm;
    }

    PG_ASSERT(meta->lifetime_start.value <= meta->lifetime_end.value);
    u64 duration = meta->lifetime_end.value - meta->lifetime_start.value;
    if (duration > 0) {
      // Used: no-op.
      continue;
    }

  do_rm:

    meta->tombstone = true;

    // Possible side-effects: keep this IR but erase the variable.
    if (IR_INSTRUCTION_KIND_SYSCALL == ins->kind) {
      ins->res_var.id.value = 0;
      continue;
    }

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
                                           MetadataDyn *metadata) {
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
    Metadata *meta = ir_find_metadata_by_var_id(*metadata, ins->res_var.id);
    PG_ASSERT(!meta->tombstone);
    meta->tombstone = true;
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
    IrInstructionDyn *instructions, MetadataDyn *metadata) {
  bool changed = false;
  for (u64 i = 0; i < instructions->len; i++) {
    IrInstruction *ins = PG_SLICE_AT_PTR(instructions, i);
    if (ins->tombstone) {
      continue;
    }

    if (!(IR_INSTRUCTION_KIND_LOAD == ins->kind ||
          IR_INSTRUCTION_KIND_ADD == ins->kind ||
          IR_INSTRUCTION_KIND_SYSCALL == ins->kind ||
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

      Metadata *meta = ir_find_metadata_by_var_id(*metadata, var.id);
      PG_ASSERT(meta);

      IrInstructionIndex var_def_ins_idx = meta->lifetime_start;
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

static void ir_optimize(IrInstructionDyn *instructions, MetadataDyn *metadata,
                        bool verbose) {
  bool changed = false;

  u64 optimization_rounds = 0;
  do {
    changed = false;
    changed |= irs_optimize_remove_unused_vars(instructions, metadata);
    if (changed) {
      irs_recompute_var_metadata(*instructions, *metadata);
    }

    changed |=
        irs_optimize_remove_trivially_aliased_vars(instructions, metadata);
    if (changed) {
      irs_recompute_var_metadata(*instructions, *metadata);
    }

    changed |= irs_optimize_replace_immediate_vars_by_immediate_value(
        instructions, metadata);
    if (changed) {
      irs_recompute_var_metadata(*instructions, *metadata);
    }

    changed |= irs_optimize_fold_constants(instructions);
    if (changed) {
      irs_recompute_var_metadata(*instructions, *metadata);
    }

    changed |=
        irs_optimize_remove_trivial_falsy_or_truthy_branches(instructions);
    if (changed) {
      irs_recompute_var_metadata(*instructions, *metadata);
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
#endif

static void ir_print_operand(IrOperand op, MetadataDyn metadata) {
  switch (op.kind) {
  case IR_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case IR_OPERAND_KIND_NUMBER:
    printf("%" PRIu64, op.u.n64);
    break;
  case IR_OPERAND_KIND_VAR: {
    Metadata meta = PG_SLICE_AT(metadata, op.u.meta_idx.value);
    ir_print_var(meta);
  } break;
  case IR_OPERAND_KIND_LABEL:
    PG_ASSERT(op.u.label.value.len);

    printf("%.*s", (i32)op.u.label.value.len, op.u.label.value.data);
    break;
  default:
    PG_ASSERT(0);
  }
}

#if 0
static void ir_emitter_trim_tombstone_items(IrEmitter *emitter) {
  for (u64 i = 0; i < emitter->instructions.len;) {
    IrInstruction ins = PG_SLICE_AT(emitter->instructions, i);
    if (ins.tombstone) {
      PG_DYN_REMOVE_AT(&emitter->instructions, i);
      continue;
    }
    i++;
  }

  for (u64 i = 0; i < fn_def->metadata.len;) {
    Metadata meta = PG_SLICE_AT(fn_def->metadata, i);
    if (meta.tombstone) {
      PG_DYN_REMOVE_AT(&fn_def->metadata, i);
      continue;
    }
    i++;
  }
}
#endif
