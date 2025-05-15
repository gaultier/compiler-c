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
  IR_INSTRUCTION_KIND_COMPARISON,
  IR_INSTRUCTION_KIND_SYSCALL,
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
  LexTokenKind token_kind;
  Origin origin;
  // Result var. Not always present.
  IrVar res_var;

  // When optimizing, IRs are not directly removed but instead tombstoned.
  bool tombstone;
} IrInstruction;
PG_SLICE(IrInstruction) IrInstructionSlice;
PG_DYN(IrInstruction) IrInstructionDyn;

typedef enum {
  LIR_VIRT_REG_CONSTRAINT_NONE,
  LIR_VIRT_REG_CONSTRAINT_CONDITION_FLAGS,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL_NUM,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL0,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL1,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL2,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL3,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL4,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL5,
  LIR_VIRT_REG_CONSTRAINT_SYSCALL_RET,
} LirVirtualRegisterConstraint;

typedef struct {
  u32 value;
  LirVirtualRegisterConstraint constraint;
  bool addressable;
} VirtualRegister;
PG_SLICE(VirtualRegister) VirtualRegisterSlice;
PG_DYN(VirtualRegister) VirtualRegisterDyn;

typedef struct {
  u32 value;
} Register;
PG_SLICE(Register) RegisterSlice;
PG_DYN(Register) RegisterDyn;

typedef enum {
  MEMORY_LOCATION_KIND_NONE,
  MEMORY_LOCATION_KIND_REGISTER,
  MEMORY_LOCATION_KIND_STACK,
  MEMORY_LOCATION_KIND_STATUS_REGISTER,
#if 0
  MEMORY_LOCATION_KIND_MEMORY,
#endif
} MemoryLocationKind;

typedef struct {
  MemoryLocationKind kind;
  union {
    Register reg;
    i32 base_pointer_offset;
#if 0
     u64 memory_address;
#endif
  };
} MemoryLocation;
PG_SLICE(MemoryLocation) MemoryLocationSlice;
PG_DYN(MemoryLocation) MemoryLocationDyn;

typedef struct {
  u32 value;
} MemoryLocationIndex;

typedef struct {
  u32 value;
} VirtualRegisterIndex;
typedef struct {
  IrVar var;
#if 0
  IrInstructionIndex lifetime_start, lifetime_end;
#endif
  VirtualRegister virtual_register;
  MemoryLocation memory_location;
#if 0
  bool tombstone;
#endif
} IrMetadata;
PG_DYN(IrMetadata) IrMetadataDyn;

typedef struct {
  IrInstructionDyn instructions;
  // Gets incremented.
  IrLabelId label_id;
  // Gets incremented.
  IrVarId var_id;

  IrMetadataDyn metadata;

  IrLabelId label_program_epilog_die;
  IrLabelId label_program_epilog_exit;
} IrEmitter;

[[nodiscard]]
static IrLabelId ir_emitter_next_label_id(IrEmitter *emitter) {
  IrLabelId id = {.value = ++emitter->label_id.value};
  return id;
}

[[nodiscard]]
static IrMetadata ir_make_metadata(IrMetadataDyn *metadata, PgString identifier,
                                   PgAllocator *allocator) {
  IrMetadata res = {0};
#if 0
  res.lifetime_start = ins_idx;
  res.lifetime_end = ins_idx;
#endif
  res.var.id.value = (u32)metadata->len;
  res.var.identifier = identifier;
  res.virtual_register.value = res.var.id.value;

  *PG_DYN_PUSH(metadata, allocator) = res;

  return res;
}

static IrMetadata *ir_find_metadata_by_var_id(IrMetadataDyn metadata,
                                              IrVarId var_id) {
  if (0 == var_id.value) {
    return nullptr;
  }

  for (u64 i = 0; i < metadata.len; i++) {
    IrMetadata *meta = PG_SLICE_AT_PTR(&metadata, i);
    if (meta->var.id.value == var_id.value) {
      return meta;
    }
  }
  return nullptr;
}

static IrMetadata *ir_find_metadata_by_virtual_register(
    IrMetadataDyn metadata, VirtualRegisterIndex virtual_register_idx) {
  for (u64 i = 0; i < metadata.len; i++) {
    IrMetadata *meta = PG_SLICE_AT_PTR(&metadata, i);
    if (meta->virtual_register.value == virtual_register_idx.value) {
      return meta;
    }
  }
  return nullptr;
}

static IrMetadata *ir_find_metadata_by_identifier(IrMetadataDyn metadata,
                                                  PgString identifier) {
  for (u64 i = 0; i < metadata.len; i++) {
    IrMetadata *meta = PG_SLICE_AT_PTR(&metadata, i);
    if (pg_string_eq(meta->var.identifier, identifier)) {
      return meta;
    }
  }
  return nullptr;
}

#if 0
static void ir_var_extend_lifetime_on_use(IrMetadataDyn metadata, IrVar var,
                                          IrInstructionIndex ins_idx) {
  IrMetadata *meta = ir_find_metadata_by_var_id(metadata, var.id);
  PG_ASSERT(meta);
  meta->lifetime_end = ins_idx;

  // TODO: Variable pointed to needs to live at least as long as the pointer to
  // it.
  // TODO: If there are multiple aliases to the same pointer, all aliases
  // should have their meta extended to this point!
  // TODO: Dataflow.
}
#endif

[[nodiscard]]
static IrOperand ir_emit_ast_node(AstNode node, IrEmitter *emitter,
                                  ErrorDyn *errors, PgAllocator *allocator) {
  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64: {
    IrMetadata meta = ir_make_metadata(&emitter->metadata, PG_S(""), allocator);

    IrInstruction ins = {
        .kind = IR_INSTRUCTION_KIND_LOAD,
        .origin = node.origin,
        .res_var.id = meta.var.id,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = (IrOperand){
        .kind = IR_OPERAND_KIND_U64,
        .n64 = node.n64,
    };

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
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
    IrOperand lhs = ir_emit_ast_node(PG_SLICE_AT(node.operands, 0), emitter,
                                     errors, allocator);
    IrOperand rhs = ir_emit_ast_node(PG_SLICE_AT(node.operands, 1), emitter,
                                     errors, allocator);

    IrMetadata meta = ir_make_metadata(&emitter->metadata, PG_S(""), allocator);

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_ADD;
    ins.origin = node.origin;
    ins.res_var.id = meta.var.id;

    *PG_DYN_PUSH(&ins.operands, allocator) = lhs;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
#if 0
    IrInstructionIndex ins_idx = meta.lifetime_start;

    if (IR_OPERAND_KIND_VAR == lhs.kind) {
      ir_var_extend_lifetime_on_use(emitter->metadata, lhs.var, ins_idx);
    }
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_use(emitter->metadata, rhs.var, ins_idx);
    }
#endif

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }

  case AST_NODE_KIND_COMPARISON: {
    PG_ASSERT(2 == node.operands.len);
    IrOperand lhs = ir_emit_ast_node(PG_SLICE_AT(node.operands, 0), emitter,
                                     errors, allocator);
    IrOperand rhs = ir_emit_ast_node(PG_SLICE_AT(node.operands, 1), emitter,
                                     errors, allocator);
    PG_ASSERT(LEX_TOKEN_KIND_EQUAL_EQUAL == node.token_kind);

    IrMetadata meta = ir_make_metadata(&emitter->metadata, PG_S(""), allocator);

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_COMPARISON;
    ins.origin = node.origin;
    ins.token_kind = node.token_kind;
    ins.res_var.id = meta.var.id;

    *PG_DYN_PUSH(&ins.operands, allocator) = lhs;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;
#if 0
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};

    if (IR_OPERAND_KIND_VAR == lhs.kind) {
      ir_var_extend_lifetime_on_use(emitter->metadata, lhs.var, ins_idx);
    }
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_use(emitter->metadata, rhs.var, ins_idx);
    }
#endif

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }

  case AST_NODE_KIND_SYSCALL: {
    IrOperandDyn operands = {0};
    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      IrOperand operand = ir_emit_ast_node(child, emitter, errors, allocator);

      *PG_DYN_PUSH(&operands, allocator) = operand;
    }

    IrMetadata meta = ir_make_metadata(&emitter->metadata, PG_S(""), allocator);

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_SYSCALL;
    ins.origin = node.origin;
    ins.operands = operands;
    ins.res_var.id = meta.var.id;
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

#if 0
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};
    for (u64 i = 0; i < node.operands.len; i++) {
      IrOperand val = PG_SLICE_AT(ins.operands, i);
      if (IR_OPERAND_KIND_VAR == val.kind) {
        IrVar var = val.var;
        ir_var_extend_lifetime_on_use(emitter->metadata, var, ins_idx);
      }
    }
#endif

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }
  case AST_NODE_KIND_BLOCK: {
    if (!pg_string_is_empty(node.identifier)) {
      // FIXME: The actual label from the source gets lost.

      IrLabelId label_id = ir_emitter_next_label_id(emitter);

      IrInstruction ir_label = {
          .kind = IR_INSTRUCTION_KIND_LABEL,
          .origin = node.origin,
      };
      *PG_DYN_PUSH(&ir_label.operands, allocator) = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .label = label_id,
      };
      *PG_DYN_PUSH(&emitter->instructions, allocator) = ir_label;

      if (pg_string_eq(node.identifier, PG_S("__builtin_exit"))) {
        emitter->label_program_epilog_exit = label_id;
      } else if (pg_string_eq(node.identifier, PG_S("__builtin_die"))) {
        emitter->label_program_epilog_die = label_id;
      }
    }

    for (u64 i = 0; i < node.operands.len; i++) {
      AstNode child = PG_SLICE_AT(node.operands, i);
      (void)ir_emit_ast_node(child, emitter, errors, allocator);
    }
    // TODO: Label?
    return (IrOperand){0};
  }
  case AST_NODE_KIND_VAR_DECL: {
    PG_ASSERT(1 == node.operands.len);
    PG_ASSERT(!pg_string_is_empty(node.identifier));

    AstNode rhs_node = PG_SLICE_AT(node.operands, 0);
    IrOperand rhs = ir_emit_ast_node(rhs_node, emitter, errors, allocator);

    IrMetadata meta =
        ir_make_metadata(&emitter->metadata, node.identifier, allocator);

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_LOAD;
    ins.origin = node.origin;
    ins.res_var.id = meta.var.id;
    ins.res_var.identifier = node.identifier;

    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

#if 0
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_var_extend_lifetime_on_use(emitter->metadata, rhs.var, ins_idx);
      PG_ASSERT(ir_find_metadata_by_var_id(emitter->metadata, rhs.var.id));
    }
#endif

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }

  case AST_NODE_KIND_IDENTIFIER: {
    IrMetadata *meta =
        ir_find_metadata_by_identifier(emitter->metadata, node.identifier);

    if (!meta) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_UNDEFINED_VAR,
          .origin = node.origin,
      };
      return (IrOperand){0};
    }

#if 0
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};
    ir_var_extend_lifetime_on_use(emitter->metadata, meta->var, ins_idx);
#endif

    return (IrOperand){
        .kind = IR_OPERAND_KIND_VAR,
        .var = meta->var,
    };
  }
  case AST_NODE_KIND_BUILTIN_ASSERT: {
    PG_ASSERT(1 == node.operands.len);
    AstNode operand = PG_SLICE_AT(node.operands, 0);

    IrInstruction ins = {
        .kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
        .origin = node.origin,
    };

    IrOperand cond = ir_emit_ast_node(operand, emitter, errors, allocator);
    *PG_DYN_PUSH(&ins.operands, allocator) = cond;

    IrOperand jump_target = {
        .kind = IR_OPERAND_KIND_LABEL,
        .label = emitter->label_program_epilog_die,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = jump_target;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

    return (IrOperand){0};
  }

  case AST_NODE_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == node.operands.len);
    AstNode operand = PG_SLICE_AT(node.operands, 0);
    PG_ASSERT(AST_NODE_KIND_IDENTIFIER == operand.kind);

    IrOperand rhs = ir_emit_ast_node(operand, emitter, errors, allocator);
    IrMetadata meta = ir_make_metadata(&emitter->metadata, PG_S(""), allocator);
    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_ADDRESS_OF;
    ins.origin = node.origin;
    ins.res_var.id = meta.var.id;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&emitter->instructions, allocator) = ins;

    if (IR_OPERAND_KIND_VAR == rhs.kind) {
#if 0
    IrInstructionIndex ins_idx = {(u32)(emitter->instructions.len - 1)};
      ir_var_extend_lifetime_on_use(emitter->metadata, rhs.var, ins_idx);
#endif
    } else {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_ADDRESS_OF_RHS_NOT_IDENTIFIER,
          .origin = node.origin,
      };
      return (IrOperand){0};
    }

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .var = ins.res_var};
  }

  case AST_NODE_KIND_IF: {
    PG_ASSERT(2 == node.operands.len);
    IrOperand cond = ir_emit_ast_node(PG_SLICE_AT(node.operands, 0), emitter,
                                      errors, allocator);
    // TODO: else.

    IrInstruction ir_cond_jump = {
        .kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
        .origin = node.origin,
    };
    *PG_DYN_PUSH(&ir_cond_jump.operands, allocator) = cond;
    *PG_DYN_PUSH(&emitter->instructions, allocator) = ir_cond_jump;
    IrInstructionIndex ir_cond_jump_idx = {
        (u32)(emitter->instructions.len - 1)};

#if 0
    if (IR_OPERAND_KIND_VAR == cond.kind) {
      ir_var_extend_lifetime_on_use(emitter->metadata, cond.var,
                                    ir_cond_jump_idx);
    }
#endif

    IrLabelId branch_if_cont_label = ir_emitter_next_label_id(emitter);
    IrLabelId branch_else_label = ir_emitter_next_label_id(emitter);

    // 'then' branch.
    {
      (void)ir_emit_ast_node(PG_SLICE_AT(node.operands, 1), emitter, errors,
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
        (void)ir_emit_ast_node(PG_SLICE_AT(node.operands, 2), emitter, errors,
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

static void ir_emit_program(IrEmitter *emitter, AstNode node, ErrorDyn *errors,
                            PgAllocator *allocator) {
  PG_ASSERT(AST_NODE_KIND_BLOCK == node.kind);

  (void)ir_emit_ast_node(node, emitter, errors, allocator);
}

#if 0
static void irs_recompute_var_metadata(IrInstructionDyn instructions,
                                       IrMetadataDyn metadata) {
  for (u64 i = 0; i < metadata.len; i++) {
    IrMetadata *meta = PG_SLICE_AT_PTR(&metadata, i);
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

        IrMetadata *meta = ir_find_metadata_by_var_id(metadata, val.var.id);
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
                                            IrMetadataDyn *metadata) {
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

    IrMetadata *meta = ir_find_metadata_by_var_id(*metadata, ins->res_var.id);
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
                                           IrMetadataDyn *metadata) {
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
    IrMetadata *meta = ir_find_metadata_by_var_id(*metadata, ins->res_var.id);
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
    IrInstructionDyn *instructions, IrMetadataDyn *metadata) {
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

      IrMetadata *meta = ir_find_metadata_by_var_id(*metadata, var.id);
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

static void ir_optimize(IrInstructionDyn *instructions, IrMetadataDyn *metadata,
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

static void ir_emitter_print_meta(u64 i, IrMetadata meta) {
#if 0
  if (meta.tombstone) {
    printf("\x1B[9m"); // Strikethrough.
  }
#endif

  printf("[%lu] ", i);
  ir_print_var(meta.var);
#if 0
  printf(" meta: [%u:%u]", meta.lifetime_start.value, meta.lifetime_end.value);
#endif

  printf("\n");
#if 0
  if (meta.tombstone) {
    printf("\x1B[0m"); // Strikethrough.
  }
#endif
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

    IrMetadata *meta =
        ir_find_metadata_by_var_id(emitter.metadata, ins.res_var.id);
    PG_ASSERT(meta);
    printf(" // ");
    ir_emitter_print_meta(i, *meta);
  } break;
  case IR_INSTRUCTION_KIND_COMPARISON: {
    PG_ASSERT(2 == ins.operands.len);
    PG_ASSERT(0 != ins.res_var.id.value);

    ir_print_var(ins.res_var);
    printf(" := ");
    ir_print_operand(PG_SLICE_AT(ins.operands, 0));
    printf(" %s ", LEX_TOKEN_KIND_EQUAL_EQUAL == ins.token_kind ? "==" : "!=");
    ir_print_operand(PG_SLICE_AT(ins.operands, 1));

    IrMetadata *meta =
        ir_find_metadata_by_var_id(emitter.metadata, ins.res_var.id);
    PG_ASSERT(meta);
    printf(" // ");
    ir_emitter_print_meta(i, *meta);
  } break;
  case IR_INSTRUCTION_KIND_LOAD: {
    PG_ASSERT(1 == ins.operands.len);
    PG_ASSERT(0 != ins.res_var.id.value);

    IrOperand rhs = PG_SLICE_AT(ins.operands, 0);
    ir_print_var(ins.res_var);
    printf(" := ");
    ir_print_operand(rhs);

    IrMetadata *meta =
        ir_find_metadata_by_var_id(emitter.metadata, ins.res_var.id);
    PG_ASSERT(meta);
    printf(" // ");
    ir_emitter_print_meta(i, *meta);
  } break;
  case IR_INSTRUCTION_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ins.operands.len);
    PG_ASSERT(0 != ins.res_var.id.value);

    ir_print_var(ins.res_var);
    printf(" := &");
    ir_print_operand(PG_SLICE_AT(ins.operands, 0));

    IrMetadata *meta =
        ir_find_metadata_by_var_id(emitter.metadata, ins.res_var.id);
    printf(" // ");
    ir_emitter_print_meta(i, *meta);
  } break;
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
      IrMetadata *meta =
          ir_find_metadata_by_var_id(emitter.metadata, ins.res_var.id);
      PG_ASSERT(meta);
      printf(" // ");
      ir_emitter_print_meta(i, *meta);
    }
    printf("\n");
  } break;
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

static void ir_emitter_print_metadata(IrMetadataDyn metadata) {
  for (u64 i = 0; i < metadata.len; i++) {
    IrMetadata meta = PG_SLICE_AT(metadata, i);
    ir_emitter_print_meta(i, meta);
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

  for (u64 i = 0; i < emitter->metadata.len;) {
    IrMetadata meta = PG_SLICE_AT(emitter->metadata, i);
    if (meta.tombstone) {
      PG_DYN_REMOVE_AT(&emitter->metadata, i);
      continue;
    }
    i++;
  }
}
#endif
