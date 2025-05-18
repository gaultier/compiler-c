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

typedef struct {
  u32 value;
} IrInstructionIndex;

typedef enum {
  IR_OPERAND_KIND_NONE,
  IR_OPERAND_KIND_U64,
  IR_OPERAND_KIND_VAR,
  IR_OPERAND_KIND_LABEL,
} IrOperandKind;

// Unresolved.
typedef struct {
  PgString value;
} Label;

typedef struct IrOperand IrOperand;
PG_SLICE(IrOperand) IrOperandSlice;
PG_DYN(IrOperand) IrOperandDyn;

typedef struct {
  u32 value;
} MetadataIndex;

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
  IrOperandDyn operands;
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

typedef enum {
  VREG_CONSTRAINT_NONE,
  VREG_CONSTRAINT_CONDITION_FLAGS,
  VREG_CONSTRAINT_SYSCALL_NUM,
  VREG_CONSTRAINT_SYSCALL0,
  VREG_CONSTRAINT_SYSCALL1,
  VREG_CONSTRAINT_SYSCALL2,
  VREG_CONSTRAINT_SYSCALL3,
  VREG_CONSTRAINT_SYSCALL4,
  VREG_CONSTRAINT_SYSCALL5,
  VREG_CONSTRAINT_SYSCALL_RET,
} VirtualRegisterConstraint;

typedef struct {
  u32 value;
  VirtualRegisterConstraint constraint;
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
  } u;
} MemoryLocation;
PG_SLICE(MemoryLocation) MemoryLocationSlice;
PG_DYN(MemoryLocation) MemoryLocationDyn;

typedef struct {
  IrInstructionIndex lifetime_start, lifetime_end;
  VirtualRegister virtual_register;
  MemoryLocation memory_location;
  PgString identifier;
#if 0
  bool tombstone;
#endif
} Metadata;
PG_DYN(Metadata) MetadataDyn;

typedef struct {
  PgString name;
  AstNodeFlag flags;

  // TODO: Arguments.

  IrInstructionDyn instructions;
  MetadataDyn metadata;
} IrFnDefinition;
PG_DYN(IrFnDefinition) IrFnDefinitionDyn;

typedef struct {
  IrFnDefinitionDyn fn_definitions;

  // Gets incremented.
  u32 label_id;

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

[[nodiscard]] static MetadataIndex ir_metadata_last_idx(MetadataDyn metadata) {
  PG_ASSERT(metadata.len > 0);
  return (MetadataIndex){(u32)metadata.len - 1};
}

[[nodiscard]]
static MetadataIndex ir_make_metadata(MetadataDyn *metadata,
                                      PgAllocator *allocator) {
  Metadata res = {0};
  res.virtual_register.value = (u32)metadata->len;

  *PG_DYN_PUSH(metadata, allocator) = res;

  return ir_metadata_last_idx(*metadata);
}

static void ir_metadata_start_lifetime(MetadataDyn metadata,
                                       MetadataIndex meta_idx,
                                       IrInstructionIndex ins_idx) {
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_start = ins_idx;
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_end = ins_idx;
}

[[nodiscard]]
static MetadataIndex ir_metadata_ptr_to_idx(MetadataDyn metadata,
                                            Metadata *meta) {
  return (MetadataIndex){(u32)(meta - metadata.data)};
}

[[nodiscard]]
static Metadata *ir_find_metadata_by_identifier(MetadataDyn metadata,
                                                PgString identifier) {
  for (u64 i = 0; i < metadata.len; i++) {
    Metadata *meta = PG_SLICE_AT_PTR(&metadata, i);
    if (pg_string_eq(meta->identifier, identifier)) {
      return meta;
    }
  }
  return nullptr;
}

static void ir_metadata_extend_lifetime_on_use(MetadataDyn metadata,
                                               MetadataIndex meta_idx,
                                               IrInstructionIndex ins_idx) {
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_end = ins_idx;

  // TODO: Variable pointed to needs to live at least as long as the pointer to
  // it.
  // TODO: If there are multiple aliases to the same pointer, all aliases
  // should have their meta extended to this point!
  // TODO: Dataflow.
}

[[nodiscard]]
static IrOperand ir_emit_ast_node(AstNode node, IrEmitter *emitter,
                                  IrFnDefinition *fn_def, ErrorDyn *errors,
                                  PgAllocator *allocator) {
  switch (node.kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64: {
    MetadataIndex meta_idx = ir_make_metadata(&fn_def->metadata, allocator);
    ir_metadata_start_lifetime(
        fn_def->metadata, meta_idx,
        (IrInstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {
        .kind = IR_INSTRUCTION_KIND_LOAD,
        .origin = node.origin,
        .meta_idx = meta_idx,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = (IrOperand){
        .kind = IR_OPERAND_KIND_U64,
        .u.n64 = node.n64,
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

    MetadataIndex meta_idx = ir_make_metadata(&fn_def->metadata, allocator);
    ir_metadata_start_lifetime(
        fn_def->metadata, meta_idx,
        (IrInstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_ADD;
    ins.origin = node.origin;
    ins.meta_idx = meta_idx;

    *PG_DYN_PUSH(&ins.operands, allocator) = lhs;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;
    IrInstructionIndex ins_idx =
        PG_SLICE_AT(fn_def->metadata, meta_idx.value).lifetime_start;

    if (IR_OPERAND_KIND_VAR == lhs.kind) {
      ir_metadata_extend_lifetime_on_use(fn_def->metadata, lhs.u.meta_idx,
                                         ins_idx);
    }
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_metadata_extend_lifetime_on_use(fn_def->metadata, rhs.u.meta_idx,
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

    MetadataIndex meta_idx = ir_make_metadata(&fn_def->metadata, allocator);
    ir_metadata_start_lifetime(
        fn_def->metadata, meta_idx,
        (IrInstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_COMPARISON;
    ins.origin = node.origin;
    ins.token_kind = node.token_kind;
    ins.meta_idx = meta_idx;

    *PG_DYN_PUSH(&ins.operands, allocator) = lhs;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

    IrInstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};

    if (IR_OPERAND_KIND_VAR == lhs.kind) {
      ir_metadata_extend_lifetime_on_use(fn_def->metadata, lhs.u.meta_idx,
                                         ins_idx);
    }
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_metadata_extend_lifetime_on_use(fn_def->metadata, rhs.u.meta_idx,
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

    MetadataIndex meta_idx = ir_make_metadata(&fn_def->metadata, allocator);
    ir_metadata_start_lifetime(
        fn_def->metadata, meta_idx,
        (IrInstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_SYSCALL;
    ins.origin = node.origin;
    ins.operands = operands;
    ins.meta_idx = meta_idx;
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

    IrInstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};
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
    if (!pg_string_is_empty(node.identifier)) {

      Label label = {.value = node.identifier};

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
    PG_ASSERT(!pg_string_is_empty(node.identifier));

    PG_ASSERT(!fn_def);
    IrFnDefinition fn_def_real = (IrFnDefinition){
        .name = node.identifier,
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
    PG_ASSERT(!pg_string_is_empty(node.identifier));

    AstNode rhs_node = PG_SLICE_AT(node.operands, 0);
    IrOperand rhs =
        ir_emit_ast_node(rhs_node, emitter, fn_def, errors, allocator);

    MetadataIndex meta_idx = ir_make_metadata(&fn_def->metadata, allocator);
    PG_SLICE_AT(fn_def->metadata, meta_idx.value).identifier = node.identifier;
    ir_metadata_start_lifetime(
        fn_def->metadata, meta_idx,
        (IrInstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_LOAD;
    ins.origin = node.origin;
    ins.meta_idx = meta_idx;

    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

    IrInstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};
    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      ir_metadata_extend_lifetime_on_use(fn_def->metadata, rhs.u.meta_idx,
                                         ins_idx);
    }

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
  }

  case AST_NODE_KIND_IDENTIFIER: {
    Metadata *meta =
        ir_find_metadata_by_identifier(fn_def->metadata, node.identifier);

    if (!meta) {
      *PG_DYN_PUSH(errors, allocator) = (Error){
          .kind = ERROR_KIND_UNDEFINED_VAR,
          .origin = node.origin,
      };
      return (IrOperand){0};
    }

    MetadataIndex meta_idx = ir_metadata_ptr_to_idx(fn_def->metadata, meta);

    IrInstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};
    ir_metadata_extend_lifetime_on_use(fn_def->metadata, meta_idx, ins_idx);

    return (IrOperand){.kind = IR_OPERAND_KIND_VAR, .u.meta_idx = meta_idx};
  }
  case AST_NODE_KIND_BUILTIN_ASSERT: {
    PG_ASSERT(1 == node.operands.len);
    MetadataIndex meta_idx = ir_make_metadata(&fn_def->metadata, allocator);
    ir_metadata_start_lifetime(
        fn_def->metadata, meta_idx,
        (IrInstructionIndex){(u32)fn_def->instructions.len});

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
          (IrOperand){.kind = IR_OPERAND_KIND_U64, .u.n64 = 0};
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
    MetadataIndex meta_idx = ir_make_metadata(&fn_def->metadata, allocator);
    ir_metadata_start_lifetime(
        fn_def->metadata, meta_idx,
        (IrInstructionIndex){(u32)fn_def->instructions.len});

    IrInstruction ins = {0};
    ins.kind = IR_INSTRUCTION_KIND_ADDRESS_OF;
    ins.origin = node.origin;
    ins.meta_idx = meta_idx;
    *PG_DYN_PUSH(&ins.operands, allocator) = rhs;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

    if (IR_OPERAND_KIND_VAR == rhs.kind) {
      IrInstructionIndex ins_idx = {(u32)(fn_def->instructions.len - 1)};
      ir_metadata_extend_lifetime_on_use(fn_def->metadata, rhs.u.meta_idx,
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

  case AST_NODE_KIND_IF: {
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
    IrInstructionIndex ir_cond_jump_idx = {(u32)(fn_def->instructions.len - 1)};

    if (IR_OPERAND_KIND_VAR == cond.kind) {
      ir_metadata_extend_lifetime_on_use(fn_def->metadata, cond.u.meta_idx,
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

static void ir_emit_program(IrEmitter *emitter, AstNode node, ErrorDyn *errors,
                            PgAllocator *allocator) {
  PG_ASSERT(AST_NODE_KIND_BLOCK == node.kind);

  emitter->label_program_epilog_die.value = PG_S("__builtin_die");
  emitter->label_program_epilog_exit.value = PG_S("__builtin_exit");

  (void)ir_emit_ast_node(node, emitter, nullptr, errors, allocator);
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

static void ir_print_var(Metadata meta) {
  if (0 == meta.virtual_register.value) {
    return;
  }

  if (!pg_string_is_empty(meta.identifier)) {
    printf("%.*s%%%" PRIu32, (i32)meta.identifier.len, meta.identifier.data,
           meta.virtual_register.value);
  } else {
    printf("%%%" PRIu32, meta.virtual_register.value);
  }
}

static void ir_print_operand(IrOperand op, MetadataDyn metadata) {
  switch (op.kind) {
  case IR_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case IR_OPERAND_KIND_U64:
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

[[nodiscard]]
static char *
lir_register_constraint_to_cstr(VirtualRegisterConstraint constraint) {
  switch (constraint) {
  case VREG_CONSTRAINT_NONE:
    return "NONE";
  case VREG_CONSTRAINT_CONDITION_FLAGS:
    return "CONDITION_FLAGS";
  case VREG_CONSTRAINT_SYSCALL_NUM:
    return "SYSCALL_NUM";
  case VREG_CONSTRAINT_SYSCALL0:
    return "SYSCALL0";
  case VREG_CONSTRAINT_SYSCALL1:
    return "SYSCALL1";
  case VREG_CONSTRAINT_SYSCALL2:
    return "SYSCALL2";
  case VREG_CONSTRAINT_SYSCALL3:
    return "SYSCALL3";
  case VREG_CONSTRAINT_SYSCALL4:
    return "SYSCALL4";
  case VREG_CONSTRAINT_SYSCALL5:
    return "SYSCALL5";
  case VREG_CONSTRAINT_SYSCALL_RET:
    return "SYSCALL_RET";

  default:
    PG_ASSERT(0);
  }
}

static void metadata_print_meta(Metadata meta) {
#if 0
  if (meta.tombstone) {
    printf("\x1B[9m"); // Strikethrough.
  }
#endif

  printf("var=");
  ir_print_var(meta);
  printf(" lifetime=[%u:%u]", meta.lifetime_start.value,
         meta.lifetime_end.value);

  if (meta.virtual_register.value) {
    printf(" vreg=v%u{constraint=%s, addressable=%s}",
           meta.virtual_register.value,
           lir_register_constraint_to_cstr(meta.virtual_register.constraint),
           meta.virtual_register.addressable ? "true" : "false");
  }

  if (MEMORY_LOCATION_KIND_NONE != meta.memory_location.kind) {
    printf(" mem_loc=");

    switch (meta.memory_location.kind) {
    case MEMORY_LOCATION_KIND_REGISTER:
    case MEMORY_LOCATION_KIND_STATUS_REGISTER:
      printf("reg(todo)");
      // TODO
#if 0
      amd64_print_register(meta.memory_location.reg);
#endif
      break;
    case MEMORY_LOCATION_KIND_STACK: {
      printf("[sp");
      i32 offset = meta.memory_location.u.base_pointer_offset;
      printf("-%" PRIi32 "]", offset);
    } break;
#if 0
    case MEMORY_LOCATION_KIND_MEMORY:
      printf("%#lx", loc.memory_address);
      break;
#endif
    case MEMORY_LOCATION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

#if 0
  if (meta.tombstone) {
    printf("\x1B[0m"); // Strikethrough.
  }
#endif
}

static void metadata_print(MetadataDyn metadata) {
  for (u64 i = 0; i < metadata.len; i++) {
    Metadata meta = PG_SLICE_AT(metadata, i);
    printf("[%lu] ", i);
    metadata_print_meta(meta);
    printf("\n");
  }
}
static void ir_emitter_print_fn_definition(IrFnDefinition fn_def) {
  PG_ASSERT(fn_def.name.len);

  printf("fn %.*s() {\n", (i32)fn_def.name.len, fn_def.name.data);

  for (u64 i = 0; i < fn_def.instructions.len; i++) {
    IrInstruction ins = PG_SLICE_AT(fn_def.instructions, i);

#if 0
  if (ins.tombstone) {
    printf("\x1B[9m"); // Strikethrough.
  }
#endif

    if (IR_INSTRUCTION_KIND_LABEL_DEFINITION == ins.kind) {
      printf("\n");
    }

    printf("[%lu] ", i);
    origin_print(ins.origin);
    printf(": ");

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_NONE:
      PG_ASSERT(0);
    case IR_INSTRUCTION_KIND_ADD: {
      PG_ASSERT(2 == ins.operands.len);
      PG_ASSERT(0 != ins.meta_idx.value);
      Metadata meta = PG_SLICE_AT(fn_def.metadata, ins.meta_idx.value);
      ir_print_var(meta);
      printf(" := ");
      ir_print_operand(PG_SLICE_AT(ins.operands, 0), fn_def.metadata);
      printf(" + ");
      ir_print_operand(PG_SLICE_AT(ins.operands, 1), fn_def.metadata);

      printf(" // ");
      metadata_print_meta(meta);
    } break;
    case IR_INSTRUCTION_KIND_COMPARISON: {
      PG_ASSERT(2 == ins.operands.len);
      PG_ASSERT(0 != ins.meta_idx.value);

      Metadata meta = PG_SLICE_AT(fn_def.metadata, ins.meta_idx.value);

      ir_print_var(meta);
      printf(" := ");
      ir_print_operand(PG_SLICE_AT(ins.operands, 0), fn_def.metadata);
      printf(" %s ",
             LEX_TOKEN_KIND_EQUAL_EQUAL == ins.token_kind ? "==" : "!=");
      ir_print_operand(PG_SLICE_AT(ins.operands, 1), fn_def.metadata);

      printf(" // ");
      metadata_print_meta(meta);
    } break;
    case IR_INSTRUCTION_KIND_LOAD: {
      PG_ASSERT(1 == ins.operands.len);
      PG_ASSERT(0 != ins.meta_idx.value);
      Metadata meta = PG_SLICE_AT(fn_def.metadata, ins.meta_idx.value);

      IrOperand rhs = PG_SLICE_AT(ins.operands, 0);
      ir_print_var(meta);
      printf(" := ");
      ir_print_operand(rhs, fn_def.metadata);

      printf(" // ");
      metadata_print_meta(meta);
    } break;
    case IR_INSTRUCTION_KIND_ADDRESS_OF: {
      PG_ASSERT(1 == ins.operands.len);
      PG_ASSERT(0 != ins.meta_idx.value);

      Metadata meta = PG_SLICE_AT(fn_def.metadata, ins.meta_idx.value);

      ir_print_var(meta);
      printf(" := &");
      ir_print_operand(PG_SLICE_AT(ins.operands, 0), fn_def.metadata);

      printf(" // ");
      metadata_print_meta(meta);
    } break;
    case IR_INSTRUCTION_KIND_SYSCALL: {
      Metadata meta = PG_SLICE_AT(fn_def.metadata, ins.meta_idx.value);

      ir_print_var(meta);
      printf("%ssyscall(", 0 == ins.meta_idx.value ? "" : " := ");

      for (u64 j = 0; j < ins.operands.len; j++) {
        IrOperand val = PG_SLICE_AT(ins.operands, j);
        ir_print_operand(val, fn_def.metadata);

        if (j + 1 < ins.operands.len) {
          printf(", ");
        }
      }

      printf(")");

      if (0 != ins.meta_idx.value) {
        printf(" // ");
        metadata_print_meta(meta);
      }
    } break;
    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
      PG_ASSERT(2 == ins.operands.len);
      PG_ASSERT(0 == ins.meta_idx.value);

      IrOperand branch_else = PG_SLICE_AT(ins.operands, 0);
      PG_ASSERT(IR_OPERAND_KIND_LABEL == branch_else.kind);

      IrOperand cond = PG_SLICE_AT(ins.operands, 1);
      PG_ASSERT(IR_OPERAND_KIND_VAR == cond.kind ||
                IR_OPERAND_KIND_U64 == cond.kind);

      printf("jump_if_false(");
      ir_print_operand(cond, fn_def.metadata);
      printf(", ");
      ir_print_operand(branch_else, fn_def.metadata);
      printf(")");
    } break;
    case IR_INSTRUCTION_KIND_JUMP: {
      PG_ASSERT(1 == ins.operands.len);
      PG_ASSERT(0 == ins.meta_idx.value);

      IrOperand op = PG_SLICE_AT(ins.operands, 0);
      PG_ASSERT(IR_OPERAND_KIND_LABEL == op.kind);
      PG_ASSERT(op.u.label.value.len);
      printf("jump ");
      ir_print_operand(op, fn_def.metadata);
    } break;

    case IR_INSTRUCTION_KIND_LABEL_DEFINITION: {
      PG_ASSERT(1 == ins.operands.len);
      PG_ASSERT(0 == ins.meta_idx.value);

      IrOperand op = PG_SLICE_AT(ins.operands, 0);
      PG_ASSERT(IR_OPERAND_KIND_LABEL == op.kind);
      PG_ASSERT(op.u.label.value.len);
      ir_print_operand(op, fn_def.metadata);
    } break;
    default:
      PG_ASSERT(0);
    }

    if (IR_INSTRUCTION_KIND_LABEL_DEFINITION == ins.kind) {
      printf(":");
    }
    printf("\n");
#if 0
  if (ins.tombstone) {
    printf("\x1B[0m"); // Reset.
  }
#endif
  }
  printf("}\n");

  printf("\n------------ IR metadata %.*s ------------\n", (i32)fn_def.name.len,
         fn_def.name.data);
  metadata_print(fn_def.metadata);
  printf("\n\n");
}

static void ir_emitter_print_fn_definitions(IrEmitter emitter) {
  for (u64 i = 0; i < emitter.fn_definitions.len; i++) {
    IrFnDefinition fn_def = PG_SLICE_AT(emitter.fn_definitions, i);
    ir_emitter_print_fn_definition(fn_def);
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
