#pragma once
#include "ir.h"
#include "submodules/cstd/lib.c"

// On all relevant targets (amd64, aarch64, riscv), syscalls take up to 6
// register arguments.
static const u64 max_syscall_args_count = 6;

typedef struct {
  u32 value;
} InterferenceNodeIndex;
PG_SLICE(InterferenceNodeIndex) InterferenceNodeIndexSlice;
PG_DYN(InterferenceNodeIndex) InterferenceNodeIndexDyn;

typedef struct {
  Label label;
  u64 code_address;
} LabelAddress;
PG_SLICE(LabelAddress) LabelAddressSlice;
PG_DYN(LabelAddress) LabelAddressDyn;

typedef enum {
  LIR_INSTRUCTION_KIND_NONE,
  LIR_INSTRUCTION_KIND_ADD,
  LIR_INSTRUCTION_KIND_SUB,
  LIR_INSTRUCTION_KIND_MOV,
  LIR_INSTRUCTION_KIND_JUMP_IF_EQ,
  LIR_INSTRUCTION_KIND_JUMP,
  LIR_INSTRUCTION_KIND_LABEL_DEFINITION,
  LIR_INSTRUCTION_KIND_CMP,
  LIR_INSTRUCTION_KIND_ADDRESS_OF,
  LIR_INSTRUCTION_KIND_SYSCALL,
} LirInstructionKind;

typedef enum {
  LIR_OPERAND_KIND_NONE,
  LIR_OPERAND_KIND_VIRTUAL_REGISTER,
  LIR_OPERAND_KIND_IMMEDIATE,
  LIR_OPERAND_KIND_LABEL,
} LirOperandKind;

typedef struct {
  LirOperandKind kind;
  union {
    MetadataIndex meta_idx;
    u64 immediate;
    Label label; // LIR_OPERAND_KIND_LABEL.
  } u;
} LirOperand;
PG_SLICE(LirOperand) LirOperandSlice;
PG_DYN(LirOperand) LirOperandDyn;

typedef struct {
  LirInstructionKind kind;
  LirOperandDyn operands;
  Origin origin;
  LexTokenKind token_kind;
} LirInstruction;
PG_DYN(LirInstruction) LirInstructionDyn;

// Graph represented as a adjacency matrix (M(i,j) = 1 if there is an edge
// between i and j), stored as a bitfield of the right-upper half (without the
// diagonal).
// Each row is a memory location (see above field).
typedef PgAdjacencyMatrix InterferenceGraph;

typedef struct {
  PgString name;
  AstNodeFlag flags;

  // TODO: Arguments.

  LirInstructionDyn instructions;
  MetadataDyn metadata;
  InterferenceGraph interference_graph;
  u32 stack_base_pointer_offset;
  u32 stack_base_pointer_max_offset;
} LirFnDefinition;
PG_DYN(LirFnDefinition) LirFnDefinitionDyn;

typedef struct {
  LirFnDefinitionDyn fn_definitions;
} LirEmitter;

static void lir_print_operand(LirOperand op, MetadataDyn metadata) {
  switch (op.kind) {
  case LIR_OPERAND_KIND_NONE:
    PG_ASSERT(0);
  case LIR_OPERAND_KIND_VIRTUAL_REGISTER:
    Metadata meta = PG_SLICE_AT(metadata, op.u.meta_idx.value);
    printf("v%u{constraint=%s, addressable=%s}", meta.virtual_register.value,
           lir_register_constraint_to_cstr(meta.virtual_register.constraint),
           meta.virtual_register.addressable ? "true" : "false");
    break;
  case LIR_OPERAND_KIND_IMMEDIATE:
    printf("%" PRIu64, op.u.immediate);
    break;
  case LIR_OPERAND_KIND_LABEL:
    PG_ASSERT(op.u.label.value.len);
    printf("%.*s", (i32)op.u.label.value.len, op.u.label.value.data);
    break;
  default:
    PG_ASSERT(0);
  }
}

static void lir_emitter_print_fn_definition(LirFnDefinition fn_def) {
  PG_ASSERT(fn_def.name.len);

  printf("fn %.*s() {\n", (i32)fn_def.name.len, fn_def.name.data);

  for (u64 i = 0; i < fn_def.instructions.len; i++) {
    LirInstruction ins = PG_SLICE_AT(fn_def.instructions, i);

    if (LIR_INSTRUCTION_KIND_LABEL_DEFINITION == ins.kind) {
      printf("\n");
    }

    printf("[%" PRIu64 "] ", i);

    origin_print(ins.origin);
    printf(": ");

    switch (ins.kind) {
    case LIR_INSTRUCTION_KIND_ADD:
      printf("add ");
      break;
    case LIR_INSTRUCTION_KIND_SUB:
      printf("sub ");
      break;
    case LIR_INSTRUCTION_KIND_MOV:
      printf("mov ");
      break;
    case LIR_INSTRUCTION_KIND_SYSCALL:
      printf("syscall ");
      break;
    case LIR_INSTRUCTION_KIND_JUMP_IF_EQ:
      printf("je ");
      break;
    case LIR_INSTRUCTION_KIND_JUMP:
      printf("jmp ");
      break;
    case LIR_INSTRUCTION_KIND_LABEL_DEFINITION:
      break;
    case LIR_INSTRUCTION_KIND_ADDRESS_OF:
      printf("address_of ");
      break;
    case LIR_INSTRUCTION_KIND_CMP:
      PG_ASSERT(LEX_TOKEN_KIND_EQUAL_EQUAL == ins.token_kind);
      PG_ASSERT(3 == ins.operands.len);
      printf("cmp%s ",
             LEX_TOKEN_KIND_EQUAL_EQUAL == ins.token_kind ? "==" : "!=");
      break;
    case LIR_INSTRUCTION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }

    for (u64 j = 0; j < ins.operands.len; j++) {
      LirOperand op = PG_SLICE_AT(ins.operands, j);
      lir_print_operand(op, fn_def.metadata);

      if (j + 1 < ins.operands.len) {
        printf(", ");
      }
    }

    if (LIR_INSTRUCTION_KIND_LABEL_DEFINITION == ins.kind) {
      printf(":");
    }
    printf("\n");
  }
  printf("}\n\n");
}

static void lir_emitter_print_fn_definitions(LirEmitter emitter) {
  for (u64 i = 0; i < emitter.fn_definitions.len; i++) {
    LirFnDefinition fn_def = PG_SLICE_AT(emitter.fn_definitions, i);
    lir_emitter_print_fn_definition(fn_def);
  }
}

static void lir_emit_copy_virt_reg_to_virt_reg(LirFnDefinition *fn_def,
                                               MetadataIndex src_idx,
                                               MetadataIndex dst_idx,
                                               Origin origin,
                                               PgAllocator *allocator) {
  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand rhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .u.meta_idx = src_idx,
  };

  LirOperand lhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .u.meta_idx = dst_idx,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;
}

// We pass `IrOperand src` to be open to more immediate kinds in the future.
static void lir_emit_copy_immediate_to_virt_reg(LirFnDefinition *fn_def,
                                                IrOperand src_op,
                                                MetadataIndex dst_idx,
                                                Origin origin,
                                                PgAllocator *allocator) {
  // TODO: Expand when more immediate types are available.
  PG_ASSERT(IR_OPERAND_KIND_NUMBER == src_op.kind);

  LirInstruction ins = {
      .kind = LIR_INSTRUCTION_KIND_MOV,
      .origin = origin,
  };
  PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

  LirOperand lhs = {
      .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
      .u.meta_idx = dst_idx,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs;

  LirOperand rhs = {
      .kind = LIR_OPERAND_KIND_IMMEDIATE,
      .u.immediate = src_op.u.n64,
  };
  *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs;

  *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;
}

static void lir_emit_copy_to_virt_reg(LirFnDefinition *fn_def, IrOperand src_op,
                                      MetadataIndex dst_meta_idx, Origin origin,
                                      PgAllocator *allocator) {
  switch (src_op.kind) {
  case IR_OPERAND_KIND_NUMBER:
    lir_emit_copy_immediate_to_virt_reg(fn_def, src_op, dst_meta_idx, origin,
                                        allocator);
    break;
  case IR_OPERAND_KIND_VAR: {
    lir_emit_copy_virt_reg_to_virt_reg(fn_def, src_op.u.meta_idx, dst_meta_idx,
                                       origin, allocator);
  } break;
  case IR_OPERAND_KIND_LABEL:
  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]]
static LirOperand lir_ir_operand_to_lir_operand(IrOperand ir_op) {
  switch (ir_op.kind) {
  case IR_OPERAND_KIND_NUMBER:
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_IMMEDIATE,
        .u.immediate = ir_op.u.n64,
    };
  case IR_OPERAND_KIND_VAR: {
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .u.meta_idx = ir_op.u.meta_idx,
    };
  }
  case IR_OPERAND_KIND_LABEL:
    return (LirOperand){
        .kind = LIR_OPERAND_KIND_LABEL,
        .u.label = ir_op.u.label,
    };
  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void lir_emit_instruction(LirFnDefinition *fn_def, IrInstruction ir_ins,
                                 PgAllocator *allocator) {
#if 0
  PG_ASSERT(!ir_ins.tombstone);
#endif

  switch (ir_ins.kind) {
  case IR_INSTRUCTION_KIND_ADD: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.meta_idx.value);

    IrOperand lhs_ir_val = PG_SLICE_AT(ir_ins.operands, 0);

    lir_emit_copy_to_virt_reg(fn_def, lhs_ir_val, ir_ins.meta_idx,
                              ir_ins.origin, allocator);

    // We now need to add rhs to it.

    IrOperand rhs_ir_val = PG_SLICE_AT(ir_ins.operands, 1);
    PG_ASSERT(IR_OPERAND_KIND_VAR == rhs_ir_val.kind ||
              IR_OPERAND_KIND_NUMBER == rhs_ir_val.kind);

    LirOperand rhs_op = lir_ir_operand_to_lir_operand(rhs_ir_val);
    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_ADD,
        .origin = ir_ins.origin,
    };
    PG_DYN_ENSURE_CAP(&ins.operands, 2, allocator);

    LirOperand lhs_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .u.meta_idx = ir_ins.meta_idx,
    };
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = lhs_op;
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins.operands) = rhs_op;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;

  } break;
  case IR_INSTRUCTION_KIND_LOAD: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.meta_idx.value);

    IrOperand src_ir_val = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_VAR == src_ir_val.kind ||
              IR_OPERAND_KIND_NUMBER == src_ir_val.kind);

    lir_emit_copy_to_virt_reg(fn_def, src_ir_val, ir_ins.meta_idx,
                              ir_ins.origin, allocator);

  } break;
  case IR_INSTRUCTION_KIND_SYSCALL: {
    PG_ASSERT(ir_ins.operands.len <=
              1 /* syscall num */ + max_syscall_args_count);
    PG_ASSERT(ir_ins.operands.len > 0);

    if (ir_ins.meta_idx.value) {
      PG_SLICE_AT(fn_def->metadata, ir_ins.meta_idx.value)
          .virtual_register.constraint = VREG_CONSTRAINT_SYSCALL_RET;
    }
    // TODO: Record clobbering of first argument since it is also the return
    // value of the syscall (at least on amd64).

    for (u64 j = 0; j < ir_ins.operands.len; j++) {
      IrOperand val = PG_SLICE_AT(ir_ins.operands, j);
      VirtualRegisterConstraint virt_reg_constraint =
          (0 == j)
              ? VREG_CONSTRAINT_SYSCALL_NUM
              : (VirtualRegisterConstraint)(VREG_CONSTRAINT_SYSCALL0 + j - 1);
      PG_SLICE_AT(fn_def->metadata, val.u.meta_idx.value)
          .virtual_register.constraint = virt_reg_constraint;
    }

    LirInstruction lir_ins = {
        .kind = LIR_INSTRUCTION_KIND_SYSCALL,
        .origin = ir_ins.origin,
    };
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = lir_ins;

  } break;
  case IR_INSTRUCTION_KIND_ADDRESS_OF: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.meta_idx.value);

    IrOperand lhs_ir_op = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_VAR == lhs_ir_op.kind);

    PG_SLICE_AT(fn_def->metadata, lhs_ir_op.u.meta_idx.value)
        .virtual_register.addressable = true;

    PG_ASSERT(lhs_ir_op.u.meta_idx.value != ir_ins.meta_idx.value);

    LirInstruction lir_ins = {
        .kind = LIR_INSTRUCTION_KIND_ADDRESS_OF,
        .origin = ir_ins.origin,
    };
    LirOperand lhs_lir_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .u.meta_idx = ir_ins.meta_idx,
    };
    LirOperand rhs_lir_op = {
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .u.meta_idx = lhs_ir_op.u.meta_idx,
    };
    *PG_DYN_PUSH(&lir_ins.operands, allocator) = lhs_lir_op;
    *PG_DYN_PUSH(&lir_ins.operands, allocator) = rhs_lir_op;
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = lir_ins;
  } break;
  case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.meta_idx.value);

    IrOperand branch_else = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == branch_else.kind);

    LirInstruction ins_je = {
        .kind = LIR_INSTRUCTION_KIND_JUMP_IF_EQ,
        .origin = ir_ins.origin,
    };

    LirOperand ins_je_op = {
        .kind = LIR_OPERAND_KIND_LABEL,
        .u.label = branch_else.u.label,
    };
    *PG_DYN_PUSH(&ins_je.operands, allocator) = ins_je_op;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins_je;
  } break;
  case IR_INSTRUCTION_KIND_JUMP: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.meta_idx.value);

    IrOperand op = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == op.kind);

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_JUMP,
        .origin = ir_ins.origin,
    };

    LirOperand lir_op = {
        .kind = LIR_OPERAND_KIND_LABEL,
        .u.label = op.u.label,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = lir_op;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;
  } break;
  case IR_INSTRUCTION_KIND_LABEL_DEFINITION: {
    PG_ASSERT(1 == ir_ins.operands.len);
    PG_ASSERT(0 == ir_ins.meta_idx.value);

    IrOperand op = PG_SLICE_AT(ir_ins.operands, 0);
    PG_ASSERT(IR_OPERAND_KIND_LABEL == op.kind);

    LirInstruction ins = {
        .kind = LIR_INSTRUCTION_KIND_LABEL_DEFINITION,
        .origin = ir_ins.origin,
    };

    LirOperand lir_op = {
        .kind = LIR_OPERAND_KIND_LABEL,
        .u.label = op.u.label,
    };
    *PG_DYN_PUSH(&ins.operands, allocator) = lir_op;

    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins;
  } break;

  case IR_INSTRUCTION_KIND_COMPARISON: {
    PG_ASSERT(2 == ir_ins.operands.len);
    PG_ASSERT(ir_ins.meta_idx.value);

    PG_SLICE_AT(fn_def->metadata, ir_ins.meta_idx.value)
        .virtual_register.constraint = VREG_CONSTRAINT_CONDITION_FLAGS;

    IrOperand ir_lhs = PG_SLICE_AT(ir_ins.operands, 0);
    IrOperand ir_rhs = PG_SLICE_AT(ir_ins.operands, 1);

    LirInstruction ins_cmp = {
        .kind = LIR_INSTRUCTION_KIND_CMP,
        .origin = ir_ins.origin,
        .token_kind = ir_ins.token_kind,
    };
    PG_DYN_ENSURE_CAP(&ins_cmp.operands, 3, allocator);

    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_cmp.operands) = (LirOperand){
        .kind = LIR_OPERAND_KIND_VIRTUAL_REGISTER,
        .u.meta_idx = ir_ins.meta_idx,
    };
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_cmp.operands) =
        lir_ir_operand_to_lir_operand(ir_lhs);
    *PG_DYN_PUSH_WITHIN_CAPACITY(&ins_cmp.operands) =
        lir_ir_operand_to_lir_operand(ir_rhs);
    *PG_DYN_PUSH(&fn_def->instructions, allocator) = ins_cmp;

  } break;

  case IR_INSTRUCTION_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]]
static InterferenceGraph lir_build_interference_graph(MetadataDyn metadata,
                                                      PgAllocator *allocator) {
  InterferenceGraph graph = {0};

  if (1 == metadata.len) {
    return graph;
  }

  graph = pg_adjacency_matrix_make(metadata.len, allocator);
  PG_ASSERT(metadata.len == graph.nodes_count);

  for (u64 i = 0; i < metadata.len; i++) {
    Metadata meta = PG_SLICE_AT(metadata, i);
#if 0
    PG_ASSERT(!meta.tombstone);
#endif
    PG_ASSERT(meta.lifetime_start.value <= meta.lifetime_end.value);
    PG_ASSERT(i == 0 || meta.virtual_register.value);

    // Interferes with no one (unused).
    if (meta.lifetime_start.value == meta.lifetime_end.value) {
      continue;
    }

    for (u64 j = i + 1; j < metadata.len; j++) {
      Metadata it = PG_SLICE_AT(metadata, j);
      PG_ASSERT(it.lifetime_start.value <= it.lifetime_end.value);
#if 0
      PG_ASSERT(!it.tombstone);
#endif

      PG_ASSERT(meta.virtual_register.value != it.virtual_register.value);

      // Interferes with no one (unused).
      if (it.lifetime_start.value == it.lifetime_end.value) {
        continue;
      }

      // `it` strictly before `meta`.
      if (it.lifetime_end.value < meta.lifetime_start.value) {
        continue;
      }

      // `it` strictly after `meta`.
      if (meta.lifetime_end.value < it.lifetime_start.value) {
        continue;
      }

      // Interferes: add an edge between the two nodes.

      pg_adjacency_matrix_add_edge(&graph, j, i);
    }
  }

  return graph;
}

static void lir_print_interference_graph(InterferenceGraph graph,
                                         MetadataDyn metadata) {

  printf("nodes_count=%lu\n\n", graph.nodes_count);

  for (u64 row = 0; row < graph.nodes_count; row++) {
    for (u64 col = 0; col < row; col++) {
      bool edge = pg_adjacency_matrix_has_edge(graph, row, col);
      if (!edge) {
        continue;
      }

      Metadata a_meta = PG_SLICE_AT(metadata, row);
      Metadata b_meta = PG_SLICE_AT(metadata, col);
      ir_print_var(a_meta);
      printf(" -> ");
      ir_print_var(b_meta);
      printf("\n");
    }
  }
}

static void lir_emit_fn_definition(LirEmitter *emitter,
                                   IrFnDefinition ir_fn_def, bool verbose,
                                   PgAllocator *allocator) {
  LirFnDefinition lir_fn_def = {
      .name = ir_fn_def.name,
      .flags = ir_fn_def.flags,
      .metadata = ir_fn_def.metadata,
  };

  for (u64 i = 0; i < ir_fn_def.instructions.len; i++) {
    lir_emit_instruction(&lir_fn_def, PG_SLICE_AT(ir_fn_def.instructions, i),
                         allocator);
  }

  if (lir_fn_def.metadata.len > 0) {
    lir_fn_def.interference_graph =
        lir_build_interference_graph(lir_fn_def.metadata, allocator);
  }

  if (verbose) {
    printf("\n------------ Interference graph ------------\n");
    lir_print_interference_graph(lir_fn_def.interference_graph,
                                 lir_fn_def.metadata);
  }

  *PG_DYN_PUSH(&emitter->fn_definitions, allocator) = lir_fn_def;
}

static void lir_emit_fn_definitions(LirEmitter *emitter,
                                    IrFnDefinitionDyn ir_fn_definitions,
                                    bool verbose, PgAllocator *allocator) {
  for (u64 i = 0; i < ir_fn_definitions.len; i++) {
    IrFnDefinition ir_fn_def = PG_SLICE_AT(ir_fn_definitions, i);
    lir_emit_fn_definition(emitter, ir_fn_def, verbose, allocator);
  }
}
