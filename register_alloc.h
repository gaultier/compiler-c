#pragma once
#include "ir.h"

typedef struct {
  u32 value;
} InterferenceNodeIndex;
PG_DYN_DECL(InterferenceNodeIndex);

[[nodiscard]]
static InterferenceGraph reg_build_interference_graph(PG_DYN(Metadata) metadata,
                                                      PgAllocator *allocator) {
  InterferenceGraph graph = {0};

  if (1 == metadata.len) {
    return graph;
  }

  graph = pg_adjacency_matrix_make(metadata.len, allocator);
  PG_ASSERT(metadata.len == graph.nodes_count);

  // Skip dummy.
  for (u64 i = 1; i < metadata.len; i++) {
    Metadata meta = PG_SLICE_AT(metadata, i);
#if 0
    PG_ASSERT(!meta.tombstone);
#endif
    PG_ASSERT(meta.lifetime_start.value <= meta.lifetime_end.value);
    PG_ASSERT(meta.virtual_register.value);

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

[[maybe_unused]]
static void reg_print_interference_graph(InterferenceGraph graph,
                                         PG_DYN(Metadata) metadata,
                                         PgWriter *writer_internals,
                                         PgAllocator *allocator) {

  (void)pg_writer_write_full(writer_internals, PG_S("nodes_count="), allocator);
  (void)pg_writer_write_u64_as_string(writer_internals, graph.nodes_count,
                                      allocator);

  for (u64 row = 0; row < graph.nodes_count; row++) {
    for (u64 col = 0; col < row; col++) {
      bool edge = pg_adjacency_matrix_has_edge(graph, row, col);
      if (!edge) {
        continue;
      }

      Metadata a_meta = PG_SLICE_AT(metadata, row);
      Metadata b_meta = PG_SLICE_AT(metadata, col);
      metadata_print_var(a_meta, writer_internals, allocator);
      (void)pg_writer_write_full(writer_internals, PG_S(" -> "), allocator);
      metadata_print_var(b_meta, writer_internals, allocator);
      (void)pg_writer_write_full(writer_internals, PG_S("\n"), allocator);
    }
  }
}
