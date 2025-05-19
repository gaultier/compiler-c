#pragma once

#include "origin.h"

typedef struct {
  PgString name;
  u64 size;
  Origin origin;
} Type;
PG_DYN(Type) TypeDyn;

static const Type types_builtin[] = {
    {0}, // Dummy
    {.name = PG_S("u64"), .size = sizeof(u64)},
    {.name = PG_S("bool"), .size = 1},
};

typedef struct {
  TypeDyn types;
} TypeChecker;

[[nodiscard]] static TypeChecker
types_make_type_checker(PgAllocator *allocator) {
  TypeChecker type_checker = {0};

  *PG_DYN_PUSH(&type_checker.types, allocator) = (Type){0}; // Dummy
  *PG_DYN_PUSH(&type_checker.types, allocator) =
      (Type){.name = PG_S("u64"), .size = sizeof(u64)};
  *PG_DYN_PUSH(&type_checker.types, allocator) =
      (Type){.name = PG_S("bool"), .size = 1};

  return type_checker;
}

[[nodiscard]] static Type type_find_by_name(TypeDyn types, PgString name) {
  for (u64 i = 0; i < types.len; i++) {
    Type it = PG_SLICE_AT(types, i);
    if (pg_string_eq(it.name, name)) {
      return it;
    }
  }

  return (Type){0};
}
