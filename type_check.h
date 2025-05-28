#pragma once

#include "origin.h"

typedef enum {
  TYPE_KIND_NONE,
  TYPE_KIND_BOOLEAN,
  TYPE_KIND_NUMBER,
  // More...
} TypeKind;

typedef struct Type Type;
struct Type {
  TypeKind kind;
  u64 size;
  Origin origin;
  PgString name; // Key.
  Type *child[4];
};

typedef struct {
  u32 value;
} TypeIdx;

#if 0
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
#endif

[[nodiscard]] static Type *type_upsert(Type **htrie, PgString name,
                                       PgAllocator *allocator) {
  for (u64 h = pg_hash_fnv(name); *htrie; h <<= 2) {
    if (pg_string_eq(name, (*htrie)->name)) {
      return *htrie;
    }
    htrie = &(*htrie)->child[h >> 62];
  }
  if (!allocator) {
    return nullptr;
  }

  *htrie = pg_alloc(allocator, sizeof(Type), _Alignof(Type), 1);
  (*htrie)->name = name;

  return (*htrie);
}

static void type_print(Type *type) {
  if (!type) {
    printf("any");
    return;
  }

  printf("%.*s", (i32)type->name.len, type->name.data);
}
