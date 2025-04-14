#pragma once
#include "amd64.h"
#include "submodules/cstd/lib.c"

static const u32 ElfProgramHeaderTypeLoad = 1;
static const u32 ElfProgramHeaderFlagsExecutable = 1;
static const u32 ElfProgramHeaderFlagsReadable = 4;

static const u32 ElfSectionHeaderTypeProgBits = 1;
static const u32 ElfSectionHeaderTypeStrTab = 3;
static const u64 ElfSectionHeaderFlagAlloc = 2;
static const u64 ElfSectionHeaderFlagExecInstr = 4;

typedef struct {
  u32 type;
  u32 flags;
  u64 p_offset;
  u64 p_vaddr;
  u64 p_paddr;
  u64 p_filesz;
  u64 p_memsz;
  u64 alignment;
} ElfProgramHeader;
static_assert(56 == sizeof(ElfProgramHeader));

typedef struct {
  u32 name;
  u32 type;
  u64 flags;
  u64 addr;
  u64 offset;
  u64 size;
  u32 link;
  u32 info;
  u64 align;
  u64 entsize;
} ElfSectionHeader;
static_assert(64 == sizeof(ElfSectionHeader));

[[nodiscard]]
static PgError elf_write_exe(Amd64Program program, PgAllocator *allocator) {
  u64 vm_start = 1 << 22;
  u64 page_size = 0x1000;
  u64 elf_header_size = 64;

  PgString program_encoded = amd64_encode_program_text(program, allocator);

  const u64 program_headers_len = 2;
  ElfProgramHeader program_headers[] = {
      {
          .type = ElfProgramHeaderTypeLoad,
          .p_offset = page_size,
          .p_vaddr = vm_start + page_size,
          .p_paddr = vm_start + page_size,
          .p_filesz =
              elf_header_size + program_headers_len * sizeof(ElfProgramHeader),
          .p_memsz =
              elf_header_size + program_headers_len * sizeof(ElfProgramHeader),
          .flags =
              ElfProgramHeaderFlagsExecutable | ElfProgramHeaderFlagsReadable,
          .alignment = page_size,
      },
      {
          .type = ElfProgramHeaderTypeLoad,
          .p_offset = PG_ROUNDUP(program_encoded.len, page_size),
          .p_filesz = elf_header_size +
                      program_headers_len * sizeof(ElfProgramHeader) +
                      PG_ROUNDUP(program_encoded.len, page_size),
          .p_memsz = elf_header_size +
                     program_headers_len * sizeof(ElfProgramHeader) +
                     PG_ROUNDUP(program_encoded.len, page_size),
          .p_vaddr =
              vm_start + page_size + PG_ROUNDUP(program_encoded.len, page_size),
          .p_paddr =
              vm_start + page_size + PG_ROUNDUP(program_encoded.len, page_size),
          .flags = ElfProgramHeaderFlagsReadable,
          .alignment = page_size,
      },
  };

  PgString elf_strings[] = {
      PG_S(".shstrtab"),
      PG_S(".text"),
      PG_S(".rodata"),
      PG_S(".data"),
  };
  PgStringSlice elf_strings_slice = {
      .data = elf_strings,
      .len = PG_STATIC_ARRAY_LEN(elf_strings),
  };
  u64 strings_size = 1;

  for (u64 i = 0; i < elf_strings_slice.len; i++) {
    PgString elf_string = PG_SLICE_AT(elf_strings_slice, i);
    strings_size += elf_string.len + 1 /* Null terminator */;
  }

  u64 rodata_size = 0;
  for (u64 i = 0; i < program.rodata.len; i++) {
    Amd64Constant constant = PG_SLICE_AT(program.rodata, i);
    switch (constant.kind) {
    case AMD64_CONSTANT_KIND_NONE:
      PG_ASSERT(0);
    case AMD64_CONSTANT_KIND_U64:
      rodata_size += sizeof(u64);
      break;
    case AMD64_CONSTANT_KIND_BYTES:
      rodata_size += constant.bytes.len;
      break;
    default:
      PG_ASSERT(0);
    }
  }

  ElfSectionHeader section_headers[] = {
      // Null
      {0},
      // Text (code).
      {
          .name = 11,
          .type = ElfSectionHeaderTypeProgBits,
          .flags = ElfSectionHeaderFlagExecInstr | ElfSectionHeaderFlagAlloc,
          .addr = vm_start + page_size,
          .offset = page_size,
          .size = program_encoded.len,
          .align = 16,
      },

      // Rodata.
      {
          .name = 17,
          .type = ElfSectionHeaderTypeProgBits,
          .flags = ElfSectionHeaderFlagAlloc,
          .addr =
              vm_start + page_size + PG_ROUNDUP(program_encoded.len, page_size),
          .offset = page_size + PG_ROUNDUP(program_encoded.len, page_size),
          .size = rodata_size,
          .align = 16,
      },

      // Strings.
      {
          .name = 1,
          .type = ElfSectionHeaderTypeStrTab,
          .flags = 0,
          .addr = 0,
          .offset = page_size + PG_ROUNDUP(program_encoded.len, page_size) +
                    rodata_size,
          .size = strings_size,
          .align = 1,
      },
  };

  Pgu8Dyn sb = {0};
  PG_DYN_ENSURE_CAP(&sb, 32 * PG_KiB, allocator);
  {
    // Magic.
    *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 0x7f;
    PG_DYN_APPEND_SLICE_WITHIN_CAPACITY(&sb, PG_S("ELF"));

    *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 2; // 64 bit.
    *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 1; // Little-endian.
    *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 1; // ELF header version = 1.
    *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 0; // OS ABI, 0 = System V.
    pg_byte_buffer_append_u64_within_capacity(&sb, 0);    // Padding.
    pg_byte_buffer_append_u16_within_capacity(&sb, 2);    // Type: Executable.
    pg_byte_buffer_append_u16_within_capacity(&sb, 0x3e); // ISA x86_64.
    pg_byte_buffer_append_u32_within_capacity(&sb, 1);    // ELF version = 1.
    PG_ASSERT(24 == sb.len);

    // Program entry offset.
    u64 program_entry_offset = program_headers[1].p_vaddr;
    pg_byte_buffer_append_u64_within_capacity(&sb, program_entry_offset);

    // Program header table offset.
    pg_byte_buffer_append_u64_within_capacity(&sb, elf_header_size);

    // Section header table offset.
    u64 section_header_table_offset =
        page_size /* program headers with padding */ +
        PG_ROUNDUP(program_encoded.len, page_size) + rodata_size + strings_size;
    pg_byte_buffer_append_u64_within_capacity(&sb, section_header_table_offset);

    pg_byte_buffer_append_u32_within_capacity(&sb, 0); // Flags.

    PG_ASSERT(52 == sb.len);

    pg_byte_buffer_append_u16_within_capacity(&sb, 64); // Elf header size.
    pg_byte_buffer_append_u16_within_capacity(
        &sb,
        sizeof(
            ElfProgramHeader)); // Size of an entry in the program header table.
    pg_byte_buffer_append_u16_within_capacity(
        &sb,
        PG_STATIC_ARRAY_LEN(
            program_headers)); // Number of entries in the program header table.

    pg_byte_buffer_append_u16_within_capacity(
        &sb,
        sizeof(
            ElfSectionHeader)); // Size of an entry in the section header table.
    pg_byte_buffer_append_u16_within_capacity(
        &sb,
        PG_STATIC_ARRAY_LEN(
            section_headers)); // Number of entries in the section header table.

    u16 section_header_string_table_index =
        PG_STATIC_ARRAY_LEN(section_headers) - 1;
    pg_byte_buffer_append_u16_within_capacity(
        &sb, section_header_string_table_index); // Section index in the section
                                                 // header table.

    PG_ASSERT(64 == sb.len);
  }

  for (u64 i = 0; i < PG_STATIC_ARRAY_LEN(program_headers); i++) {
    PgString s = {.data = (u8 *)&program_headers[i],
                  .len = sizeof(program_headers[i])};
    PG_DYN_APPEND_SLICE_WITHIN_CAPACITY(&sb, s);
  }

  // Pad.
  for (u64 i = sb.len; i < page_size; i++) {
    *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 0;
  }

  // Text.
  PG_DYN_APPEND_SLICE_WITHIN_CAPACITY(&sb, program_encoded);

  // Pad.
  for (u64 i = program_encoded.len;
       i < PG_ROUNDUP(program_encoded.len, page_size); i++) {
    *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 0;
  }

  // Rodata.
  for (u64 i = 0; i < program.rodata.len; i++) {
    Amd64Constant constant = PG_SLICE_AT(program.rodata, i);
    switch (constant.kind) {
    case AMD64_CONSTANT_KIND_NONE:
      PG_ASSERT(0);
    case AMD64_CONSTANT_KIND_U64:
      pg_byte_buffer_append_u64_within_capacity(&sb, constant.n64);
      break;
    case AMD64_CONSTANT_KIND_BYTES:
      PG_DYN_APPEND_SLICE_WITHIN_CAPACITY(&sb, constant.bytes);
      break;
    default:
      PG_ASSERT(0);
    }
  }

  // Strings.
  *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 0; // Null string.

  for (u64 i = 0; i < PG_STATIC_ARRAY_LEN(elf_strings); i++) {
    PG_DYN_APPEND_SLICE_WITHIN_CAPACITY(&sb, elf_strings[i]);
    *PG_DYN_PUSH_WITHIN_CAPACITY(&sb) = 0; // Null terminator.
  }

  for (u64 i = 0; i < PG_STATIC_ARRAY_LEN(section_headers); i++) {
    PgString s = {.data = (u8 *)&section_headers[i],
                  .len = sizeof(section_headers[i])};
    PG_DYN_APPEND_SLICE_WITHIN_CAPACITY(&sb, s);
  }

  PgString sb_string = PG_DYN_SLICE(PgString, sb);

  return pg_file_write_full(program.file_name, sb_string, 0700, allocator);
}
