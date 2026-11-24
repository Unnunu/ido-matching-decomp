#!/usr/bin/env python3
"""Copy missing local target symbols into a base object for objdiff.

The IDO build often leaves anonymous local data and static functions unnamed,
while spimdisasm gives the corresponding target symbols names such as
``RO_STR_...``, ``D_...`` and ``func_...``. objdiff can only pair symbols that
exist on both sides, so without this step the whole base ``.rodata`` section is
matched against one target blob and the GUI cannot show string-by-string
comparisons.

This tool adds the missing local target symbols to the base object's symbol
table. It only changes symbol metadata; section contents, relocations and the
rest of the object are left untouched.

BSS labels need special handling. spimdisasm names target BSS ranges ``B_...``
but emits them as size-0 local labels, while the compiler often leaves the base
with only a ``.bss`` section symbol plus relocation addends. objdiff resolves
section relocations to the nearest named symbol, so without mirroring, target
relocations use ``B_...`` while base relocations use ``[.bss]+offset`` and a
correct reference is reported as a mismatch. Missing target BSS labels are
therefore copied to the base, but only when the base has no symbol at the
destination offset. They keep size 0 and ``STT_NOTYPE``. If a target split
covers only part of the base ``.bss`` (or the compiler ordered BSS variables
differently), the destination is shifted by a per-section delta inferred from
matching ``R_MIPS_LO16`` relocations.
"""

from __future__ import annotations

import argparse
import io
import os
import shutil
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass, replace
from pathlib import Path

from elftools.elf.elffile import ELFFile

SYMBOL_TYPES = ("STT_FUNC", "STT_OBJECT", "STT_NOTYPE")


@dataclass(frozen=True)
class Symbol:
    section: str
    value: int
    size: int
    name: str
    type: str
    bind: str
    is_bss: bool = False


def objcopy_command() -> str:
    explicit = os.environ.get("OBJCOPY")
    if explicit:
        return explicit
    prefix = os.environ.get("MIPS_BINUTILS_PREFIX", "mips-linux-gnu-")
    return f"{prefix}objcopy"


def read_symbols(path: Path) -> list[Symbol]:
    symbols: list[Symbol] = []
    with path.open("rb") as f:
        elf = ELFFile(f)
        symtab = elf.get_section_by_name(".symtab")
        if symtab is None:
            return symbols

        for symbol in symtab.iter_symbols():
            name = symbol.name
            if not name or name.endswith(".NON_MATCHING"):
                continue

            info = symbol["st_info"]
            if info["type"] not in SYMBOL_TYPES:
                continue

            section_index = symbol["st_shndx"]
            if (
                not isinstance(section_index, int)
                or section_index <= 0
                or section_index >= elf.num_sections()
            ):
                continue

            section = elf.get_section(section_index)
            if section is None:
                continue

            size = symbol["st_size"]
            is_bss = section["sh_type"] == "SHT_NOBITS"
            if size <= 0 and not (
                is_bss and info["bind"] == "STB_LOCAL" and name.startswith("B_")
            ):
                continue

            symbols.append(
                Symbol(
                    section=section.name,
                    value=symbol["st_value"],
                    size=size,
                    name=name,
                    type=info["type"],
                    bind=info["bind"],
                    is_bss=is_bss,
                )
            )
    return symbols


def symbol_names(path: Path) -> set[str]:
    """Return every symbol name, including undefined ones."""

    names: set[str] = set()
    with path.open("rb") as f:
        elf = ELFFile(f)
        symtab = elf.get_section_by_name(".symtab")
        if symtab is None:
            return names
        for symbol in symtab.iter_symbols():
            if symbol.name:
                names.add(symbol.name)
    return names


def bss_offsets(path: Path) -> dict[str, set[int]]:
    """Map BSS section names to all occupied symbol offsets."""

    offsets: dict[str, set[int]] = {}
    with path.open("rb") as f:
        elf = ELFFile(f)
        symtab = elf.get_section_by_name(".symtab")
        if symtab is None:
            return offsets
        for symbol in symtab.iter_symbols():
            section_index = symbol["st_shndx"]
            if (
                not isinstance(section_index, int)
                or section_index <= 0
                or section_index >= elf.num_sections()
            ):
                continue
            section = elf.get_section(section_index)
            if section is None or section["sh_type"] != "SHT_NOBITS":
                continue
            offsets.setdefault(section.name, set()).add(symbol["st_value"])
    return offsets


def relocation_section(elf: ELFFile, section_name: str):
    for prefix in (".rel", ".rela"):
        section = elf.get_section_by_name(f"{prefix}{section_name}")
        if section is not None:
            return section
    return None


def symbol_section(elf: ELFFile, symbol):
    section_index = symbol["st_shndx"]
    if (
        not isinstance(section_index, int)
        or section_index <= 0
        or section_index >= elf.num_sections()
    ):
        return None
    return elf.get_section(section_index)


def bss_deltas(target: Path, base: Path) -> dict[str, int]:
    """Infer target-to-base BSS offset shifts from matching relocations.

    A target split can cover only part of the base ``.bss`` (or the compiler
    can order BSS variables differently), so the same ``B_...`` name may sit at
    a different offset on each side.  When target and base have an ``R_MIPS_LO16``
    relocation at the same address and both point into BSS, the difference of
    their effective offsets is the section shift.  Only unambiguous shifts are
    returned.
    """

    deltas: dict[str, set[int]] = {}
    with target.open("rb") as target_file, base.open("rb") as base_file:
        target_elf = ELFFile(target_file)
        base_elf = ELFFile(base_file)
        target_symtab = target_elf.get_section_by_name(".symtab")
        base_symtab = base_elf.get_section_by_name(".symtab")
        if target_symtab is None or base_symtab is None:
            return {}

        endian = "<" if target_elf.little_endian else ">"
        for reloc_section in target_elf.iter_sections():
            if not reloc_section.name.startswith((".rel", ".rela")):
                continue
            target_index = reloc_section["sh_info"]
            if target_index <= 0 or target_index >= target_elf.num_sections():
                continue
            target_section = target_elf.get_section(target_index)
            base_section = base_elf.get_section_by_name(target_section.name)
            if base_section is None:
                continue
            base_reloc_section = relocation_section(base_elf, target_section.name)
            if base_reloc_section is None:
                continue

            base_relocs = {
                reloc["r_offset"]: reloc
                for reloc in base_reloc_section.iter_relocations()
            }
            target_data = target_section.data()
            base_data = base_section.data()
            for reloc in reloc_section.iter_relocations():
                if reloc["r_info_type"] != 6:  # R_MIPS_LO16
                    continue
                base_reloc = base_relocs.get(reloc["r_offset"])
                if base_reloc is None or base_reloc["r_info_type"] != 6:
                    continue
                target_symbol = target_symtab.get_symbol(reloc["r_info_sym"])
                base_symbol = base_symtab.get_symbol(base_reloc["r_info_sym"])
                target_bss = symbol_section(target_elf, target_symbol)
                base_bss = symbol_section(base_elf, base_symbol)
                if target_bss is None or base_bss is None:
                    continue
                if target_bss["sh_type"] != "SHT_NOBITS":
                    continue
                if base_bss["sh_type"] != "SHT_NOBITS":
                    continue
                if target_bss.name != base_bss.name:
                    continue
                if reloc["r_offset"] + 4 > len(target_data):
                    continue
                if base_reloc["r_offset"] + 4 > len(base_data):
                    continue
                target_imm = struct.unpack_from(
                    endian + "I", target_data, reloc["r_offset"]
                )[0] & 0xFFFF
                base_imm = struct.unpack_from(
                    endian + "I", base_data, base_reloc["r_offset"]
                )[0] & 0xFFFF
                target_offset = target_symbol["st_value"] + target_imm
                base_offset = base_symbol["st_value"] + base_imm
                deltas.setdefault(target_bss.name, set()).add(
                    base_offset - target_offset
                )

    return {
        section: next(iter(values))
        for section, values in deltas.items()
        if len(values) == 1
    }


def section_info(path: Path) -> dict[str, tuple[int, bool]]:
    with path.open("rb") as f:
        elf = ELFFile(f)
        return {
            section.name: (section["sh_size"], bool(section["sh_flags"] & 0x4))
            for section in elf.iter_sections()
        }


def missing_symbols(target: Path, base: Path) -> tuple[list[Symbol], set[str]]:
    target_symbols = read_symbols(target)
    base_symbols = read_symbols(base)
    base_keys = {(symbol.section, symbol.value, symbol.size) for symbol in base_symbols}
    base_by_name = {symbol.name: symbol for symbol in base_symbols}
    base_names = symbol_names(base)
    base_bss_offsets = bss_offsets(base)
    deltas = bss_deltas(target, base)
    base_sections = section_info(base)

    additions: list[Symbol] = []
    stale: set[str] = set()
    for symbol in target_symbols:
        info = base_sections.get(symbol.section)
        if info is None:
            continue
        section_size, executable = info
        # Local symbols are mirrored everywhere.  Global data symbols are also
        # mirrored when the base has no name for them: a static const such as
        # __Release_ID can be unnamed in the base object even though the bytes
        # are present.  Without the name objdiff drops the whole data section.
        if symbol.bind != "STB_LOCAL" and executable:
            continue
        if symbol.size == 0:
            if not symbol.is_bss:
                continue
            value = symbol.value + deltas.get(symbol.section, 0)
            if value > section_size:
                continue
            existing = base_by_name.get(symbol.name)
            if existing is not None and existing.value == value:
                continue
            # Only mirror BSS labels where the base has no symbol at the
            # target offset.  Otherwise the existing base symbol is enough for
            # objdiff to resolve the relocation, and a duplicate label would
            # just hide the meaningful base name.
            if value in base_bss_offsets.get(symbol.section, set()):
                continue
            if existing is not None:
                # A previously mirrored label at the old (unshifted) offset is
                # stale; move it to the inferred base offset.
                if (
                    existing.is_bss
                    and existing.size == 0
                    and existing.bind == "STB_LOCAL"
                    and existing.name.startswith("B_")
                ):
                    stale.add(symbol.name)
                else:
                    continue
            elif symbol.name in base_names:
                continue
            additions.append(replace(symbol, value=value))
            continue
        if symbol.value > section_size or symbol.size > section_size - symbol.value:
            continue
        if (symbol.section, symbol.value, symbol.size) in base_keys:
            continue
        if symbol.name in base_names:
            continue
        additions.append(symbol)
    return additions, stale


def patch_symbol_metadata(path: Path, additions: list[Symbol]) -> None:
    data = bytearray(path.read_bytes())
    elf = ELFFile(io.BytesIO(data))
    symtab = elf.get_section_by_name(".symtab")
    if symtab is None:
        raise RuntimeError(f"{path}: object has no .symtab")

    endian = "<" if elf.little_endian else ">"
    symbol_offset = symtab["sh_offset"]
    entry_size = symtab["sh_entsize"]
    sections = {section.name: section for section in elf.iter_sections()}
    by_name = {symbol.name: symbol for symbol in additions}
    found: set[str] = set()

    for index, symbol in enumerate(symtab.iter_symbols()):
        addition = by_name.get(symbol.name)
        if addition is None or symbol.name in found:
            continue

        entry_offset = symbol_offset + index * entry_size
        if elf.elfclass == 32:
            struct.pack_into(endian + "I", data, entry_offset + 8, addition.size)
            info_offset = entry_offset + 12
        else:
            struct.pack_into(endian + "Q", data, entry_offset + 16, addition.size)
            info_offset = entry_offset + 4

        # objdiff infers the fake section-symbol size from Object symbols. Mark
        # mirrored data symbols as objects so the section blob is not truncated
        # to the size of the last STT_OBJECT that happened to exist in base.
        # BSS labels stay NOTYPE: they are size-0 relocation targets, not data
        # objects, and objdiff infers their ranges from the neighbouring labels.
        section = sections.get(addition.section)
        if (
            section is not None
            and section["sh_type"] != "SHT_NOBITS"
            and not (section["sh_flags"] & 0x4)
        ):
            bind = data[info_offset] & 0xF0
            data[info_offset] = bind | 1  # STT_OBJECT

        found.add(symbol.name)

    missing = set(by_name) - found
    if missing:
        raise RuntimeError(f"{path}: failed to patch symbols: {', '.join(sorted(missing))}")

    path.write_bytes(data)


def symbolize_base(target: Path, base: Path) -> int:
    """Add target-only symbols to *base* and return the number added."""

    if not target.is_file() or not base.is_file():
        return 0

    additions, stale = missing_symbols(target, base)
    if not additions and not stale:
        return 0

    fd, temp_name = tempfile.mkstemp(
        dir=base.parent, prefix=f".{base.name}.", suffix=".tmp"
    )
    os.close(fd)
    temp = Path(temp_name)
    try:
        shutil.copy2(base, temp)
        command = [objcopy_command()]
        for name in sorted(stale):
            command.append(f"--strip-symbol={name}")
        for symbol in additions:
            bind = "global" if symbol.bind == "STB_GLOBAL" else "local"
            command.append(
                f"--add-symbol={symbol.name}={symbol.section}:{symbol.value},{bind}"
            )
        command.append(str(temp))
        subprocess.run(command, check=True)
        patch_symbol_metadata(temp, additions)
        os.replace(temp, base)
    finally:
        temp.unlink(missing_ok=True)

    return len(additions)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", type=Path, help="target object with named symbols")
    parser.add_argument("base", type=Path, help="base object to update in place")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    count = symbolize_base(args.target, args.base)
    print(f"Added {count} symbol(s) to {args.base}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
