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
from dataclasses import dataclass
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

            size = symbol["st_size"]
            if size <= 0:
                continue

            section = elf.get_section(section_index)
            if section is None:
                continue

            symbols.append(
                Symbol(
                    section=section.name,
                    value=symbol["st_value"],
                    size=size,
                    name=name,
                    type=info["type"],
                    bind=info["bind"],
                )
            )
    return symbols


def section_info(path: Path) -> dict[str, tuple[int, bool]]:
    with path.open("rb") as f:
        elf = ELFFile(f)
        return {
            section.name: (section["sh_size"], bool(section["sh_flags"] & 0x4))
            for section in elf.iter_sections()
        }


def missing_symbols(target: Path, base: Path) -> list[Symbol]:
    target_symbols = read_symbols(target)
    base_symbols = read_symbols(base)
    base_keys = {(symbol.section, symbol.value, symbol.size) for symbol in base_symbols}
    base_names = {symbol.name for symbol in base_symbols}
    base_sections = section_info(base)

    additions: list[Symbol] = []
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
        if symbol.value > section_size or symbol.size > section_size - symbol.value:
            continue
        if (symbol.section, symbol.value, symbol.size) in base_keys:
            continue
        if symbol.name in base_names:
            continue
        additions.append(symbol)
    return additions


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
        section = sections.get(addition.section)
        if section is not None and not (section["sh_flags"] & 0x4):
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

    additions = missing_symbols(target, base)
    if not additions:
        return 0

    fd, temp_name = tempfile.mkstemp(
        dir=base.parent, prefix=f".{base.name}.", suffix=".tmp"
    )
    os.close(fd)
    temp = Path(temp_name)
    try:
        shutil.copy2(base, temp)
        command = [objcopy_command()]
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
