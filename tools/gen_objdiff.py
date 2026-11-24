#!/usr/bin/env python3
"""Generate objdiff.json for the IDO matching decomp project.

objdiff symbol_mappings are directional: the key is the target symbol name and
the value is the base symbol name (target -> base). This was verified with
7.1/ugen/reg_mgr (add_restricted_reg -> restricted_reg).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

from elftools.elf.elffile import ELFFile

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
SRC = ROOT / "src"
SYMBOLS = ROOT / "symbols"

VERSIONS = ("5.3", "7.1")
SOURCE_EXTS = (".c", ".p")
MIN_VERSION = "3.8.3"

# Explicit target -> source aliases where the split name differs from the
# source basename.
SOURCE_ALIASES = {
    ("7.1", "cc", "mld"): "src/mld/sex.c",
    ("7.1", "cc", "release_id"): "src/releaseid.c",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--version",
        choices=(*VERSIONS, "all"),
        default="all",
        help="IDO version to generate units for (default: all)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("objdiff.json"),
        help="output path relative to the repository root (default: objdiff.json)",
    )
    parser.add_argument(
        "--include-missing-base",
        action="store_true",
        help="also emit units for targets without a built base object",
    )
    return parser.parse_args()


def target_objects(version: str) -> list[tuple[str, str, Path]]:
    version_dir = BUILD / "asm" / version
    if not version_dir.is_dir():
        return []

    units: list[tuple[str, str, Path]] = []
    for program_dir in sorted(p for p in version_dir.iterdir() if p.is_dir()):
        program = program_dir.name
        for target in sorted(program_dir.rglob("*.o")):
            rel = target.relative_to(program_dir).with_suffix("").as_posix()
            units.append((program, rel, target))
    return units


def resolve_source(version: str, program: str, rel: str) -> Path | None:
    alias = SOURCE_ALIASES.get((version, program, rel))
    if alias is not None:
        path = ROOT / alias
        return path if path.is_file() else None

    rel_path = Path(rel)
    basename = rel_path.name

    for ext in SOURCE_EXTS:
        candidates = (
            SRC / program / f"{rel}{ext}",
            SRC / f"{rel}{ext}",
            SRC / program / f"{basename}{ext}",
        )
        for candidate in candidates:
            if candidate.is_file():
                return candidate

    match = re.fullmatch(r"[A-Za-z0-9]+_([0-9A-Fa-f]{6})", basename)
    if match is not None:
        vram = 0x400000 + int(match.group(1), 16)
        candidate = SRC / program / f"code_{vram:08X}.c"
        if candidate.is_file():
            return candidate

    matches: list[Path] = []
    for ext in SOURCE_EXTS:
        matches.extend(SRC.rglob(f"{basename}{ext}"))
    if len(matches) == 1:
        return matches[0]
    return None


def base_for_source(version: str, source: Path) -> Path:
    rel = source.relative_to(SRC).with_suffix(".o")
    return BUILD / "src" / version / rel


def base_for_target(version: str, program: str, rel: str) -> Path | None:
    for candidate in (
        BUILD / "src" / version / program / f"{rel}.o",
        BUILD / "src" / version / f"{rel}.o",
    ):
        if candidate.is_file():
            return candidate
    return None


def read_symbols(path: Path) -> list[tuple[str, int, int, str]]:
    with path.open("rb") as f:
        elf = ELFFile(f)
        symtab = elf.get_section_by_name(".symtab")
        if symtab is None:
            return []

        result: list[tuple[str, int, int, str]] = []
        section_count = elf.num_sections()
        for symbol in symtab.iter_symbols():
            name = symbol.name
            if not name or name.endswith(".NON_MATCHING"):
                continue
            if symbol["st_info"]["type"] not in ("STT_FUNC", "STT_OBJECT", "STT_NOTYPE"):
                continue
            section_index = symbol["st_shndx"]
            if not isinstance(section_index, int):
                continue
            if section_index <= 0 or section_index >= section_count:
                continue
            size = symbol["st_size"]
            if size <= 0:
                continue
            section = elf.get_section(section_index)
            if section is None:
                continue
            result.append((section.name, symbol["st_value"], size, name))
        return result


def symbol_mappings(target_path: Path, base_path: Path, version: str, program: str) -> dict[str, str]:
    target_symbols = read_symbols(target_path)
    base_symbols = read_symbols(base_path)

    target_by_key: dict[tuple[str, int, int], set[str]] = defaultdict(set)
    base_by_key: dict[tuple[str, int, int], set[str]] = defaultdict(set)
    target_by_name: dict[str, tuple[str, int, int]] = {}

    for section, value, size, name in target_symbols:
        target_by_key[(section, value, size)].add(name)
        target_by_name[name] = (section, value, size)
    for section, value, size, name in base_symbols:
        base_by_key[(section, value, size)].add(name)

    mappings: dict[str, str] = {}
    for key, target_names in target_by_key.items():
        if len(target_names) != 1:
            continue
        base_names = base_by_key.get(key, set())
        if len(base_names) != 1:
            continue
        target_name = next(iter(target_names))
        base_name = next(iter(base_names))
        if target_name != base_name:
            mappings[target_name] = base_name

    overrides = load_overrides(version, program)
    for target_name, action in overrides.items():
        if action == "ignored":
            mappings.pop(target_name, None)
        elif action == "matched":
            if target_name in mappings:
                continue
            key = target_by_name.get(target_name)
            if key is None:
                continue
            base_names = base_by_key.get(key, set())
            if len(base_names) != 1:
                continue
            base_name = next(iter(base_names))
            if base_name != target_name:
                mappings[target_name] = base_name

    return dict(sorted(mappings.items()))


def load_overrides(version: str, program: str) -> dict[str, str]:
    path = SYMBOLS / version / f"{program}.match_overrides.txt"
    if not path.is_file():
        return {}

    overrides: dict[str, str] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line or "=" not in line:
            continue
        target, action = (part.strip() for part in line.split("=", 1))
        if action in ("matched", "ignored"):
            overrides[target] = action
    return overrides


def generate(versions: list[str], include_missing_base: bool) -> tuple[dict, int, int, int]:
    categories: dict[str, dict[str, str]] = {}
    units: list[dict] = []
    complete_units = 0
    mapping_count = 0
    skipped_units = 0

    for version in versions:
        for program, rel, target in target_objects(version):
            source = resolve_source(version, program, rel)
            base: Path | None = None
            if source is not None:
                candidate = base_for_source(version, source)
                if candidate.is_file():
                    base = candidate
            if base is None:
                base = base_for_target(version, program, rel)

            if base is None and not include_missing_base:
                skipped_units += 1
                continue

            category_id = f"{version}/{program}"
            categories.setdefault(category_id, {"id": category_id, "name": f"{version} / {program}"})

            complete = base is not None
            if complete:
                complete_units += 1

            metadata: dict = {
                "complete": complete,
                "auto_generated": source is None,
                "progress_categories": [category_id],
            }
            if source is not None:
                metadata["source_path"] = source.relative_to(ROOT).as_posix()

            unit: dict = {
                "name": f"{version}/{program}/{rel}",
                "target_path": target.relative_to(ROOT).as_posix(),
                "symbol_mappings": {},
                "metadata": metadata,
            }
            if base is not None:
                unit["base_path"] = base.relative_to(ROOT).as_posix()
                unit["symbol_mappings"] = symbol_mappings(target, base, version, program)
                mapping_count += len(unit["symbol_mappings"])

            units.append(unit)

    return {
        "min_version": MIN_VERSION,
        "build_base": False,
        "build_target": False,
        "watch_patterns": ["src/**", "symbols/**", "include/**"],
        "progress_categories": [categories[key] for key in sorted(categories)],
        "units": units,
    }, complete_units, mapping_count, skipped_units


def main() -> int:
    args = parse_args()
    versions = list(VERSIONS) if args.version == "all" else [args.version]
    config, complete_units, mapping_count, skipped_units = generate(
        versions, args.include_missing_base
    )

    output = args.output if args.output.is_absolute() else ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", encoding="utf-8") as f:
        json.dump(config, f, indent=2)
        f.write("\n")

    try:
        display = output.relative_to(ROOT)
    except ValueError:
        display = output
    print(
        f"Wrote {display}: {len(config['units'])} units "
        f"({complete_units} with base, {skipped_units} skipped without base), "
        f"{mapping_count} symbol mappings"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
