#!/usr/bin/env python3
"""Compute matching progress from an objdiff report.

The objdiff report is the source of truth for matches: a function is matched
only when objdiff reports a 100% fuzzy match.  Target objects without a base
object are still counted as unmatched so unstarted source files stay in the
denominator.  Exclusions and per-program overrides are applied without
modifying the generated objdiff data.

The tool also produces a NON_MATCHING view under build/asm-marked without
rewriting the disassembled asm/ tree.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

from elftools.elf.elffile import ELFFile

from library import LibraryCatalog, library_base_path

ROOT = Path(__file__).resolve().parent.parent

VERSIONS = ("5.3", "7.1")
SCHEMA_VERSION = 1

# Symbols that are not part of the decompilation denominator.  Keep these
# anchored so ordinary functions such as current_address_pair_start or
# mem_start are not excluded by accident.
EXCLUDED_NAME_PATTERNS = (
    re.compile(r"^__start$"),
    re.compile(r"^__start_[A-Za-z0-9_]*$"),
    re.compile(r"^_start$"),
    re.compile(r"^_mcount$"),
    re.compile(r"^__mcount$"),
    re.compile(r"^_ftext$"),
    re.compile(r"^_rld_[A-Za-z0-9_]*$"),
    re.compile(r"^_*crt[A-Za-z0-9_]*$"),
    re.compile(r"^_*runtime[A-Za-z0-9_]*$"),
    re.compile(r"^__runtime_[A-Za-z0-9_]*$"),
)

NONMATCHING_RE = re.compile(r"^\s*nonmatching\s+([^\s,]+)")
MARKED_SUFFIXES = (".text.s", ".data.s", ".rodata.s", ".bss.s")
DATA_SECTIONS = (".data", ".rodata")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "build/report.json",
        help="objdiff report JSON (default: build/report.json)",
    )
    parser.add_argument(
        "--progress",
        type=Path,
        default=ROOT / "build/progress.json",
        help="progress JSON output (default: build/progress.json)",
    )
    parser.add_argument(
        "--markdown",
        type=Path,
        default=ROOT / "PROGRESS.md",
        help="tracked progress table (default: PROGRESS.md)",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        default=ROOT / "build/baseline.json",
        help="progress baseline (default: build/baseline.json)",
    )
    parser.add_argument(
        "--asm-root",
        type=Path,
        default=ROOT / "asm",
        help="disassembled asm root (default: asm)",
    )
    parser.add_argument(
        "--asm-build-root",
        type=Path,
        default=ROOT / "build/asm",
        help="assembled target object root (default: build/asm)",
    )
    parser.add_argument(
        "--marked-root",
        type=Path,
        default=ROOT / "build/asm-marked",
        help="generated NON_MATCHING view (default: build/asm-marked)",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="write build/progress.json, build/asm-marked and PROGRESS.md",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify PROGRESS.md, asm-marked and baseline without writing",
    )
    parser.add_argument(
        "--print",
        dest="print_table",
        action="store_true",
        help="print the progress table",
    )
    parser.add_argument(
        "--incremental",
        action="store_true",
        help="reuse mtime cache for build/asm-marked",
    )
    parser.add_argument(
        "--full",
        action="store_true",
        help="ignore the mtime cache and regenerate everything",
    )
    parser.add_argument(
        "--no-markdown",
        action="store_true",
        help="do not write PROGRESS.md",
    )
    parser.add_argument(
        "--init-baseline",
        action="store_true",
        help="create build/baseline.json when it does not exist",
    )
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="overwrite build/baseline.json with the current results",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="only print warnings and errors",
    )
    return parser.parse_args()


def is_excluded_name(name: str) -> bool:
    return any(pattern.match(name) for pattern in EXCLUDED_NAME_PATTERNS)


def load_overrides(version: str, program: str) -> dict[str, str]:
    path = ROOT / "symbols" / version / f"{program}.match_overrides.txt"
    if not path.is_file():
        return {}

    overrides: dict[str, str] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line or "=" not in line:
            continue
        target, action = (part.strip() for part in line.split("=", 1))
        if action == "matched":
            overrides[target] = "matched"
        elif action in ("ignored", "excluded"):
            overrides[target] = "ignored"
    return overrides


def load_report(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def read_target_functions(path: Path) -> list[dict]:
    """Return executable symbols from a target object.

    objdiff treats sized STT_FUNC and STT_NOTYPE symbols in executable sections
    as functions.  Use the same rule so target-only units get the same
    denominator as report units.
    """

    functions: list[dict] = []
    with path.open("rb") as f:
        elf = ELFFile(f)
        symtab = elf.get_section_by_name(".symtab")
        if symtab is None:
            return functions

        for symbol in symtab.iter_symbols():
            name = symbol.name
            if not name or name.endswith(".NON_MATCHING"):
                continue
            if symbol["st_info"]["type"] not in ("STT_FUNC", "STT_NOTYPE"):
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
            if section is None or not (section["sh_flags"] & 0x4):
                continue
            functions.append(
                {
                    "name": name,
                    "size": size,
                    "address": str(symbol["st_value"]),
                    "section": section.name,
                }
            )
    return functions


def target_signature(functions: list[dict]) -> tuple:
    return tuple(
        sorted(
            (function["name"], function["size"], function["address"], function["section"])
            for function in functions
        )
    )


def read_target_sections(path: Path) -> dict[str, dict]:
    sections: dict[str, dict] = {}
    with path.open("rb") as f:
        elf = ELFFile(f)
        for name in DATA_SECTIONS:
            section = elf.get_section_by_name(name)
            if section is None:
                continue
            size = section["sh_size"]
            if size <= 0:
                continue
            digest = None
            if name != ".bss":
                digest = hashlib.sha1(section.data()).hexdigest()
            sections[name] = {"size": size, "digest": digest}
    return sections


def target_data_signature(sections: dict[str, dict]) -> tuple:
    return tuple(
        sorted(
            (name, value["size"], value.get("digest"))
            for name, value in sections.items()
        )
    )


def target_path_for_unit(
    version: str, program: str, rel: str, asm_build_root: Path
) -> Path:
    return asm_build_root / version / program / f"{rel}.o"


def classify_function(
    name: str,
    size: int,
    address: str | None,
    fuzzy: float | None,
    has_source: bool,
    action: str | None,
) -> dict:
    if action == "matched":
        matched = True
        reason = "override"
    elif not has_source:
        matched = False
        reason = "no-source"
    else:
        matched = fuzzy is not None and float(fuzzy) >= 100.0 - 1e-9
        reason = "matched" if matched else "unmatched"

    return {
        "name": name,
        "size": size,
        "address": address,
        "fuzzy_match_percent": fuzzy,
        "matched": matched,
        "reason": reason,
    }


def compute(report: dict, asm_build_root: Path) -> tuple[dict, dict]:
    units: list[dict] = []
    library_records: list[dict] = []
    matched_by_unit: dict[tuple[str, str, str], set[str]] = {}
    override_cache: dict[tuple[str, str], dict[str, str]] = {}
    report_target_paths: set[Path] = set()
    seen_signatures: dict[tuple[str, str], set[tuple]] = {}
    catalogs = {version: LibraryCatalog(version) for version in VERSIONS}
    library_names: set[str] = set()
    for catalog in catalogs.values():
        library_names.update(library for library, _module in catalog.unit_map.values())
        library_names.update(
            library for library, _module in catalog.function_map.values()
        )
    library_report_units: dict[tuple[str, str, str, str, str], dict] = {}
    library_defined_cache: dict[tuple[str, str, str], set[str]] = {}

    def overrides_for(version: str, program: str) -> dict[str, str]:
        key = (version, program)
        overrides = override_cache.get(key)
        if overrides is None:
            overrides = load_overrides(version, program)
            override_cache[key] = overrides
        return overrides

    def seen_for(version: str, program: str) -> set[tuple]:
        return seen_signatures.setdefault((version, program), set())

    def section_measures(
        target_sections: dict[str, dict], section_fuzzy: dict[str, float]
    ) -> dict[str, dict]:
        sections: dict[str, dict] = {}
        for section_name in DATA_SECTIONS:
            total = int(target_sections.get(section_name, {}).get("size", 0))
            fuzzy = float(section_fuzzy.get(section_name, 0.0))
            sections[section_name] = {
                "total": total,
                "matched": int(round(total * fuzzy / 100.0)),
            }
        return sections

    def function_measures(functions: list[dict]) -> tuple[int, int, int, int]:
        functions_total = len(functions)
        functions_matched = sum(1 for function in functions if function["matched"])
        code_total = sum(function["size"] for function in functions)
        code_matched = sum(
            function["size"] for function in functions if function["matched"]
        )
        return functions_total, functions_matched, code_total, code_matched

    def mark_matched(
        version: str, program: str, rel: str, functions: list[dict]
    ) -> None:
        key = (version, program, rel)
        matched = matched_by_unit.setdefault(key, set())
        matched.update(
            function["name"] for function in functions if function["matched"]
        )

    def add_program_unit(
        name: str,
        version: str,
        program: str,
        rel: str,
        source_path: str | None,
        auto_generated: bool,
        complete: bool,
        functions: list[dict],
        excluded_functions: int,
        target_path: Path | None,
        target_sections: dict[str, dict],
        section_fuzzy: dict[str, float],
    ) -> None:
        functions_total, functions_matched, code_total, code_matched = (
            function_measures(functions)
        )
        sections = section_measures(target_sections, section_fuzzy)
        mark_matched(version, program, rel, functions)

        units.append(
            {
                "name": name,
                "version": version,
                "program": program,
                "rel": rel,
                "source_path": source_path,
                "auto_generated": auto_generated,
                "complete": complete,
                "target_path": (
                    target_path.relative_to(ROOT).as_posix()
                    if target_path is not None and target_path.is_relative_to(ROOT)
                    else None
                ),
                "functions": functions_total,
                "matched_functions": functions_matched,
                "code": code_total,
                "matched_code": code_matched,
                "sections": sections,
                "excluded_functions": excluded_functions,
                "function_results": functions,
            }
        )

    def add_library_record(
        version: str,
        library: str,
        module: str,
        program: str,
        rel: str,
        functions: list[dict],
        target_sections: dict[str, dict],
        section_fuzzy: dict[str, float],
        target_path: Path | None,
    ) -> None:
        functions_total, functions_matched, code_total, code_matched = (
            function_measures(functions)
        )
        sections = section_measures(target_sections, section_fuzzy)
        mark_matched(version, program, rel, functions)

        library_records.append(
            {
                "name": f"{version}/{library}/{module}/{program}/{rel}",
                "version": version,
                "library": library,
                "module": module,
                "program": program,
                "rel": rel,
                "target_path": (
                    target_path.relative_to(ROOT).as_posix()
                    if target_path is not None and target_path.is_relative_to(ROOT)
                    else None
                ),
                "functions": functions_total,
                "matched_functions": functions_matched,
                "code": code_total,
                "matched_code": code_matched,
                "sections": sections,
                "function_results": functions,
            }
        )

    def add_library_groups(
        version: str,
        program: str,
        rel: str,
        grouped: dict[tuple[str, str], list[dict]],
        target_path: Path | None,
        target_sections: dict[str, dict],
        section_fuzzy_by_category: dict[tuple[str, str], dict[str, float]],
        dominant: tuple[str, str] | None,
    ) -> None:
        for category, functions in sorted(grouped.items()):
            library, module = category
            use_sections = category == dominant
            add_library_record(
                version,
                library,
                module,
                program,
                rel,
                functions,
                target_sections if use_sections else {},
                section_fuzzy_by_category.get(category, {}) if use_sections else {},
                target_path,
            )

    def library_defines(
        version: str, library: str, module: str, name: str
    ) -> bool:
        key = (version, library, module)
        defined = library_defined_cache.get(key)
        if defined is None:
            defined = set()
            base_path = library_base_path(version, library, module)
            if base_path is not None:
                defined = {
                    function["name"]
                    for function in read_target_functions(base_path)
                }
            library_defined_cache[key] = defined
        return name in defined

    def library_fuzzy(
        version: str, program: str, rel: str, category: tuple[str, str], name: str
    ) -> float | None:
        library, module = category
        if not library_defines(version, library, module, name):
            return None
        report_unit = library_report_units.get(
            (version, program, rel, library, module)
        )
        if report_unit is None:
            return None
        for function in report_unit.get("functions", []):
            if function.get("name") == name:
                fuzzy = function.get("fuzzy_match_percent")
                return float(fuzzy) if fuzzy is not None else None
        return None

    def classify_library_function(
        name: str,
        size: int,
        address: str | None,
        fuzzy: float | None,
        action: str | None,
    ) -> dict:
        if action == "matched":
            matched = True
            reason = "override"
        else:
            matched = fuzzy is not None and float(fuzzy) >= 100.0 - 1e-9
            reason = "matched" if matched else "unmatched"

        return {
            "name": name,
            "size": size,
            "address": address,
            "fuzzy_match_percent": fuzzy,
            "matched": matched,
            "reason": reason,
        }

    for unit in report.get("units", []):
        name = unit.get("name", "")
        metadata = unit.get("metadata", {})
        version = name.split("/", 1)[0]

        library_parts = name.split("/", 4)
        if len(library_parts) == 5 and library_parts[1] in library_names:
            version, library, module, target_program, target_rel = library_parts
            library_report_units[
                (version, target_program, target_rel, library, module)
            ] = unit
            continue

        if metadata.get("library"):
            target_program = metadata.get("target_program")
            target_rel = metadata.get("target_rel")
            library = metadata.get("library_name")
            module = metadata.get("library_module")
            if target_program and target_rel and library and module:
                library_report_units[
                    (version, target_program, target_rel, library, module)
                ] = unit
            continue

        parts = name.split("/", 2)
        if len(parts) != 3:
            continue
        version, program, rel = parts

        source_path = metadata.get("source_path")
        auto_generated = bool(metadata.get("auto_generated", source_path is None))
        complete = bool(metadata.get("complete", True))
        has_source = bool(source_path) and not auto_generated and complete

        target_path = target_path_for_unit(version, program, rel, asm_build_root)
        report_target_paths.add(target_path)
        target_sections: dict[str, dict] = {}
        if target_path.is_file():
            target_functions = read_target_functions(target_path)
            target_sections = read_target_sections(target_path)
            if target_functions:
                seen_for(version, program).add(
                    ("functions", target_signature(target_functions))
                )
            elif target_sections:
                seen_for(version, program).add(
                    ("data", target_data_signature(target_sections))
                )
        else:
            target_sections = {
                section.get("name", ""): {"size": int(section.get("size", "0"))}
                for section in unit.get("sections", [])
                if section.get("name") in DATA_SECTIONS
            }

        section_fuzzy = {
            section.get("name", ""): float(section.get("fuzzy_match_percent", 0.0))
            for section in unit.get("sections", [])
        }

        overrides = overrides_for(version, program)
        catalog = catalogs[version]
        program_functions: list[dict] = []
        library_functions: dict[tuple[str, str], list[dict]] = {}
        excluded_functions = 0

        for function in unit.get("functions", []):
            function_name = function.get("name", "")
            if not function_name:
                continue
            if function_name.endswith(".NON_MATCHING"):
                excluded_functions += 1
                continue
            if is_excluded_name(function_name):
                excluded_functions += 1
                continue

            action = overrides.get(function_name)
            if action == "ignored":
                excluded_functions += 1
                continue

            fuzzy = function.get("fuzzy_match_percent")
            category = catalog.category_for(program, rel, function_name)
            if category is not None:
                library_functions.setdefault(category, []).append(
                    classify_library_function(
                        function_name,
                        int(function.get("size", "0")),
                        function.get("address"),
                        fuzzy,
                        action,
                    )
                )
            else:
                program_functions.append(
                    classify_function(
                        function_name,
                        int(function.get("size", "0")),
                        function.get("address"),
                        fuzzy,
                        has_source,
                        action,
                    )
                )

        all_library = bool(library_functions) and not program_functions
        if all_library:
            dominant = max(
                library_functions,
                key=lambda category: sum(
                    function["size"] for function in library_functions[category]
                ),
            )
            add_library_groups(
                version,
                program,
                rel,
                library_functions,
                target_path,
                target_sections,
                {dominant: section_fuzzy},
                dominant,
            )
        else:
            if program_functions or not library_functions:
                add_program_unit(
                    name,
                    version,
                    program,
                    rel,
                    source_path,
                    auto_generated,
                    complete,
                    program_functions,
                    excluded_functions,
                    target_path,
                    target_sections,
                    section_fuzzy,
                )
            add_library_groups(
                version,
                program,
                rel,
                library_functions,
                target_path,
                {},
                {},
                None,
            )

    # Count target-only units as unmatched.  Report units are the source of
    # truth for matches, but the denominator must include every target
    # function, including files that have not been started yet.
    for version in VERSIONS:
        version_dir = asm_build_root / version
        if not version_dir.is_dir():
            continue
        catalog = catalogs[version]
        for program_dir in sorted(path for path in version_dir.iterdir() if path.is_dir()):
            program = program_dir.name
            for target_path in sorted(program_dir.rglob("*.o")):
                if target_path in report_target_paths:
                    continue

                target_functions = read_target_functions(target_path)
                target_sections = read_target_sections(target_path)
                if not target_functions and not target_sections:
                    continue

                if target_functions:
                    signature = ("functions", target_signature(target_functions))
                else:
                    signature = ("data", target_data_signature(target_sections))

                seen = seen_for(version, program)
                if signature in seen:
                    continue
                seen.add(signature)

                rel = target_path.relative_to(program_dir).with_suffix("").as_posix()
                overrides = overrides_for(version, program)
                unit_library = catalog.unit_category(program, rel)
                program_functions = []
                library_functions: dict[tuple[str, str], list[dict]] = {}
                excluded_functions = 0

                for function in target_functions:
                    function_name = function["name"]
                    if is_excluded_name(function_name):
                        excluded_functions += 1
                        continue

                    action = overrides.get(function_name)
                    if action == "ignored":
                        excluded_functions += 1
                        continue

                    category = catalog.category_for(program, rel, function_name)
                    if category is not None:
                        fuzzy = library_fuzzy(
                            version, program, rel, category, function_name
                        )
                        library_functions.setdefault(category, []).append(
                            classify_library_function(
                                function_name,
                                function["size"],
                                function["address"],
                                fuzzy,
                                action,
                            )
                        )
                    else:
                        program_functions.append(
                            classify_function(
                                function_name,
                                function["size"],
                                function["address"],
                                None,
                                False,
                                action,
                            )
                        )

                all_library = unit_library is not None or (
                    bool(target_functions) and not program_functions
                )

                if all_library:
                    if not library_functions:
                        continue
                    if unit_library is not None:
                        dominant = unit_library
                    else:
                        dominant = max(
                            library_functions,
                            key=lambda category: sum(
                                function["size"]
                                for function in library_functions[category]
                            ),
                        )
                    section_fuzzy_by_category = {}
                    for category in library_functions:
                        library, module = category
                        report_unit = library_report_units.get(
                            (version, program, rel, library, module)
                        )
                        if report_unit is None:
                            continue
                        section_fuzzy_by_category[category] = {
                            section.get("name", ""): float(
                                section.get("fuzzy_match_percent", 0.0)
                            )
                            for section in report_unit.get("sections", [])
                        }
                    add_library_groups(
                        version,
                        program,
                        rel,
                        library_functions,
                        target_path,
                        target_sections,
                        section_fuzzy_by_category,
                        dominant,
                    )
                    continue

                if library_functions:
                    add_library_groups(
                        version,
                        program,
                        rel,
                        library_functions,
                        target_path,
                        {},
                        {},
                        None,
                    )

                if rel.startswith("pad_") and not library_functions:
                    continue

                if not program_functions and not library_functions:
                    has_sections = any(
                        int(target_sections.get(section_name, {}).get("size", 0))
                        > 0
                        for section_name in DATA_SECTIONS
                    )
                    if not has_sections:
                        continue

                add_program_unit(
                    f"{version}/{program}/{rel}",
                    version,
                    program,
                    rel,
                    None,
                    True,
                    False,
                    program_functions,
                    excluded_functions,
                    target_path,
                    target_sections,
                    {},
                )

    def empty_measures() -> dict:
        return {
            "functions": 0,
            "matched_functions": 0,
            "code": 0,
            "matched_code": 0,
            "sections": {
                section_name: {"total": 0, "matched": 0}
                for section_name in DATA_SECTIONS
            },
            "excluded_functions": 0,
            "units": 0,
        }

    def add_measures(target: dict, unit: dict) -> None:
        target["functions"] += unit["functions"]
        target["matched_functions"] += unit["matched_functions"]
        target["code"] += unit["code"]
        target["matched_code"] += unit["matched_code"]
        target["excluded_functions"] += unit.get("excluded_functions", 0)
        target["units"] += 1
        for section_name in DATA_SECTIONS:
            target["sections"][section_name]["total"] += unit["sections"][section_name][
                "total"
            ]
            target["sections"][section_name]["matched"] += unit["sections"][
                section_name
            ]["matched"]

    programs: dict[str, dict] = {}
    libraries: dict[str, dict] = {}
    versions: dict[str, dict] = {}
    for unit in units:
        program_key = f"{unit['version']}/{unit['program']}"
        add_measures(programs.setdefault(program_key, empty_measures()), unit)
        add_measures(versions.setdefault(unit["version"], empty_measures()), unit)
    for record in library_records:
        library_key = f"{record['version']}/{record['library']}"
        add_measures(libraries.setdefault(library_key, empty_measures()), record)
        add_measures(versions.setdefault(record["version"], empty_measures()), record)

    totals = empty_measures()
    totals["units"] = 0
    for scope in (programs, libraries):
        for value in scope.values():
            totals["functions"] += value["functions"]
            totals["matched_functions"] += value["matched_functions"]
            totals["code"] += value["code"]
            totals["matched_code"] += value["matched_code"]
            totals["excluded_functions"] += value["excluded_functions"]
            totals["units"] += value["units"]
            for section_name in DATA_SECTIONS:
                totals["sections"][section_name]["total"] += value["sections"][
                    section_name
                ]["total"]
                totals["sections"][section_name]["matched"] += value["sections"][
                    section_name
                ]["matched"]

    result = {
        "schema_version": SCHEMA_VERSION,
        "versions": {key: versions[key] for key in sorted(versions)},
        "programs": {key: programs[key] for key in sorted(programs)},
        "libraries": {key: libraries[key] for key in sorted(libraries)},
        "totals": totals,
        "units": sorted(units, key=lambda unit: unit["name"]),
        "library_units": sorted(
            library_records, key=lambda record: record["name"]
        ),
    }
    return result, matched_by_unit

def percent(matched: int, total: int) -> str:
    if total <= 0:
        return "0.00%"
    return f"{matched * 100.0 / total:.2f}%"


def section_percent(measures: dict, section_name: str) -> str:
    section = measures["sections"][section_name]
    return percent(section["matched"], section["total"])


def render_markdown(result: dict) -> str:
    programs = result["programs"]
    libraries = result.get("libraries", {})
    versions = result["versions"]

    lines = [
        "# Progress",
        "",
        "| Version | Program | Functions | Matched | Code | .data | .rodata |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: |",
    ]

    def row(label_version: str, label_program: str, measures: dict) -> str:
        return (
            f"| {label_version} | {label_program} | {measures['functions']} | "
            f"{measures['matched_functions']} | "
            f"{percent(measures['matched_code'], measures['code'])} | "
            f"{section_percent(measures, '.data')} | "
            f"{section_percent(measures, '.rodata')} |"
        )

    for version in sorted(versions, reverse=True):
        for key in sorted(programs):
            program_version, program_name = key.split("/", 1)
            if program_version != version:
                continue
            lines.append(row(version, program_name, programs[key]))
        for key in sorted(libraries):
            library_version, library_name = key.split("/", 1)
            if library_version != version:
                continue
            lines.append(row(version, f"{library_name} (library)", libraries[key]))
        lines.append(row(version, "**subtotal**", versions[version]))

    lines.append(row("**all**", "", result["totals"]))
    lines.append("")
    lines.append("Percentages are matched byte percentages.")
    lines.append("")
    lines.append(
        "Library rows are statically linked library code found in target "
        "objects. They are counted separately from the program that embeds "
        "them; see `symbols/<version>/libraries.csv`."
    )
    lines.append("")
    return "\n".join(lines)


def unit_for_asm_file(rel_path: str) -> str:
    for suffix in MARKED_SUFFIXES:
        if rel_path.endswith(suffix):
            return rel_path[: -len(suffix)]
    return rel_path[:-2] if rel_path.endswith(".s") else rel_path


def filter_asm(text: str, matched_names: set[str]) -> str:
    lines = text.splitlines(keepends=True)
    kept: list[str] = []
    for line in lines:
        match = NONMATCHING_RE.match(line)
        if match is not None and match.group(1) in matched_names:
            continue
        kept.append(line)
    return "".join(kept)


def unit_digest(matched_names: set[str]) -> str:
    payload = "\n".join(sorted(matched_names)).encode("utf-8")
    return hashlib.sha1(payload).hexdigest()[:16]


def asm_files(asm_root: Path) -> list[tuple[str, str, str, Path]]:
    files: list[tuple[str, str, str, Path]] = []
    if not asm_root.is_dir():
        return files

    for version_dir in sorted(path for path in asm_root.iterdir() if path.is_dir()):
        version = version_dir.name
        if version not in VERSIONS:
            continue
        for program_dir in sorted(path for path in version_dir.iterdir() if path.is_dir()):
            program = program_dir.name
            if program == "functions":
                continue
            for source in sorted(program_dir.rglob("*.s")):
                rel_path = source.relative_to(program_dir).as_posix()
                files.append((version, program, rel_path, source))
    return files


def write_if_changed(path: Path, content: str) -> bool:
    if path.is_file():
        try:
            if path.read_text(encoding="utf-8") == content:
                return False
        except UnicodeDecodeError:
            pass
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return True


def build_marked(
    files: list[tuple[str, str, str, Path]],
    matched_by_unit: dict[tuple[str, str, str], set[str]],
    marked_root: Path,
    old_cache: dict,
    incremental: bool,
    write: bool,
) -> tuple[dict, list[str]]:
    cache: dict[str, dict] = {}
    errors: list[str] = []
    expected_paths: set[Path] = set()

    for version, program, rel_path, source in files:
        unit_rel = unit_for_asm_file(rel_path)
        matched_names = matched_by_unit.get((version, program, unit_rel), set())
        digest = unit_digest(matched_names)

        output = marked_root / version / program / rel_path
        expected_paths.add(output)
        key = output.relative_to(ROOT).as_posix()

        stat = source.stat()
        cached = old_cache.get(key) if incremental else None
        if (
            cached is not None
            and cached.get("source_mtime_ns") == stat.st_mtime_ns
            and cached.get("source_size") == stat.st_size
            and cached.get("digest") == digest
            and output.is_file()
        ):
            cache[key] = cached
            continue

        text = source.read_text(encoding="utf-8")
        filtered = filter_asm(text, matched_names)

        if write:
            write_if_changed(output, filtered)
        elif not output.is_file() or output.read_text(encoding="utf-8") != filtered:
            errors.append(f"{key}: generated NON_MATCHING view is stale")

        cache[key] = {
            "source": source.relative_to(ROOT).as_posix(),
            "source_mtime_ns": stat.st_mtime_ns,
            "source_size": stat.st_size,
            "digest": digest,
        }

    if write:
        for stale in sorted(marked_root.rglob("*.s")):
            if stale not in expected_paths:
                stale.unlink()
    elif marked_root.is_dir():
        for stale in sorted(marked_root.rglob("*.s")):
            if stale not in expected_paths:
                errors.append(
                    f"{stale.relative_to(ROOT).as_posix()}: stale generated file"
                )

    return cache, errors


def baseline_measures(value: dict) -> dict:
    return {
        "functions": value["functions"],
        "matched_functions": value["matched_functions"],
        "code": value["code"],
        "matched_code": value["matched_code"],
        "sections": {
            section_name: {
                "total": value["sections"][section_name]["total"],
                "matched": value["sections"][section_name]["matched"],
            }
            for section_name in DATA_SECTIONS
        },
    }


def baseline_from_result(result: dict) -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "versions": {
            key: baseline_measures(value)
            for key, value in sorted(result["versions"].items())
        },
        "programs": {
            key: baseline_measures(value)
            for key, value in sorted(result["programs"].items())
        },
        "libraries": {
            key: baseline_measures(value)
            for key, value in sorted(result.get("libraries", {}).items())
        },
        "totals": baseline_measures(result["totals"]),
    }


def compare_baseline(result: dict, baseline: dict) -> list[str]:
    failures: list[str] = []
    current = baseline_from_result(result)

    for scope in ("programs", "libraries", "versions", "totals"):
        old_scope = baseline.get(scope, {})
        new_scope = current[scope]
        if scope == "totals":
            old_items = {"totals": old_scope}
            new_items = {"totals": new_scope}
        else:
            old_items = old_scope
            new_items = new_scope

        for key, new in new_items.items():
            old = old_items.get(key)
            if old is None:
                continue
            if new["matched_functions"] < old["matched_functions"]:
                failures.append(
                    f"{scope}:{key}: matched functions decreased "
                    f"{old['matched_functions']} -> {new['matched_functions']}"
                )
            if new["matched_code"] < old["matched_code"]:
                failures.append(
                    f"{scope}:{key}: matched code decreased "
                    f"{old['matched_code']} -> {new['matched_code']}"
                )
            old_sections = old.get("sections", {})
            new_sections = new.get("sections", {})
            for section_name in DATA_SECTIONS:
                old_section = old_sections.get(section_name)
                new_section = new_sections.get(section_name)
                if old_section is None or new_section is None:
                    continue
                if new_section["matched"] < old_section["matched"]:
                    failures.append(
                        f"{scope}:{key}: {section_name} matched bytes decreased "
                        f"{old_section['matched']} -> {new_section['matched']}"
                    )

    return failures


def main() -> int:
    args = parse_args()

    if not args.report.is_file():
        print(f"error: report not found: {args.report}", file=sys.stderr)
        return 2

    report = load_report(args.report)
    result, matched_by_unit = compute(report, args.asm_build_root)

    progress_path = args.progress
    if progress_path.is_file():
        try:
            with progress_path.open("r", encoding="utf-8") as f:
                old_progress = json.load(f)
        except (OSError, json.JSONDecodeError):
            old_progress = {}
    else:
        old_progress = {}

    use_incremental = args.incremental and not args.full and not args.check
    old_cache = old_progress.get("asm_marked", {}) if use_incremental else {}

    files = asm_files(args.asm_root)
    marked_cache, marked_errors = build_marked(
        files,
        matched_by_unit,
        args.marked_root,
        old_cache,
        incremental=use_incremental,
        write=args.write and not args.check,
    )

    result["asm_marked"] = marked_cache
    markdown = render_markdown(result)

    if args.print_table:
        print(markdown)

    if args.write and not args.check:
        progress_json = json.dumps(result, indent=2) + "\n"
        progress_changed = write_if_changed(progress_path, progress_json)
        if args.no_markdown:
            markdown_changed = False
        else:
            markdown_changed = write_if_changed(args.markdown, markdown)

        if args.write_baseline or (args.init_baseline and not args.baseline.is_file()):
            baseline = baseline_from_result(result)
            write_if_changed(args.baseline, json.dumps(baseline, indent=2) + "\n")

        if not args.quiet:
            totals = result["totals"]
            print(
                f"{totals['matched_functions']}/{totals['functions']} functions "
                f"matched ({percent(totals['matched_functions'], totals['functions'])}), "
                f"{percent(totals['matched_code'], totals['code'])} of code; "
                f"{len(result['units'])} units"
            )
            if progress_changed:
                print(f"Wrote {progress_path}")
            if markdown_changed:
                print(f"Wrote {args.markdown}")
        return 0

    if not args.check:
        return 0

    failures = list(marked_errors)

    if not args.markdown.is_file():
        failures.append(f"{args.markdown}: missing (run make match)")
    else:
        actual_markdown = args.markdown.read_text(encoding="utf-8")
        if actual_markdown != markdown:
            failures.append(f"{args.markdown}: stale (run make match)")

    if not args.baseline.is_file():
        failures.append(
            f"{args.baseline}: missing (run make match once to initialize it)"
        )
    else:
        try:
            with args.baseline.open("r", encoding="utf-8") as f:
                baseline = json.load(f)
        except (OSError, json.JSONDecodeError) as exc:
            failures.append(f"{args.baseline}: cannot read baseline: {exc}")
        else:
            failures.extend(compare_baseline(result, baseline))

    if failures:
        for failure in failures:
            print(f"error: {failure}", file=sys.stderr)
        return 1

    totals = result["totals"]
    if not args.quiet:
        print(
            f"check passed: {totals['matched_functions']}/{totals['functions']} "
            f"functions matched ({percent(totals['matched_functions'], totals['functions'])}), "
            f"{percent(totals['matched_code'], totals['code'])} of code"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
