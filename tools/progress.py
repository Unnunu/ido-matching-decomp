#!/usr/bin/env python3
"""Compute matching progress from an objdiff report.

The objdiff report is the source of truth for matches: a function is matched
only when objdiff reports a 100% fuzzy match.  Target objects without a base
object are still counted as unmatched so unstarted source files stay in the
denominator.  Exclusions and per-program overrides are applied without
modifying the generated objdiff data.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
from typing import NamedTuple

from elftools.elf.elffile import ELFFile

from library import LibraryCatalog, library_base_path

ROOT = Path(__file__).resolve().parent.parent
REPORT = ROOT / "build/report.json"
MARKDOWN = ROOT / "PROGRESS.md"
ASM_BUILD_ROOT = ROOT / "build/asm"

VERSIONS = ("5.3", "7.1")

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

DATA_SECTIONS = (".data", ".rodata")


class ElfData(NamedTuple):
    functions: list[dict]
    sections: dict[str, dict]
    text: bytes
    text_ranges: list[tuple[int, int]]


@lru_cache(maxsize=None)
def read_elf(path: Path) -> ElfData:
    """Read all ELF data needed by progress in one pass."""

    functions: list[dict] = []
    sections: dict[str, dict] = {}
    text = b""

    with path.open("rb") as f:
        elf = ELFFile(f)

        symtab = elf.get_section_by_name(".symtab")
        if symtab is not None:
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

        text_section = elf.get_section_by_name(".text")
        if text_section is not None:
            text = text_section.data()

        for name in DATA_SECTIONS:
            section = elf.get_section_by_name(name)
            if section is None:
                continue
            size = section["sh_size"]
            if size <= 0:
                continue
            sections[name] = {
                "size": size,
                "digest": hashlib.sha1(section.data()).hexdigest(),
            }

    text_ranges = [
        (int(function["address"]), int(function["address"]) + function["size"])
        for function in functions
        if function["section"] == ".text"
    ]
    return ElfData(functions, sections, text, text_ranges)


def is_excluded_name(name: str) -> bool:
    return any(pattern.match(name) for pattern in EXCLUDED_NAME_PATTERNS)


def is_excluded_unit(rel: str) -> bool:
    return is_excluded_name(Path(rel).name)


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


def load_symbol_mappings() -> dict[str, dict[str, str]]:
    path = ROOT / "objdiff.json"
    if not path.is_file():
        return {}
    try:
        with path.open("r", encoding="utf-8") as f:
            config = json.load(f)
    except (OSError, json.JSONDecodeError):
        return {}
    return {
        unit.get("name", ""): unit.get("symbol_mappings", {})
        for unit in config.get("units", [])
        if unit.get("name")
    }


def target_signature(functions: list[dict]) -> tuple:
    return tuple(
        sorted(
            (function["name"], function["size"], function["address"], function["section"])
            for function in functions
        )
    )


def target_data_signature(sections: dict[str, dict]) -> tuple:
    return tuple(
        sorted(
            (name, value["size"], value.get("digest"))
            for name, value in sections.items()
        )
    )


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


def section_fuzzy_by_name(unit: dict) -> dict[str, float]:
    return {
        section.get("name", ""): float(section.get("fuzzy_match_percent", 0.0))
        for section in unit.get("sections", [])
    }


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


def unit_measures(
    functions: list[dict],
    target_sections: dict[str, dict],
    section_fuzzy: dict[str, float],
    excluded_functions: int = 0,
) -> dict:
    functions_total, functions_matched, code_total, code_matched = (
        function_measures(functions)
    )
    return {
        "functions": functions_total,
        "matched_functions": functions_matched,
        "code": code_total,
        "matched_code": code_matched,
        "sections": section_measures(target_sections, section_fuzzy),
        "excluded_functions": excluded_functions,
        "units": 1,
    }


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


def compute(report: dict, asm_build_root: Path) -> tuple[dict, list[str]]:
    programs: dict[str, dict] = {}
    libraries: dict[str, dict] = {}
    versions: dict[str, dict] = {}
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
    library_base_cache: dict[tuple[str, str, str], Path | None] = {}
    known_rels: dict[str, dict[str, set[str]]] = defaultdict(
        lambda: defaultdict(set)
    )
    known_functions: dict[str, dict[str, set[str]]] = defaultdict(
        lambda: defaultdict(set)
    )

    def overrides_for(version: str, program: str) -> dict[str, str]:
        key = (version, program)
        overrides = override_cache.get(key)
        if overrides is None:
            overrides = load_overrides(version, program)
            override_cache[key] = overrides
        return overrides

    def seen_for(version: str, program: str) -> set[tuple]:
        return seen_signatures.setdefault((version, program), set())

    def library_base(
        version: str, library: str, module: str
    ) -> Path | None:
        key = (version, library, module)
        if key not in library_base_cache:
            library_base_cache[key] = library_base_path(version, library, module)
        return library_base_cache[key]

    def add_program_measures(
        version: str,
        program: str,
        functions: list[dict],
        excluded_functions: int,
        target_sections: dict[str, dict],
        section_fuzzy: dict[str, float],
    ) -> None:
        measures = unit_measures(
            functions, target_sections, section_fuzzy, excluded_functions
        )
        add_measures(
            programs.setdefault(f"{version}/{program}", empty_measures()), measures
        )
        add_measures(versions.setdefault(version, empty_measures()), measures)

    def add_library_measures(
        version: str,
        library: str,
        functions: list[dict],
        target_sections: dict[str, dict],
        section_fuzzy: dict[str, float],
    ) -> None:
        measures = unit_measures(functions, target_sections, section_fuzzy)
        add_measures(
            libraries.setdefault(f"{version}/{library}", empty_measures()), measures
        )
        add_measures(versions.setdefault(version, empty_measures()), measures)

    def add_library_groups(
        version: str,
        grouped: dict[tuple[str, str], list[dict]],
        target_sections: dict[str, dict],
        section_fuzzy_by_category: dict[tuple[str, str], dict[str, float]],
        dominant: tuple[str, str] | None,
    ) -> None:
        for category, functions in sorted(grouped.items()):
            library, _module = category
            use_sections = category == dominant
            add_library_measures(
                version,
                library,
                functions,
                target_sections if use_sections else {},
                section_fuzzy_by_category.get(category, {}) if use_sections else {},
            )

    def library_defines(
        version: str, library: str, module: str, name: str
    ) -> bool:
        key = (version, library, module)
        defined = library_defined_cache.get(key)
        if defined is None:
            defined = set()
            base_path = library_base(version, library, module)
            if base_path is not None:
                defined = {
                    function["name"] for function in read_elf(base_path).functions
                }
            library_defined_cache[key] = defined
        return name in defined

    def library_has_anonymous_code(
        version: str,
        category: tuple[str, str],
        target_path: Path | None,
        address: str | None,
        size: int,
    ) -> bool:
        if target_path is None or address is None or size <= 0:
            return False
        library, module = category
        base_path = library_base(version, library, module)
        if base_path is None:
            return False
        try:
            start = int(address)
        except (TypeError, ValueError):
            return False
        end = start + size
        base_elf = read_elf(base_path)
        target_elf = read_elf(target_path)
        if start < 0 or end > len(base_elf.text) or end > len(target_elf.text):
            return False
        if base_elf.text[start:end] != target_elf.text[start:end]:
            return False
        return not any(
            low <= start and end <= high for low, high in base_elf.text_ranges
        )

    def library_fuzzy(
        version: str,
        program: str,
        rel: str,
        category: tuple[str, str],
        function: dict,
        target_path: Path | None,
    ) -> float | None:
        library, module = category
        name = function.get("name", "")
        if not (
            library_defines(version, library, module, name)
            or library_has_anonymous_code(
                version,
                category,
                target_path,
                function.get("address"),
                int(function.get("size", 0)),
            )
        ):
            return None
        report_unit = library_report_units.get(
            (version, program, rel, library, module)
        )
        if report_unit is None:
            return None
        for report_function in report_unit.get("functions", []):
            if report_function.get("name") == name:
                fuzzy = report_function.get("fuzzy_match_percent")
                return float(fuzzy) if fuzzy is not None else None
        return None

    def library_report_key(name: str, metadata: dict) -> tuple[str, str, str, str, str] | None:
        parts = name.split("/", 4)
        if len(parts) == 5 and parts[1] in library_names:
            version, library, module, target_program, target_rel = parts
            return (version, target_program, target_rel, library, module)

        if not metadata.get("library"):
            return None
        target_program = metadata.get("target_program")
        target_rel = metadata.get("target_rel")
        library = metadata.get("library_name")
        module = metadata.get("library_module")
        if not (target_program and target_rel and library and module):
            return None
        version = name.split("/", 1)[0]
        return (version, target_program, target_rel, library, module)

    def is_library_report_unit(name: str, metadata: dict) -> bool:
        parts = name.split("/", 4)
        return (len(parts) == 5 and parts[1] in library_names) or bool(
            metadata.get("library")
        )

    report_units = report.get("units", [])
    symbol_mappings = load_symbol_mappings()

    for unit in report_units:
        key = library_report_key(
            unit.get("name", ""), unit.get("metadata", {})
        )
        if key is not None:
            library_report_units[key] = unit

    for unit in report_units:
        name = unit.get("name", "")
        metadata = unit.get("metadata", {})
        if is_library_report_unit(name, metadata):
            continue

        parts = name.split("/", 2)
        if len(parts) != 3:
            continue
        version, program, rel = parts
        if is_excluded_unit(rel):
            continue

        source_path = metadata.get("source_path")
        auto_generated = bool(metadata.get("auto_generated", source_path is None))
        complete = bool(metadata.get("complete", True))
        has_source = bool(source_path) and not auto_generated and complete

        target_path = asm_build_root / version / program / f"{rel}.o"
        report_target_paths.add(target_path)
        known_rels[version][program].add(rel)
        base_path = asm_build_root.parent / "src" / version / program / f"{rel}.o"
        base_function_names: set[str] | None = None
        if base_path.is_file():
            base_function_names = {
                function["name"] for function in read_elf(base_path).functions
            }

        target_functions: list[dict] = []
        target_sections: dict[str, dict] = {}
        if target_path.is_file():
            target_elf = read_elf(target_path)
            target_functions = target_elf.functions
            known_functions[version][program].update(
                function["name"] for function in target_functions
            )
            target_sections = target_elf.sections
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

        section_fuzzy = section_fuzzy_by_name(unit)
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

            category = catalog.category_for(program, rel, function_name)
            if category is not None:
                library_functions.setdefault(category, []).append(
                    classify_function(
                        function_name,
                        int(function.get("size", "0")),
                        function.get("address"),
                        library_fuzzy(
                            version,
                            program,
                            rel,
                            category,
                            function,
                            target_path,
                        ),
                        True,
                        action,
                    )
                )
            else:
                result = classify_function(
                    function_name,
                    int(function.get("size", "0")),
                    function.get("address"),
                    function.get("fuzzy_match_percent"),
                    has_source,
                    action,
                )
                mapped_base_name = symbol_mappings.get(name, {}).get(result["name"])
                if (
                    result["matched"]
                    and has_source
                    and base_function_names is not None
                    and result["name"] not in base_function_names
                    and mapped_base_name not in base_function_names
                ):
                    result["matched"] = False
                    result["reason"] = "no-base"
                program_functions.append(result)

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
                library_functions,
                target_sections,
                {dominant: section_fuzzy},
                dominant,
            )
        else:
            if program_functions or not library_functions:
                add_program_measures(
                    version,
                    program,
                    program_functions,
                    excluded_functions,
                    target_sections,
                    section_fuzzy,
                )
            add_library_groups(
                version,
                library_functions,
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

                rel = target_path.relative_to(program_dir).with_suffix("").as_posix()
                if is_excluded_unit(rel):
                    continue
                known_rels[version][program].add(rel)

                target_elf = read_elf(target_path)
                target_functions = target_elf.functions
                target_sections = target_elf.sections
                known_functions[version][program].update(
                    function["name"] for function in target_functions
                )
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
                        library_functions.setdefault(category, []).append(
                            classify_function(
                                function_name,
                                function["size"],
                                function["address"],
                                library_fuzzy(
                                    version,
                                    program,
                                    rel,
                                    category,
                                    function,
                                    target_path,
                                ),
                                True,
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
                        if unit_library is not None:
                            library, module = unit_library
                            section_fuzzy = {}
                            report_unit = library_report_units.get(
                                (version, program, rel, library, module)
                            )
                            if report_unit is not None:
                                section_fuzzy = section_fuzzy_by_name(report_unit)
                            if any(
                                int(target_sections.get(section_name, {}).get("size", 0))
                                > 0
                                for section_name in DATA_SECTIONS
                            ):
                                add_library_measures(
                                    version,
                                    library,
                                    [],
                                    target_sections,
                                    section_fuzzy,
                                )
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
                        section_fuzzy_by_category[category] = section_fuzzy_by_name(
                            report_unit
                        )
                    add_library_groups(
                        version,
                        library_functions,
                        target_sections,
                        section_fuzzy_by_category,
                        dominant,
                    )
                    continue

                if library_functions:
                    add_library_groups(
                        version,
                        library_functions,
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

                add_program_measures(
                    version,
                    program,
                    program_functions,
                    excluded_functions,
                    target_sections,
                    {},
                )

    annotation_problems: list[str] = []
    for version, catalog in catalogs.items():
        version_rels = known_rels.get(version, {})
        version_functions = known_functions.get(version, {})
        if not version_rels:
            continue
        for (program, rel), (library, module) in sorted(catalog.unit_map.items()):
            if rel not in version_rels.get(program, set()):
                annotation_problems.append(
                    f"{version}: unit annotation {program}/{rel} "
                    f"({library}/{module}) does not match any target object"
                )
        for (program, name), (library, module) in sorted(
            catalog.function_map.items()
        ):
            if name not in version_functions.get(program, set()):
                annotation_problems.append(
                    f"{version}: function annotation {program}:{name} "
                    f"({library}/{module}) does not match any target function"
                )

    totals = empty_measures()
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
        "versions": {key: versions[key] for key in sorted(versions)},
        "programs": {key: programs[key] for key in sorted(programs)},
        "libraries": {key: libraries[key] for key in sorted(libraries)},
        "totals": totals,
    }
    return result, annotation_problems


def percent(matched: int, total: int) -> str:
    if total <= 0:
        return "0.00%"
    return f"{matched * 100.0 / total:.2f}%"


def section_percent(measures: dict, section_name: str) -> str:
    section = measures["sections"][section_name]
    return percent(section["matched"], section["total"])


def render_markdown(result: dict) -> str:
    programs = result["programs"]
    libraries = result["libraries"]
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


def main() -> int:
    if not REPORT.is_file():
        print(f"error: report not found: {REPORT}", file=sys.stderr)
        return 2

    report = load_report(REPORT)
    result, annotation_problems = compute(report, ASM_BUILD_ROOT)
    for problem in annotation_problems:
        print(f"error: stale library annotation: {problem}", file=sys.stderr)
    if annotation_problems:
        return 1

    markdown = render_markdown(result)
    markdown_changed = write_if_changed(MARKDOWN, markdown)

    totals = result["totals"]
    function_units = sum(
        program["units"] for program in result["programs"].values()
    )
    print(
        f"{totals['matched_functions']}/{totals['functions']} functions "
        f"matched ({percent(totals['matched_functions'], totals['functions'])}), "
        f"{percent(totals['matched_code'], totals['code'])} of code; "
        f"{function_units} units"
    )
    if markdown_changed:
        print(f"Wrote {MARKDOWN}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
