"""Library membership annotations for target objects.

The split CSVs describe where target code and data live, but a split object can
contain code from both a program and a statically linked library.  Library
membership is therefore tracked per target unit and per function in
``symbols/<version>/libraries.csv``.

File format (comma separated, one annotation per line)::

    # kind,program,target,library,module
    unit,ugen,ugen_04F430,libu,uini
    function,ugen,uputinit,libu,ucio

``kind=unit`` marks every function in ``<program>/<target>`` as library code.
``kind=function`` marks one function name in that program.  Function rows take
precedence over unit rows.  Anything not listed stays program code.

Library categories currently used:

    libu    src/libu (uini, bwri, ucio, bread, uscan)
    libp    src/libp (textoutput, Pascal runtime helpers)
    libmld  SGI libmld; src/mld is the source folder for sex.c, while the
            rest of libmld (st_*, swap_*, ldf*) has no source yet
    libelf  SGI libelf (elf_*, _elf_*)
    libc    C runtime helpers (memmove, ...)

Only libu/libp/libmld have source and built base objects today.  Other library
categories are still counted, but as unmatched until a base object exists.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERSIONS = ("5.3", "7.1")

LIBRARY_BASE_DIRS = {"libu": "libu", "libp": "libp", "libmld": "mld"}
SOURCE_EXTS = (".c", ".p")


class LibraryCatalog:
    def __init__(self, version: str, root: Path = ROOT) -> None:
        self.version = version
        self.root = root
        self.unit_map: dict[tuple[str, str], tuple[str, str]] = {}
        self.function_map: dict[tuple[str, str], tuple[str, str]] = {}
        self._load()

    def _load(self) -> None:
        path = self.root / "symbols" / self.version / "libraries.csv"
        if not path.is_file():
            return

        for raw_line in path.read_text(encoding="utf-8").splitlines():
            line = raw_line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = [part.strip() for part in line.split(",")]
            if len(parts) != 5:
                continue
            kind, program, target, library, module = parts
            if not kind or not program or not target or not library:
                continue
            category = (library, module or library)
            if kind == "unit":
                self.unit_map[(program, target)] = category
            elif kind == "function":
                self.function_map[(program, target)] = category

    def unit_category(self, program: str, rel: str) -> tuple[str, str] | None:
        return self.unit_map.get((program, rel))

    def function_category(self, program: str, name: str) -> tuple[str, str] | None:
        return self.function_map.get((program, name))

    def category_for(
        self, program: str, rel: str, name: str
    ) -> tuple[str, str] | None:
        return self.function_category(program, name) or self.unit_category(
            program, rel
        )


def library_base_path(
    version: str, library: str, module: str, root: Path = ROOT
) -> Path | None:
    directory = LIBRARY_BASE_DIRS.get(library)
    if directory is None:
        return None
    path = root / "build" / "src" / version / directory / f"{module}.o"
    return path if path.is_file() else None


def library_source_path(
    version: str, library: str, module: str, root: Path = ROOT
) -> Path | None:
    directory = LIBRARY_BASE_DIRS.get(library)
    if directory is None:
        return None
    for ext in SOURCE_EXTS:
        path = root / "src" / directory / f"{module}{ext}"
        if path.is_file():
            return path
    return None


def library_category_id(version: str, library: str) -> str:
    return f"{version}/{library}"


def library_category_name(version: str, library: str) -> str:
    return f"{version} / {library} (library)"
