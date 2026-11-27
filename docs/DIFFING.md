# Diffing with objdiff

`objdiff.json` is generated locally from the build tree and is ignored by git.
It contains one unit per target/base object pair for both IDO versions.

## Setup

```bash
make setup
make disasm-all
make both
make objdiff
```

`make objdiff` regenerates `objdiff.json` for 5.3 and 7.1 and builds any stale
objects first (`objdiff` depends on `build`).

## Automatic rebuilds

`objdiff.json` sets `build_base: true` and configures
`tools/objdiff_make.py` as `custom_make`. The wrapper reads the version from
the object path and runs `make VERSION=<version> <object>`:

- In the GUI, the **Build** button and the on-save watcher rebuild the selected
  unit's base object and re-run the diff.
- `make diff` rebuilds stale objects and regenerates `objdiff.json` before
  invoking `objdiff-cli`.

`objdiff-cli diff` itself never builds; it always reads the existing `.o`
files. Use `make diff` for the automatic path, or run `make both`/`make
objdiff` first when calling `objdiff-cli` directly.

## Units

Program units are named `<version>/<program>/<file>`, for example:

```text
7.1/ugen/build
target_path = build/asm/7.1/ugen/build.o
base_path   = build/src/7.1/ugen/build.o
```

Library units are named `<version>/<library>/<program>/<file>`; see
[Libraries embedded in program targets](#libraries-embedded-in-program-targets).

`metadata.source_path` points at the C or Pascal source when it can be found.
Targets without a built base object are skipped by default. Pass
`--include-missing-base` to `tools/gen_objdiff.py` to emit them with
`metadata.complete: false`.

## Libraries embedded in program targets

IDO binaries statically link libraries such as `libu`, `libp`, `libmld`,
`libelf` and the Pascal runtime. Their functions are part of target objects but
are not program code, so they must not inflate a program's unstarted count.

Library membership is encoded in the split names themselves. A row named
`library/member` is library code, while a plain name is program code:

```text
offset,vram,.text
067250,00467250,libu/ucio
```

- The split CSVs are the single source of truth; there is no separate
  `libraries.csv`.
- `.text`, `.data` and `.rodata` rows all use the same `library/member` form.
  Gaps between library members are named `pad_<address>` and stay program code.
- A data-only library member has only `.data`/`.rodata` rows, with no `.text`
  row. Ownership comes from target symbols and references from the generated
  assembly, not from archive sizes.
- Names without `/` keep their program meaning. Continuations of a repeated
  program name get a `_2`, `_3`, ... suffix.

`tools/gen_objdiff.py` emits library units only for members that have both a
source and a built base object (`libu`, `libp`, `libmld`). Source and build
folders match the library name (`src/libmld`,
`build/src/<version>/libmld`):

```text
7.1/libu/ugen/uini
target_path = build/asm/7.1/ugen/libu/uini.o
base_path = build/src/7.1/libu/uini.o
metadata.library_name = libu
metadata.library_module = uini
metadata.target_program = ugen
metadata.target_rel = libu/uini
```

Library units live at `<version>/<library>/<program>/<member>`, not under the
program branch. Members without source or without a target object are not
emitted. These units exist for diffing and for objdiff fuzzy results. Progress
skips them as program units and uses their per-function results to score the
library bucket. Parts of `libmld` without a base object (`st_*`, `swap_*`,
`ldf*`), plus `libelf`, `libc` and the Pascal runtime, are counted as unmatched
library code.

## Symbol mappings

Target assembly often uses names such as `func_0040E238`, while the source uses
meaningful names. `tools/gen_objdiff.py` reads both ELF symbol tables and maps
target symbols to base symbols with the same section, offset, and size.

Offset pairing is only meaningful when the target and base section layouts are
aligned. If most same-named symbols sit at different offsets on the two sides
(the target has a different global set or declaration order), the generator
treats the section as misaligned and emits no mappings for it. This prevents
meaningless pairs such as `Fflag -> Kflag` in `5.3/cc/cc`, where the base `.data`
is shifted relative to the target. A section needs at least 8 common names
before this check applies. Explicit `matched` overrides still work for
misaligned sections.

The mapping direction is **target -> base**:

```json
"symbol_mappings": {
  "add_restricted_reg": "restricted_reg"
}
```

Symbols ending in `.NON_MATCHING` are ignored. Optional overrides live in
`symbols/<version>/<program>.match_overrides.txt`.

## Base symbol mirroring

The IDO compiler does not always emit names for local data and static
functions. spimdisasm, however, names the matching target symbols
`RO_STR_...`, `D_...`, `func_...`, and so on. If the base object has no such
symbols, objdiff cannot pair them: the whole base `.rodata` or `.data` section
is compared against a synthetic target blob. This can produce misleading
section scores. Before these fixes, `7.1/cfe/error` reported `.rodata` at 97.2%
even though all 352 bytes were identical, because objdiff matched 333 bytes and
treated the other 19 as an insertion.

`tools/symbolize_base.py` copies missing target symbols into the base object's
`.symtab` with the same section, offset and size. It mirrors all missing local
symbols, plus global target data symbols when the base has no name for that
range. The latter covers static data that the compiler left unnamed in the base
even though its bytes are present; for example, `7.1/ugen/release_id` has a
global `__Release_ID` in the target and only an anonymous `.rodata` section in
the base. Without the name objdiff drops the whole data section from the report
even when all 96 bytes are identical. It does not modify section contents or
relocations. `tools/gen_objdiff.py` runs it for regular units, and
`tools/objdiff_make.py` runs it after GUI-triggered rebuilds. Library units get
only the `.mdebug` repair, because their base object may be shared by several
targets.

## Source names from .mdebug

IDO records names for local source symbols in `.mdebug` even when it omits them
from `.symtab`. `tools/mdebug.py` reads procedure names (`ST_PROC` /
`ST_STATICPROC`) and local data names (`ST_STATIC` / `ST_GLOBAL` / `ST_CONST`).
`tools/symbolize_base.py` prefers these names for local functions and
`.data`/`.rodata` objects instead of the target's `func_...` / `D_...` names.
Public functions and globals already carry their source names in `.symtab`.

When a source name replaces a mirrored target name, `tools/gen_objdiff.py`
emits a `target -> source` symbol mapping, so objdiff still pairs the function
while the right column shows the C/Pascal name. Duplicate or conflicting
source names fall back to the target name. String literals, jump tables and
compiler-generated BSS labels have no source identifier, so they keep names
such as `RO_STR_...`, `jtbl_...` and `B_...`. `tools/progress.py` consults
`objdiff.json` mappings when checking that a matched function has a base
symbol.

## Source line numbers

IDO includes line info in `.mdebug` by default; `-g` is not required. Enabling
`-g` or `-g3` changes code generation and breaks matching. Two issues prevented
objdiff 3.8.3 from using the existing line info:

- `objcopy --add-symbol` moves `.mdebug` but leaves the header offsets pointing
  at the old file positions.
- objdiff assumes `ST_END.value` is an absolute end address, while IDO stores
  the function size.

`tools/mdebug.py` repairs both before objdiff reads the object: it normalizes
the header offsets to section-relative values and rewrites `ST_END.value` to
`start + size`. The operation is idempotent and changes only debug metadata.
It is run for regular units through `symbolize_base.py`, for library units in
`gen_objdiff.py`, and after GUI rebuilds in `objdiff_make.py`. objdiff then
shows source line numbers automatically; no extra configuration is needed and
objdiff itself is not patched. Target assembly objects have no source line
info, so lines appear on the base side only.

## BSS labels

BSS labels get the same treatment. spimdisasm names target BSS ranges `B_...`
but emits them as size-0 local `STT_NOTYPE` labels, while the compiler often
leaves the base with only a `.bss` section symbol plus relocation addends.
objdiff resolves section relocations to the nearest named symbol, so a target
relocation becomes `B_...` and the corresponding base relocation stays
`[.bss]+offset`; `reloc_eq` then treats the identical reference as different.
`tools/symbolize_base.py` therefore copies missing target `B_...` labels into
the base, but only when the base has no symbol at the destination offset.
`STT_SECTION` symbols do not occupy an offset: a bare `.bss` section symbol at
value 0 must not block a mirrored label at base offset 0. Existing base names
are preserved, and the mirrored labels keep size 0 and `STT_NOTYPE`.

The destination is not always the target offset. A target split can cover only
part of the base `.bss`, or the compiler can order BSS variables differently;
for example `7.1/cfe/c` target `B_10020F10` is at offset `0x10`, while the base
variable is at `0x3e90`. The tool infers the per-section shift by pairing
`R_MIPS_LO16` relocations at the same code address on both sides and comparing
their effective BSS offsets. Only unambiguous shifts are used. Without this,
the mirrored label lands at the wrong base offset and objdiff still compares
`B_10020F10` against `[.bss]+0x3e90`. With it, relocations match by symbol name
even when the two sections use different offsets. This makes correct BSS
references match 100% while a reference to a different BSS offset still
differs. BSS is not counted in `PROGRESS.md`.

## Symbol types and section sizing

The fake section symbol that objdiff adds for "all data in this section" uses
`STT_OBJECT` symbols to infer its size. The `nonmatching` macro therefore emits
`.NON_MATCHING` markers as `STT_NOTYPE`; otherwise a size-1 marker near the end
of `.rodata` makes objdiff think the section is only 333 bytes long. Mirrored
data symbols are marked `STT_OBJECT` for the same reason. Target assembly
objects depend on `include/macro.inc`, so changing the macro rebuilds them.

The `disasm` step rewrites spimdisasm's autogenerated `func_*`, `RO_*`, `D_*`
and `jtbl_*` labels to **local** labels while preserving their
`@function`/`@object` types (`glabel name, local` / `dlabel name, local`).
`B_*` labels remain local `STT_NOTYPE` as before. Dropping the types instead
would leave target data symbols as `STT_NOTYPE`, so objdiff would size the
fake `.data` symbol only up to the last real `STT_OBJECT`; for example
`7.1/cfe/target` reported `.data` at 69% even though all bytes matched.

spimdisasm can also mistake a data word for a pointer when it happens to equal
an address in `.rodata`. An optional
`symbols/<version>/<program>.reloc_addrs.txt` file (splat syntax) is passed to
the disassembler. Use `rom:<offset> reloc:MIPS_NONE symbol:0` to keep such a
word as a raw constant and suppress the relocation. For example,
`symbols/7.1/ugen.reloc_addrs.txt` pins the Pascal set word at `0x76EE0` that
equals `0x10008100`, keeping `7.1/ugen/tree_print` `.data` at 100%. The file
has no comment syntax; keep only relocation entries.

## Diffing

`make diff` builds stale objects, regenerates `objdiff.json`, and then runs the
diff:

```bash
make diff UNIT=7.1/ugen/build SYM=build_tree
```

To drive objdiff-cli directly, build first; it does not run make itself:

```bash
make both
make objdiff
objdiff-cli diff -p . -u 7.1/ugen/build build_tree
```

For non-interactive output:

```bash
make diff UNIT=7.1/ugen/build SYM=build_tree DIFF_FLAGS='-o /tmp/diff.json'
```

## objdiff-cli version

Requires objdiff-cli **3.8.3** or newer.

```bash
make diff UNIT=... SYM=... OBJDIFF_CLI=/path/to/objdiff-cli-3.8.3
```

## Report

```bash
objdiff-cli report generate -p . -o build/report.json
```

## Progress

```bash
make progress   # regenerates PROGRESS.md
```

`tools/progress.py` derives matched functions from the report. Target objects
without a base object (source files that have not been started yet) are still
counted in the denominator as unmatched. The report also marks target
functions with no corresponding base symbol as `100%`; progress therefore
cross-checks program function names against the base object and treats missing
ones as unmatched. Target objects Duplicate target objects are
deduplicated by their function/data signature. The tool excludes `__start`,
`_mcount`, `_ftext`, `_rld_*`, crt/runtime symbols and `*.NON_MATCHING`
aliases, and honours `matched`/`ignored` entries in
`symbols/<version>/<program>.match_overrides.txt`.

Library functions are counted in separate `libu`, `libp`, `libmld`, `libelf`
and `libc` rows instead of the program that embeds them. A function is
assigned to exactly one bucket: function rows first, then unit rows, otherwise
the program. `pad_*` target objects that contain only padding are ignored;
`pad_*` objects that contain a library function stay in the library bucket.
Data-only library units also contribute their `.data`/`.rodata` sections to the
library rows even though they have no functions; they are never added to a
program. Library rows are included in version subtotals and the all-versions
total.

The table also reports `.data` and `.rodata` byte match percentages. They use
objdiff section match percentages; target-only units contribute their full
section size to the denominator. `.bss` is intentionally not counted yet.

`make progress` is safe to re-run: `PROGRESS.md` is only rewritten when its
content changes.
