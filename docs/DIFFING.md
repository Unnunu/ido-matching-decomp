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

A unit is named `<version>/<program>/<file>`, for example:

```text
7.1/ugen/build
target_path = build/asm/7.1/ugen/build.o
base_path   = build/src/7.1/ugen/build.o
```

`metadata.source_path` points at the C or Pascal source when it can be found.
Targets without a built base object are skipped by default. Pass
`--include-missing-base` to `tools/gen_objdiff.py` to emit them with
`metadata.complete: false`.

## Libraries embedded in program targets

IDO binaries statically link libraries such as `libu`, `libp`, `libmld`,
`libelf` and the Pascal runtime. Their functions are part of target objects but
are not program code, so they must not inflate a program's unstarted count.

Library membership lives in `symbols/<version>/libraries.csv`:

```text
# kind,program,target,library,module
unit,ugen,ugen_04F430,libu,uini
function,ugen,uputinit,libu,ucio
```

- `kind=unit` marks every function in `<program>/<target>` as library code.
- `kind=function` marks one function name in that program.
- Function rows override unit rows; anything unlisted stays program code.
- The split CSVs are not extended because they describe object boundaries and
  are consumed by spimdisasm. A split object can mix program and library code,
  so membership has to be tracked per function as well as per object.
- A `kind=unit` row also works for a data-only split (a target object with no
  functions). Its `.data`/`.rodata` sections are then counted in the library
  bucket instead of the program bucket. Pure-library data-only splits are
  identified by cross-references: every external reference to their symbols
  comes from library functions. Data-only splits that mix program and library
  data are left as program code until section-level annotations exist.

`tools/gen_objdiff.py` emits extra library units for categories with a built
base object (`libu`, `libp`, `libmld`; `libmld` uses the `mld` source/build
folder for `sex.c`):

```text
7.1/libu/uini/ugen/ugen_04F430
target_path = build/asm/7.1/ugen/ugen_04F430.o
base_path   = build/src/7.1/libu/uini.o
metadata.library_name = libu
metadata.library_module = uini
metadata.target_program = ugen
metadata.target_rel = ugen_04F430
```

These units exist for diffing and for objdiff fuzzy results. Progress skips
them as program units and uses their per-function results to score the library
bucket. Parts of `libmld` without a base object (`st_*`, `swap_*`, `ldf*`),
plus `libelf`, `libc` and the Pascal runtime, are counted as unmatched library
code.

## Symbol mappings

Target assembly often uses names such as `func_0040E238`, while the source uses
meaningful names. `tools/gen_objdiff.py` reads both ELF symbol tables and maps
target symbols to base symbols with the same section, offset, and size.

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
`tools/objdiff_make.py` runs it after GUI-triggered rebuilds, so the base side
shows the same `RO_STR_...` names as the target. Library units are left
unchanged because their base object may be shared by several targets.

BSS labels get the same treatment. spimdisasm names target BSS ranges `B_...`
but emits them as size-0 local `STT_NOTYPE` labels, while the compiler often
leaves the base with only a `.bss` section symbol plus relocation addends.
objdiff resolves section relocations to the nearest named symbol, so a target
relocation becomes `B_...` and the corresponding base relocation stays
`[.bss]+offset`; `reloc_eq` then treats the identical reference as different.
`tools/symbolize_base.py` therefore copies missing target `B_...` labels into
the base, but only when the base has no symbol at the destination offset.
Existing base names are preserved, and the mirrored labels keep size 0 and
`STT_NOTYPE`.

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
make match      # incremental update; writes PROGRESS.md and build/progress.json
make progress   # full pass, prints the table
make check      # fail on stale PROGRESS.md or a regression vs build/baseline.json
make baseline   # explicitly refresh the regression baseline
```

`tools/progress.py` derives matched functions from the report. Target objects
without a base object (source files that have not been started yet) are still
counted in the denominator as unmatched. Duplicate target objects are
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
program. Library rows are included in version subtotals, the all-versions total
and the regression baseline.

The table also reports `.data` and `.rodata` byte match percentages. They use
objdiff section match percentages; target-only units contribute their full
section size to the denominator. `.bss` is intentionally not counted yet.

The generated NON_MATCHING view lives in `build/asm-marked/<version>/<program>/`.
It is produced from `asm/` without rewriting it. `make match` reuses an mtime
cache stored in `build/progress.json`, so unchanged units are not rewritten.
