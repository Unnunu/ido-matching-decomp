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

`make objdiff` regenerates `objdiff.json` for 5.3 and 7.1. It does not build the
objects itself; run `make both` first after a clean checkout.

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

## Diffing

```bash
make diff UNIT=7.1/ugen/build SYM=build_tree
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
`_mcount`, crt/runtime symbols and `*.NON_MATCHING` aliases, and honours
`matched`/`ignored` entries in
`symbols/<version>/<program>.match_overrides.txt`.

The table also reports `.data` and `.rodata` byte match percentages. They use
objdiff section match percentages; target-only units contribute their full
section size to the denominator. `.bss` is intentionally not counted yet.

The generated NON_MATCHING view lives in `build/asm-marked/<version>/<program>/`.
It is produced from `asm/` without rewriting it. `make match` reuses an mtime
cache stored in `build/progress.json`, so unchanged units are not rewritten.
