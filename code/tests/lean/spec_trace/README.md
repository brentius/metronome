# Clause trace: SPEC_V2 <-> Metronome.Machine

Check 1 of `BOTS/PLANS/LEAN_MACHINE_SPEC_PLAN.md`. Standard library only (`tomllib`, Python 3.11+).

| File | Role |
|---|---|
| `clauses.py` | splits `wiki/SPEC_V2.md` into hashed clauses (`python clauses.py [--json]`) |
| `spec_trace.toml` | one entry per clause: kind, decls, reason; plus an optional `[helpers]` table |
| `check_trace.py` | the checker and the `--update` generator |
| `test_spec_trace.py` | pytest, toy SPEC and Lean fixture |

## Clauses

Each non-blank line of a fenced block (`code`), each bullet including wrapped lines (`bullet`, nested bullets are separate), each numbered item (`item`), each table data row (`table`; header and separator are skipped) and each prose sentence (`p`). Sentences are not split on `e.g.`, `i.e.`, `etc.`, version numbers, decimals, `9a.8`-style references or backticked code. Headings are not clauses.

ID: `§<section>/<kind><n>`, n counted per section and kind from 1 (`§3.2/code4`, `§5/table2`, `§9a/item8`, `§3.2a/p2`). The preamble before section 1 is `§0`. Hash: first 10 hex of SHA-256 of the whitespace-normalised text.

## Classification (`kind`)

| kind | meaning | required |
|---|---|---|
| `unmapped` | not yet classified; fails the check | |
| `machine` | implemented by the named Lean declarations | non-empty `decls` |
| `table` | numbers carried by the generated `Tables` declarations | non-empty `decls` |
| `theorem` | a calculated consequence, stated or proved about the spec | `decls` (empty allowed, warns) |
| `informative` | rationale, cost, evidence status | `reason` |
| `outside` | not modelled by the machine step (toolchain obligation, model diagnostic, physical timing) | `reason` |
| `stale` | spec text changed since classification; set by `--update` only; fails the check | |

`--update` pre-classifies only the obvious non-machine clauses: section 0 and section 11 (informative), 12.5 and the 10.4 toolchain item with its bullets (outside), `**Status` and `Cost:` paragraphs and lead-in labels (informative), and text labelled "calculated" or "estimated" (theorem with `decls = []`). Everything else stays `unmapped` for the spec writer. Review the pre-classification; it is a starting point, not a decision.

## Usage

```
python check_trace.py --update            # add new clauses, keep classifications, mark changed text stale
python check_trace.py                     # full check, exit 1 on any error
python check_trace.py --allow-unmapped    # while writing: unmapped is not an error ((b), (c) still are)
python check_trace.py --allow-unmapped --allow-orphans   # also report unreferenced decls as warnings
python -m pytest code/tests/lean/spec_trace -q
```

Options `--spec`, `--toml`, `--lean-dir` override the defaults (`wiki/SPEC_V2.md`, `spec_trace.toml`, `../Metronome/Machine`).

Errors (exit 1):
- (a) a clause that is `unmapped` or `stale`, has a hash that differs from the spec, has no entry, or an entry with no clause; `machine`/`table` without `decls`; `informative`/`outside` without `reason`;
- (b) a `decls` entry (or a helper) not declared in the Lean sources: names from `def|theorem|lemma|structure|inductive|abbrev|instance|opaque`, resolved through `namespace ... end` to full names, comments ignored;
- (c) a non-`private` declaration in `Metronome.Machine.*` that no clause references and that is not in `Metronome.Machine.Util`, `Metronome.Machine.Tables` (or the file `Tables.lean`), or the `[helpers]` table. No behaviour without a clause.

The summary prints clause counts per kind and per section.

## Filling rows (spec writer)

1. Run `--update`. Open `spec_trace.toml`; the `text` field is a shortened copy of the clause.
2. For each `unmapped` clause set `kind` and add `decls = ["Metronome.Machine.Line.accept", ...]` (full names; a structure counts as one declaration, its fields are not scanned). One declaration may serve many clauses; one clause may name many declarations. Use `informative` or `outside` only with a reason that a reviewer can accept.
3. Declarations that implement no clause but are needed (glue, notation, internal lemmas) are `private`, placed in `Metronome.Machine.Util`, or listed:

```
[helpers."Metronome.Machine.foo"]
reason = "why this has no SPEC clause"
```

4. A `theorem` with `decls = []` is a consequence not yet stated; the checker warns. Fill it when the theorem exists.
5. After a SPEC edit run `--update`: unchanged text keeps its row even if renumbered, changed text becomes `stale` with `was` (old kind) and `old_text`. Review it, set `kind` back (or new), and delete `was` and `old_text`. Never edit `hash` by hand.

Evidence level: a passing check shows the mapping is complete, not that a declaration implements its clause correctly. That is checks 3 and 4 and the independent review.
