"""pytest tests for clauses.py and check_trace.py using a toy SPEC and Lean fixture."""
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import check_trace as ct  # noqa: E402
import clauses  # noqa: E402

TOY_SPEC = """# Toy spec

Status: draft. Intro text e.g. with an abbreviation.

## 1. Conventions

- One clock, `clk`.
- Reset clears
  every register.

## 2. Lines

A line counts. It wraps at v2.5 or 3.2 cycles (see section 9a.8), and `a. b` stays whole.

```
n = PH + INC
wrap = n >= MOD
```

1. First item.
2. Second item.

| Event | Timing |
|---|---|
| Trigger | t+3 |

### 2.1 Hold

Calculated consequence (calculated from the rules above).
"""

TOY_LEAN = """namespace Metronome.Machine
namespace Line
def accept (x : Nat) : Bool := true
private def hidden := 1
theorem accept_ok : True := trivial
end Line
/- block comment
def Commented := 0 -/
-- def LineComment := 0
namespace Util
def helper := 2
end Util
def Top.nested := 3
end Metronome.Machine
"""

ACCEPT = "Metronome.Machine.Line.accept"
ACCEPT_OK = "Metronome.Machine.Line.accept_ok"
NESTED = "Metronome.Machine.Top.nested"


def test_clause_ids_and_splitting():
    cl = clauses.parse(TOY_SPEC)
    ids = [c.id for c in cl]
    assert ids[:2] == ["§0/p1", "§0/p2"]  # "Status: draft." and "Intro text e.g. ..."
    assert "§1/bullet1" in ids and "§1/bullet2" in ids
    assert [c.text for c in cl if c.id == "§1/bullet2"] == ["Reset clears every register."]
    p = [c for c in cl if c.section == "2" and c.kind == "p"]
    assert len(p) == 2  # no split on v2.5, 3.2, 9a.8, or inside backticks
    assert p[0].text == "A line counts."
    assert "v2.5" in p[1].text and "`a. b`" in p[1].text
    assert [c.id for c in cl if c.kind == "code"] == ["§2/code1", "§2/code2"]
    assert [c.id for c in cl if c.kind == "item"] == ["§2/item1", "§2/item2"]
    assert [c.id for c in cl if c.kind == "table"] == ["§2/table1"]  # header and separator skipped
    assert any(c.section == "2.1" for c in cl)


def test_hash_is_whitespace_normalised_and_stable():
    assert clauses.text_hash("a  b\n c") == clauses.text_hash("a b c")
    assert len(clauses.text_hash("x")) == 10
    assert [c.hash for c in clauses.parse(TOY_SPEC)] == [c.hash for c in clauses.parse(TOY_SPEC)]


def test_real_spec_parses():
    spec = HERE.parents[1] / "wiki" / "SPEC_V2.md"
    if not spec.exists():
        pytest.skip("no SPEC_V2.md")
    cl = clauses.parse_file(spec)
    assert len({c.id for c in cl}) == len(cl)
    assert any(c.id.startswith("§3.2a/") for c in cl) and any(c.id.startswith("§9a/item") for c in cl)


def test_lean_scanner_namespaces_comments_private():
    d = {x["name"]: x for x in ct.scan_lean_text(TOY_LEAN, "T.lean")}
    assert ACCEPT in d
    assert d["Metronome.Machine.Line.hidden"]["private"]
    assert ACCEPT_OK in d
    assert NESTED in d  # after `end Line` the namespace is popped
    assert "Metronome.Machine.Util.helper" in d
    assert not any("Commented" in n or "LineComment" in n for n in d)


@pytest.fixture
def env(tmp_path):
    spec = tmp_path / "SPEC.md"
    spec.write_text(TOY_SPEC, encoding="utf-8")
    lean = tmp_path / "Machine"
    lean.mkdir()
    (lean / "Line.lean").write_text(TOY_LEAN, encoding="utf-8")
    return spec, lean, tmp_path / "t.toml"


def run(env, *extra):
    spec, lean, toml = env
    return ct.main(["--spec", str(spec), "--toml", str(toml), "--lean-dir", str(lean), *extra])


def fill(env, helper=True):
    """Update, then classify every unmapped clause so that the toy passes."""
    spec, _lean, toml = env
    entries, _ = ct.update(clauses.parse_file(spec), {})
    for e in entries.values():
        if e["kind"] == "unmapped":
            e["kind"] = "machine"
            e["decls"] = [ACCEPT, ACCEPT_OK]
    helpers = {NESTED: {"reason": "toy helper"}} if helper else {}
    ct.write_toml(toml, entries, helpers)
    return entries, helpers


def test_fresh_update_is_unmapped_and_fails(env, capsys):
    assert run(env, "--update") == 1
    out = capsys.readouterr().out
    assert "unmapped" in out and "per section" in out
    assert run(env, "--allow-unmapped") == 1  # Line.accept is an orphan: (c)
    assert run(env, "--allow-unmapped", "--allow-orphans") == 0


def test_pass_case_and_toml_roundtrip(env):
    fill(env)
    assert run(env) == 0
    data, helpers = ct.load_toml(env[2])
    assert helpers[NESTED]["reason"] == "toy helper"
    by_id = {c.id: c for c in clauses.parse_file(env[0])}
    assert data["§2/code1"]["hash"] == by_id["§2/code1"].hash


def test_preclassify_toy(env):
    entries, _ = ct.update(clauses.parse_file(env[0]), {})
    assert entries["§0/p1"]["kind"] == "informative"
    assert entries["§2.1/p1"]["kind"] == "theorem" and entries["§2.1/p1"]["decls"] == []


def test_stale_hash(env):
    fill(env)
    env[0].write_text(TOY_SPEC.replace("First item.", "First item changed."), encoding="utf-8")
    assert run(env) == 1  # hash mismatch before update
    assert run(env, "--update") == 1
    data, _ = ct.load_toml(env[2])
    assert data["§2/item1"]["kind"] == "stale" and data["§2/item1"]["was"] == "machine"
    text = env[2].read_text(encoding="utf-8")  # reviewer reclassifies: stale -> machine
    start = text.index('["§2/item1"]')
    end = text.index("\n\n", start)
    blk = text[start:end].replace('kind = "stale"', 'kind = "machine"')
    env[2].write_text(text[:start] + blk + text[end:], encoding="utf-8")
    assert run(env) == 0


def test_update_follows_renumbered_clause(env):
    fill(env)
    env[0].write_text(TOY_SPEC.replace("- One clock, `clk`.\n", "- New bullet.\n- One clock, `clk`.\n"),
                      encoding="utf-8")
    run(env, "--update")
    data, _ = ct.load_toml(env[2])
    assert data["§1/bullet1"]["kind"] == "unmapped"  # new text
    assert data["§1/bullet2"]["kind"] == "machine"  # "One clock" moved here


def test_missing_decl(env, capsys):
    fill(env)
    t = env[2].read_text(encoding="utf-8").replace(ACCEPT_OK, "Metronome.Machine.Line.nope", 1)
    env[2].write_text(t, encoding="utf-8")
    assert run(env) == 1
    assert "(b)" in capsys.readouterr().out


def test_orphan_decl_and_helper_allowance(env, capsys):
    fill(env, helper=False)
    assert run(env) == 1
    out = capsys.readouterr().out
    assert "(c) " + NESTED in out
    assert "Util.helper" not in out and "hidden" not in out  # Util and private are exempt
    fill(env, helper=True)
    assert run(env) == 0


def test_helper_must_exist_and_have_reason(env):
    entries, _ = fill(env)
    helpers = {NESTED: {"reason": ""}, "Metronome.Machine.Gone": {"reason": "x"}}
    errors, _ = ct.check(clauses.parse_file(env[0]), entries, helpers, ct.scan_lean_dir(env[1]))
    assert any("needs a reason" in e for e in errors) and any("Gone" in e for e in errors)


def test_machine_needs_decls_and_informative_needs_reason(env):
    entries, helpers = fill(env)
    entries["§1/bullet1"]["decls"] = []
    entries["§0/p1"]["reason"] = ""
    errors, _ = ct.check(clauses.parse_file(env[0]), entries, helpers, ct.scan_lean_dir(env[1]))
    assert any("§1/bullet1" in e and "decls" in e for e in errors)
    assert any("§0/p1" in e and "reason" in e for e in errors)


def test_theorem_empty_decls_warns_not_fails(env):
    entries, helpers = fill(env)
    errors, warns = ct.check(clauses.parse_file(env[0]), entries, helpers, ct.scan_lean_dir(env[1]))
    assert not errors and any("§2.1/p1" in w for w in warns)


def test_obsolete_toml_entry_fails(env):
    entries, helpers = fill(env)
    entries["§9/p1"] = {"hash": "x", "text": "gone", "kind": "informative", "reason": "r"}
    errors, _ = ct.check(clauses.parse_file(env[0]), entries, helpers, ct.scan_lean_dir(env[1]))
    assert any("§9/p1" in e for e in errors)
