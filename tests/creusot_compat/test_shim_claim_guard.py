"""Harness source rewrites may never change Creusot's claims or trust base.

Replays ``transform_creusot_to_trust_wp`` and ``apply_test_specific_shims`` on
every corpus file (should_succeed, should_fail, examples) and compares the
PROTECTED text of each file before and after: every ``#[requires]``,
``#[ensures]``, ``#[invariant]``, ``#[variant]``, ``#[trusted]``, ``#[check(..)]``
and ``#[logic(..)]`` attribute (every argument: ``law``, ``open``/``opaque``,
``prophetic``, ...), outer and inner (``#![..]``) forms alike; the WHOLE item
(signature and body) following a ``#[logic(..)]`` / ``#[predicate(..)]``
attribute, since a logic body written without ``pearlite!`` is still a spec;
and every ``proof_assert!`` / ``pearlite!`` / ``snapshot!`` / ``ghost!``
invocation. A change fails unless ``(file, kind)`` is in ``ALLOWLIST`` with a
justification and an explicit claim-neutral verdict. Allowlist entries that no
longer match any change also fail, so the list cannot rot into a blanket pass.

Seeded only from rewrites BOTH shim audits (``shims.md`` and
``shims-skeptic.md``, 2026-09-13) classify as neutral.
"""
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
WORKSPACE_ROOT = HERE.parents[1]
CORPUS = WORKSPACE_ROOT / "reference" / "creusot"
LANES = ("tests/should_succeed", "tests/should_fail", "examples")
sys.path.insert(0, str(HERE))

import harness_project  # noqa: E402

# Attribute kinds: ``#[<head>(...)]``, with optional ``creusot::`` style paths.
_ATTR_RE = re.compile(
    r"#\s*!?\s*\[\s*(?:(?:::)?[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*"
    r"(?P<kind>requires|ensures|invariant|variant|trusted|logic|predicate|check)\b"
)
_MACRO_RE = re.compile(r"\b(?P<kind>proof_assert|pearlite|snapshot|ghost)\s*!\s*(?=[({\[])")
# Attributes that make the following item a specification item.
_SPEC_ITEM_KINDS = ("logic", "predicate")
_ITEM_START_RE = re.compile(r"\bfn\b")
_CLOSE = {"(": ")", "[": "]", "{": "}"}


def _balanced(text: str, start: int) -> int:
    """Index just past the bracket group opening at ``text[start]`` (fail-closed: end of text)."""
    depth = []
    i = start
    in_str = False
    while i < len(text):
        c = text[i]
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
        elif c == '"':
            in_str = True
        elif c in _CLOSE:
            depth.append(_CLOSE[c])
        elif depth and c == depth[-1]:
            depth.pop()
            if not depth:
                return i + 1
        i += 1
    return len(text)


def _spec_item_text(source: str, attr_end: int) -> str:
    """The item a ``#[logic]``/``#[predicate]`` attribute annotates: through its body's closing brace.

    Fail-closed: without a following ``fn`` the rest of the file is protected.
    """
    m = _ITEM_START_RE.search(source, attr_end)
    if not m:
        return source[attr_end:]
    i = m.end()
    while i < len(source) and source[i] not in "{;":
        if source[i] in "([<":
            i = _balanced(source, i) if source[i] != "<" else i + 1
            continue
        i += 1
    if i >= len(source) or source[i] == ";":
        return source[attr_end : i + 1]
    return source[attr_end : _balanced(source, i)]


def protected_fragments(source: str) -> Counter:
    """Multiset of (kind, whitespace-normalised text) for every protected span."""
    out: Counter = Counter()
    for m in _ATTR_RE.finditer(source):
        open_idx = source.index("[", m.start())
        end = _balanced(source, open_idx)
        frag = " ".join(source[m.start() : end].split())
        kind = m.group("kind")
        if kind in _SPEC_ITEM_KINDS:
            args = re.search(r"\(\s*([^)]*?)\s*\)", frag)
            kind = f"{kind}({' '.join(args.group(1).split())})" if args else kind
            out[(kind, frag)] += 1
            item = " ".join(_spec_item_text(source, end).split())
            out[("spec-item", f"{frag} {item}")] += 1
            continue
        out[(kind, frag)] += 1
    for m in _MACRO_RE.finditer(source):
        end = _balanced(source, m.end())
        out[(m.group("kind"), " ".join(source[m.start() : end].split()))] += 1
    return out


def protected_changes(original: str, rewritten: str) -> set[str]:
    """Kinds whose protected text differs between ``original`` and ``rewritten``."""
    before, after = protected_fragments(original), protected_fragments(rewritten)
    return {kind for (kind, _), n in ((before - after) + (after - before)).items() if n}


def rewrite(rel: str, source: str) -> str:
    """The exact gate-path rewrite of one corpus file's lib.rs text."""
    transformed = harness_project.transform_creusot_to_trust_wp(source)
    return harness_project.apply_test_specific_shims(Path("reference/creusot") / rel, transformed)


# (corpus file, protected kind) -> (justification, claim_neutral)
ALLOWLIST: dict[tuple[str, str], tuple[str, bool]] = {
    ("tests/should_succeed/resource_algebras/fmap_view_view.rs", "pearlite"): (
        "S6/S7: `self.0@.auth()` -> `self.0@.auth` inside the Authority invariant and "
        "view pearlite bodies; trust-wp-std logic/ra/view.rs defines "
        "`#[logic(open)] fn auth(self) = self.auth` (neutral in shims.md and shims-skeptic.md)",
        True,
    ),
    ("tests/should_succeed/resource_algebras/fmap_view_view.rs", "spec-item"): (
        "S6/S7 again, seen as whole `#[logic]` items (`invariant`, `view`): the only change in "
        "the item text is `auth()` -> `.auth`, identical by trust-wp-std logic/ra/view.rs "
        "`#[logic(open)] fn auth(self) = self.auth` (neutral in both audits)",
        True,
    ),
    ("tests/should_succeed/resource_algebras/fmap_view_view.rs", "snapshot"): (
        "S4: `snapshot!(self@.insert(*k, *v))` -> `snapshot!((&*self)@.insert(*k, *v))`; the view "
        "of `&mut self` is the view of its current value, i.e. of `&*self` (neutral in both audits)",
        True,
    ),
    ("tests/should_succeed/ghost/fmap_iter.rs", "snapshot"): (
        "S2: `snapshot!(m1.merge(*m2, ..))` -> `snapshot!(m1.into_inner().merge(m2.into_inner(), ..))`; "
        "Creusot auto-derefs `Ghost` and GHOST_INTO_INNER is `result == self` (neutral in both audits)",
        True,
    ),
    ("tests/should_succeed/ghost/fmap_iter.rs", "ghost"): (
        "S2 seen through the enclosing `ghost! { .. }` block of merge_fmaps: the block text differs "
        "only by the S2 snapshot rewrite (neutral in both audits)",
        True,
    ),
    ("tests/should_succeed/ghost/ghost_map.rs", "ghost"): (
        "S10: `let (x, map2) = map.split_mut_ghost(&1);` -> `let (x, mut map2) = ..` inside the "
        "ghost block; binding mutability only (neutral in both audits)",
        True,
    ),
    ("examples/hillel.rs", "snapshot"): (
        "E1: `snapshot! { 0 }` / `snapshot! { 1 + *c }` -> `Int::from(0)` / `Int::from(1) + *c`; "
        "literal typing, same integer (neutral in both audits)",
        True,
    ),
    ("examples/iterators/02_iter_mut.rs", "snapshot"): (
        "I2: `Seq::singleton(x)` -> `Seq::singleton(Snapshot::capture(&x).into_inner())`; capture is "
        "`result == value`, into_inner is `result == self` (neutral in both audits)",
        True,
    ),
    ("examples/iterators/03_std_iterators.rs", "snapshot"): (
        "I1: `snapshot! { slice@ }` -> `snapshot! { (&*slice)@ }`; the view of `&mut [T]` is its "
        "current view (neutral in both audits)",
        True,
    ),
    ("examples/iterators/06_map_precond.rs", "snapshot"): (
        "I4: `self.produced.push_back(v)` -> `..push_back(Snapshot::capture(&v).into_inner())`; "
        "identity as I2 (neutral in both audits)",
        True,
    ),
    ("examples/iterators/17_filter.rs", "snapshot"): (
        "I3: `produced.push_back(n)` -> `produced.push_back(Snapshot::capture(&n).into_inner())`; "
        "identity as I2 (neutral in both audits)",
        True,
    ),
}

# Rewrites the audits classify as CHANGING a claim (or unconstraining a ghost
# witness). They are tolerated ONLY in the examples lane, which is outside the
# 278/99 gate and unmeasured; they are listed so the guard still catches any NEW
# rewrite there, and so nobody can read the examples lane as claim-faithful.
# A gate-lane (should_succeed / should_fail) key here is a test failure.
KNOWN_CLAIM_CHANGING_OUTSIDE_GATE: dict[tuple[str, str], str] = {
    ("examples/linked_list.rs", "ghost"): "E9: `seq: Seq::new()` -> `seq: ghost!(Seq::new())` (changes_claim; skeptic: identical or fail-closed)",
    ("examples/parallel_add.rs", "snapshot"): "PA1: `snapshot!((atomic, frag1.id(), frag2.id()))` -> `Snapshot::new_phantom()` (changes_claim)",
    ("examples/parallel_add_n.rs", "snapshot"): "P3/P5 new_phantom witnesses (changes_claim), plus neutral P2/P4 literal typing",
    ("examples/parallel_add_n.rs", "ghost"): "P2/P4/P5 seen through the enclosing ghost blocks (P5 changes_claim)",
    ("examples/persistent_array.rs", "snapshot"): "depth/perms key rewrites to `x.as_ref().clone()` (skeptic: changes_claim, fail-closed), plus neutral PA-1..PA-3",
    ("examples/persistent_array.rs", "ghost"): "PA-8 `ghost!(&mut *pa)` -> `ghost!(pa.into_inner())` (changes_claim, possible false->true) and key rewrites inside ghost blocks",
    ("examples/union_find_cpp.rs", "snapshot"): "E7 `snapshot!(such_that(|_| true))` -> `Snapshot::new_phantom()` (changes_claim)",
    ("examples/union_find_cpp.rs", "ghost"): "E7 seen through the enclosing ghost block of `new` (changes_claim)",
    ("examples/union_find_full.rs", "snapshot"): "F4 new_phantom witnesses and F6 oracle removal (changes_claim), plus neutral F5",
    ("examples/union_find_full.rs", "ghost"): "F4/F5/F6 seen through the enclosing ghost blocks (changes_claim)",
}


def _corpus_files() -> list[str]:
    files = []
    for lane in LANES:
        files.extend(p.relative_to(CORPUS).as_posix() for p in (CORPUS / lane).rglob("*.rs"))
    return sorted(files)


def _corpus_changes() -> dict[tuple[str, str], None]:
    changes = {}
    for rel in _corpus_files():
        source = (CORPUS / rel).read_text(encoding="utf-8")
        for kind in protected_changes(source, rewrite(rel, source)):
            changes[(rel, kind)] = None
    return changes


requires_corpus = pytest.mark.skipif(
    not (CORPUS / "tests" / "should_succeed").is_dir(), reason="Creusot reference corpus not checked out"
)


@requires_corpus
def test_corpus_is_the_full_gate_corpus():
    files = _corpus_files()
    assert sum(f.startswith("tests/should_succeed/") for f in files) >= 278
    assert sum(f.startswith("tests/should_fail/") for f in files) >= 99


@requires_corpus
def test_no_unallowlisted_rewrite_of_claims_or_trust():
    changes = _corpus_changes()
    known = set(ALLOWLIST) | set(KNOWN_CLAIM_CHANGING_OUTSIDE_GATE)
    unjustified = sorted(k for k in changes if k not in known)
    assert not unjustified, (
        "harness rewrites change contract/trust text without an ALLOWLIST justification: "
        f"{unjustified}"
    )
    stale = sorted(k for k in known if k not in changes)
    assert not stale, f"ALLOWLIST entries match no rewrite (remove them): {stale}"


@requires_corpus
def test_should_fail_lane_is_never_rewritten_in_protected_text():
    assert not [k for k in _corpus_changes() if k[0].startswith("tests/should_fail/")]


def test_claim_changing_rewrites_are_confined_to_the_examples_lane():
    assert not set(ALLOWLIST) & set(KNOWN_CLAIM_CHANGING_OUTSIDE_GATE)
    for (rel, _kind), why in KNOWN_CLAIM_CHANGING_OUTSIDE_GATE.items():
        assert rel.startswith("examples/"), rel
        assert len(why) > 30, rel


def test_allowlist_entries_are_justified_and_claim_neutral():
    for key, (why, neutral) in ALLOWLIST.items():
        assert isinstance(why, str) and len(why) > 40, key
        # Only claim-neutral rewrites may be seeded; a claim-changing rewrite
        # needs a new audit, not an allowlist line.
        assert neutral is True, key


@pytest.mark.parametrize(
    "before, after, kind",
    [
        ("#[ensures(x.0 == x.1)]\nfn f() {}", "#[ensures(x.0 == x.0 && x.1 == x.1)]\nfn f() {}", "ensures"),
        ("#[ensures(r)]\nfn f() {}", "#[requires(x == 0)]\n#[ensures(r)]\nfn f() {}", "requires"),
        ("#[check(ghost)]\nfn f() {}", "#[trusted]\n#[check(ghost)]\nfn f() {}", "trusted"),
        ("#[trusted]\n#[ensures(a)]\nfn f() {}", "#[ensures(a)]\nfn f() {}", "trusted"),
        ("#[logic(law)]\nfn l() {}", "#[trusted]\nfn l() {}", "logic(law)"),
        ("#[invariant(i < n)]\nwhile c {}", "#[invariant(i <= n)]\nwhile c {}", "invariant"),
        ("#[variant(n)]\nfn f() {}", "#[variant(n - 1)]\nfn f() {}", "variant"),
        ("proof_assert! { a && b };", "proof_assert! { a };", "proof_assert"),
        ("pearlite! { self.0@.auth() != None }", "pearlite! { true }", "pearlite"),
        ("#[creusot::ensures(a)]\nfn f() {}", "#[creusot::ensures(b)]\nfn f() {}", "ensures"),
        ("#[logic(open)]\nfn l() -> bool { true }", "#[logic(opaque)]\nfn l() -> bool { true }", "logic(open)"),
        ("#[logic(open)]\nfn l() -> bool { true }", "#[logic(opaque)]\nfn l() -> bool { true }", "logic(opaque)"),
        ("#[logic(prophetic)]\nfn l() {}", "#[logic]\nfn l() {}", "logic(prophetic)"),
        ("#[logic]\nfn l(x: Int) -> bool { x > 0 }", "#[logic]\nfn l(x: Int) -> bool { x >= 0 }", "spec-item"),
        ("#[logic]\nfn l(x: Int) -> bool { x > 0 }", "#[logic]\nfn l(x: Int, y: Int) -> bool { x > 0 }", "spec-item"),
        ("#[predicate]\nfn p(x: Int) -> bool { x > 0 }", "#[predicate]\nfn p(x: Int) -> bool { true }", "spec-item"),
        ("#[check(ghost)]\nfn f() {}", "#[check(terminates)]\nfn f() {}", "check"),
        ("#[check(ghost)]\nfn f() {}", "fn f() {}", "check"),
        ("mod m {\n#![trusted]\nfn f() {}\n}", "mod m {\nfn f() {}\n}", "trusted"),
        ("#![check(terminates)]\nfn f() {}", "fn f() {}", "check"),
        ("let s = snapshot!(x + 1);", "let s = snapshot!(x);", "snapshot"),
        ("let s = snapshot! { *c };", "let s = Snapshot::new_phantom();", "snapshot"),
        ("let g = ghost!(&mut *pa);", "let g = ghost!(pa.into_inner());", "ghost"),
    ],
)
def test_detector_flags_each_protected_kind(before, after, kind):
    assert kind in protected_changes(before, after)


def test_detector_ignores_unprotected_rewrites():
    before = "extern crate creusot_std;\nfn f() { let x = snapshot!(1); }\n#[ensures(r)]\nfn g() {}\n#[logic]\nfn l() -> bool { true }"
    after = "#![register_tool(creusot)]\nfn f() { let mut x = snapshot!(1); }\n#[ensures(r)]\nfn g() {}\n#[logic]\nfn l() -> bool {\n    true\n}"
    assert protected_changes(before, after) == set()


def test_detector_ignores_moves_but_not_duplication():
    a = "#[ensures(a)]\nfn f() {}\n#[ensures(b)]\nfn g() {}"
    assert protected_changes(a, "#[ensures(b)]\nfn g() {}\n#[ensures(a)]\nfn f() {}") == set()
    assert "ensures" in protected_changes(a, a + "\n#[ensures(a)]\nfn h() {}")


# ---------------------------------------------------------------------------
# A goal-bearing item a shim marks #[trusted] is UNCOVERED, never credited.
# ---------------------------------------------------------------------------
# Trust is resolved against the ORIGINAL corpus source, so an item that only
# the rewritten fixture declares ``#[trusted]`` is not Creusot's trust base: its
# ``trusted (skipped)`` line is a negative row and its goals stay uncovered.

_FVV = "tests/should_succeed/resource_algebras/fmap_view_view.rs"
_FVV_CLONE_ITEM = "impl_Clone_for_Fragment_K_V::clone"
_FVV_CLONE_PATH = "<Fragment<K, V> as std::clone::Clone>::clone"
_FVV_CLONE_ANCHOR = "impl<K, V> Clone for Fragment<K, V> {\n    #[check(ghost)]"


def _fvv_shim_trusted_source(original: str) -> str:
    """What the removed S8 shim compiled: ``#[trusted]`` on Fragment::clone."""
    assert original.count(_FVV_CLONE_ANCHOR) == 1
    return original.replace(_FVV_CLONE_ANCHOR, _FVV_CLONE_ANCHOR.replace("{\n", "{\n    #[trusted]\n"))


def _fvv_report() -> list[str]:
    return [f"trust-wp: {_FVV_CLONE_PATH} trusted (skipped)"]


def _load_script(name: str):
    import importlib.util

    spec = importlib.util.spec_from_file_location(f"{name}_shim_guard", WORKSPACE_ROOT / "scripts" / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _clone_entries(coverage: dict) -> tuple[list[dict], list[dict]]:
    pick = lambda key: [e for e in coverage.get(key) or [] if e["item"] == _FVV_CLONE_ITEM]  # noqa: E731
    return pick("covered"), pick("uncovered")


@requires_corpus
def test_shim_trusted_item_is_uncovered_in_runner_goal_coverage():
    import harness_runner

    original = (CORPUS / _FVV).read_text(encoding="utf-8")
    shimmed = _fvv_shim_trusted_source(original)
    # The fixture text WOULD declare it trusted -- so crediting depends only on
    # which source the resolver sees.
    assert harness_runner.resolve_trusted_def_path(_FVV_CLONE_PATH, shimmed)
    assert not harness_runner.resolve_trusted_def_path(_FVV_CLONE_PATH, original)

    cov = harness_runner._goal_coverage_for(_FVV, _fvv_report(), original, [_FVV_CLONE_PATH])
    covered, uncovered = _clone_entries(cov)
    assert cov["inventory"] == "coma"
    assert covered == [] and len(uncovered) == 1, cov
    assert "source-declared" not in uncovered[0]["reason"]
    # Contrast: had the corpus itself declared it #[trusted], the same report
    # would credit it -- so the corpus-source resolution is what refuses it.
    as_if_source = harness_runner.compute_goal_coverage(_FVV, _fvv_report(), trusted_source_paths=[_FVV_CLONE_PATH])
    assert _clone_entries(as_if_source)[0], as_if_source


@requires_corpus
def test_shim_trusted_item_is_uncovered_in_compare_baselines_gate():
    cb = _load_script("compare_baselines")
    result = {
        "name": _FVV,
        "status": "pass",
        "driver_report": _fvv_report(),
        "trusted_def_paths": [_FVV_CLONE_PATH],
        "telemetry": {"trusted": 1},
    }
    assert cb.source_trusted_resolution(result), "shim-trusted item must not resolve as source-declared"
    reasons = cb.goal_coverage_reasons(result)
    assert any(_FVV_CLONE_ITEM in r for r in reasons), reasons


@requires_corpus
def test_run_single_test_resolves_trust_against_the_corpus_file(monkeypatch, tmp_path):
    """The runner must hand the coverage gate the corpus file, not the fixture."""
    import types

    import harness_model
    import harness_runner

    original = (CORPUS / _FVV).read_text(encoding="utf-8")
    output = "\n".join(_fvv_report()) + "\n"
    seen = {}
    real = harness_runner._goal_coverage_for

    def spy(test_name, report_lines, source, trusted_def_paths):
        seen["source"] = source
        return real(test_name, report_lines, source, trusted_def_paths)

    def fake_run(harness, workspace, test_path, temp_path, *rest):
        # Simulate a fixture whose lib.rs a shim marked trusted.
        (temp_path / "lib.rs").write_text(_fvv_shim_trusted_source(test_path.read_text()))
        return False, output, 1, 2

    monkeypatch.setattr(harness_runner, "_run_project_with_retry", fake_run)
    monkeypatch.setattr(
        harness_runner, "_classify_outcome", lambda *a, **k: ("pass", "", None, None, False)
    )
    monkeypatch.setattr(harness_runner, "_goal_coverage_for", spy)
    facade = types.SimpleNamespace(TestResult=harness_model.TestResult)
    result = harness_runner._run_single_test(
        facade, WORKSPACE_ROOT, CORPUS / _FVV, 0, 1, 1, tmp_path, False
    )
    assert seen["source"] == original
    covered, uncovered = _clone_entries(result.goal_coverage)
    assert covered == [] and len(uncovered) == 1, result.goal_coverage
