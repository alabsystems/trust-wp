"""Crediting policy for `expect: reject` adversarial cases (wp-s47 v2).

A rejection is credited only when trust-wp delivered it: a verifier verdict
with a TRUST_WP_RESULT line, or a named trust-wp refusal. A rustc compile
error, a run without a wire line, an undeclared error, or a crash is TEETH LOST.
"""
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import run_adversarial as ra  # noqa: E402

WIRE_FIELDS = (
    "verified failed errors warnings assumed trusted skipped verified_with_axiom_deps "
    "unverified_axioms vacuous evidence_gaps proof_assert_verified proof_assert_inconclusive "
    "verified_native_only proof_assert_failed proof_assert_errors panics demoted parse_errors "
    "termination_errors logic_recursion_errors erasure_errors"
).split()


def wire(base: int = 2, **counts: int) -> str:
    fields = {name: 0 for name in WIRE_FIELDS}
    fields.update(counts)
    return f"TRUST_WP_RESULT:v1 base_exit_code={base} " + " ".join(f"{k}={v}" for k, v in fields.items())


def case(**directives: str) -> ra.Case:
    return ra.Case(path=Path("x.rs"), name="x", directives={"expect": "reject", "mechanism": "m", **directives})


RUSTC_FAIL = (
    "error: extern blocks must be unsafe\n --> src/lib.rs:7:1\n"
    "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
)
REFUSAL = "error: trust-wp: `x_current` is spelled as a name the verifier derives from `x`; rename it\n"


def judge(c: ra.Case, output: str, exit_code: int | None = 2) -> tuple[str, bool, str]:
    verdict = ra.classify(False, output, exit_code)
    ok, note = ra.evaluate(c, verdict, output, exit_code)
    return verdict, ok, note


def test_rustc_compile_error_is_teeth_lost():
    verdict, ok, note = judge(case(), RUSTC_FAIL, 3)
    assert verdict == ra.ERROR and not ok
    assert "no TRUST_WP_RESULT line" in note and "extern blocks must be unsafe" in note


def test_rustc_error_cannot_satisfy_refused_with():
    c = case(verdict="error", **{"refused-with": "extern blocks must be unsafe"})
    _, ok, note = judge(c, RUSTC_FAIL + wire())
    assert not ok and "not reported by trust-wp itself" in note


def test_named_trust_wp_refusal_is_credited():
    c = case(verdict="error", **{"refused-with": "is spelled as a name the verifier derives from `x`"})
    verdict, ok, note = judge(c, REFUSAL + wire())
    assert (verdict, ok) == (ra.ERROR, True), note


def test_prefix_style_refusal_is_credited():
    c = case(verdict="error", **{"refused-with": "shadows a standard or spec-library path root"})
    out = "trust-wp: error: local item `crate::std` shadows a standard or spec-library path root\n" + wire(errors=1)
    verdict, ok, note = judge(c, out)
    assert (verdict, ok) == (ra.ERROR, True), note


def test_named_refusal_without_wire_line_is_teeth_lost():
    c = case(verdict="error", **{"refused-with": "is spelled as a name"})
    _, ok, note = judge(c, REFUSAL)
    assert not ok and "no TRUST_WP_RESULT line" in note


def test_undeclared_error_verdict_is_teeth_lost():
    _, ok, note = judge(case(), REFUSAL + wire())
    assert not ok and "named trust-wp refusal" in note


def test_verifier_failure_with_wire_is_credited():
    out = "trust-wp: f FAILED ✗ (postcondition)\ntrust-wp: 0 verified, 1 failed, 0 errors\n" + wire(1, failed=1)
    verdict, ok, note = judge(case(), out, 1)
    assert (verdict, ok) == (ra.FAILED, True), note


def test_verifier_failure_text_without_wire_is_teeth_lost():
    out = "trust-wp: f FAILED ✗ (postcondition)\ntrust-wp: 0 verified, 1 failed, 0 errors\n"
    verdict, ok, _ = judge(case(), out, 1)
    assert verdict == ra.FAILED and not ok


def test_inconclusive_proof_assert_reads_wire_counters_as_unknown():
    out = (
        "trust-wp: proof_assert in c::f inconclusive (quantifier-unhandled) — function has no contracts\n"
        "trust-wp: 0 verified, 0 failed, 0 errors\n" + wire(proof_assert_inconclusive=1)
    )
    verdict, ok, note = judge(case(), out)
    assert (verdict, ok) == (ra.UNKNOWN, True), note


def test_harness_timeout_without_wire_is_teeth_lost():
    verdict, ok, _ = judge(case(), "Timeout after 120s\n", None)
    assert verdict == ra.TIMEOUT and not ok


@pytest.mark.parametrize(
    "output, code",
    [
        ("thread 'rustc' panicked at src/x.rs:1:1\n" + wire(1, failed=1) + "\ntrust-wp: 0 verified, 1 failed, 0 errors", 1),
        (wire(1, failed=1, panics=1) + "\ntrust-wp: 0 verified, 1 failed, 0 errors", 1),
        ("error: internal compiler error: boom\n" + wire(), 2),
        ("trust-wp: 0 verified, 1 failed, 0 errors\n" + wire(1, failed=1), 101),
    ],
)
def test_crash_is_teeth_lost_even_with_a_failure_verdict(output, code):
    _, ok, note = judge(case(), output, code)
    assert not ok and "CRASH" in note


def test_accept_is_still_a_false_accept():
    ok, note = ra.evaluate(case(), ra.ACCEPTED, "", 0)
    assert not ok and "FALSE ACCEPT" in note


def test_controls_are_unchanged():
    c = ra.Case(path=Path("x.rs"), name="x", directives={"expect": "verify", "mechanism": "m"})
    assert ra.evaluate(c, ra.ACCEPTED, "", 0)[0]
    assert not ra.evaluate(c, ra.ERROR, RUSTC_FAIL, 2)[0]


def test_verdict_error_without_refused_with_is_a_load_error(tmp_path):
    (tmp_path / "bad.rs").write_text("//@ expect: reject\n//@ mechanism: m\n//@ verdict: error\nfn f() {}\n")
    with pytest.raises(RuntimeError, match="requires `refused-with:`"):
        ra.load_cases(tmp_path, None)


def test_every_shipped_error_verdict_names_its_refusal():
    cases = ra.load_cases(Path(__file__).resolve().parent / "cases", None)
    for c in cases:
        if c.directives.get("verdict") == ra.ERROR:
            assert c.directives.get("refused-with"), c.name


# ---------------------------------------------------------------------------
# Parallel execution: the schedule must not be observable in the results.
# ---------------------------------------------------------------------------


def _control(name: str) -> ra.Case:
    return ra.Case(
        path=Path(f"{name}.rs"),
        name=name,
        directives={"expect": "verify", "mechanism": "m"},
    )


def _fake_run_case(monkeypatch, seen: list[tuple[str, str]]):
    """Record (case, worker target) and finish in an order the caller did not ask for."""
    import random
    import time

    def fake(workspace, case, target, timeout_sec, verbose):
        time.sleep(random.uniform(0, 0.02))
        seen.append((case.name, str(target)))
        return ra.Outcome(
            case=case, verdict=ra.ACCEPTED, duration_ms=1, ok=True, note="verified", output=""
        )

    monkeypatch.setattr(ra, "run_case", fake)


def test_results_come_back_in_case_order_not_completion_order(monkeypatch, tmp_path, capsys):
    seen: list[tuple[str, str]] = []
    _fake_run_case(monkeypatch, seen)
    monkeypatch.setattr(ra, "clone_target_dir", lambda seed, dest: dest.mkdir(parents=True))
    cases = [_control(f"c{index:02d}") for index in range(24)]

    outcomes = ra.run_cases_parallel(tmp_path, cases, tmp_path / "seed", 10, False, False, 4)

    assert [o.case.name for o in outcomes] == [c.name for c in cases]
    printed = [line.split()[1] for line in capsys.readouterr().out.splitlines() if line.startswith("[")]
    assert printed == [c.name for c in cases]


def test_each_concurrent_case_gets_its_own_target_dir(monkeypatch, tmp_path):
    # Two cases sharing a target dir would delete each other's `creusot_test`
    # artifacts mid-compile, so a worker must never hand its target to a peer
    # while it is still running.
    import threading

    live: dict[str, str] = {}
    collisions: list[str] = []
    guard = threading.Lock()

    def fake(workspace, case, target, timeout_sec, verbose):
        with guard:
            if str(target) in live.values():
                collisions.append(case.name)
            live[case.name] = str(target)
        try:
            return ra.Outcome(
                case=case, verdict=ra.ACCEPTED, duration_ms=1, ok=True, note="verified", output=""
            )
        finally:
            with guard:
                del live[case.name]

    monkeypatch.setattr(ra, "run_case", fake)
    monkeypatch.setattr(ra, "clone_target_dir", lambda seed, dest: dest.mkdir(parents=True))
    cases = [_control(f"c{index:02d}") for index in range(40)]

    ra.run_cases_parallel(tmp_path, cases, tmp_path / "seed", 10, False, False, 6)
    assert collisions == []


def test_one_job_reuses_the_warm_seed_target(monkeypatch, tmp_path):
    # A single worker has nothing to race with, so cloning would only throw the
    # warm dependency cache away.
    targets: list[str] = []
    monkeypatch.setattr(
        ra,
        "clone_target_dir",
        lambda seed, dest: pytest.fail("--jobs 1 must not clone the target dir"),
    )
    monkeypatch.setattr(
        ra,
        "run_case",
        lambda workspace, case, target, timeout_sec, verbose: (
            targets.append(str(target))
            or ra.Outcome(case=case, verdict=ra.ACCEPTED, duration_ms=1, ok=True, note="", output="")
        ),
    )
    seed = tmp_path / "seed"

    ra.run_cases_parallel(tmp_path, [_control("c0"), _control("c1")], seed, 10, False, False, 1)
    assert targets == [str(seed), str(seed)]


def test_default_jobs_leaves_headroom(monkeypatch):
    for cpus, expected in ((14, 8), (8, 2), (4, 1), (1, 1)):
        monkeypatch.setattr(ra.os, "cpu_count", lambda cpus=cpus: cpus)
        assert ra.default_jobs() == expected


def test_changed_since_selects_only_touched_cases(tmp_path):
    import subprocess

    repo = tmp_path / "repo"
    (repo / "cases").mkdir(parents=True)
    run = lambda *argv: subprocess.run(argv, cwd=repo, check=True, capture_output=True)
    run("git", "init", "-q")
    run("git", "config", "user.email", "t@example.com")
    run("git", "config", "user.name", "t")
    (repo / "cases" / "old.rs").write_text("//@ expect: reject\n")
    run("git", "add", "-A")
    run("git", "commit", "-qm", "base")
    base = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo, capture_output=True, text=True
    ).stdout.strip()
    (repo / "cases" / "touched.rs").write_text("//@ expect: reject\n// edited\n")
    (repo / "cases" / "old.rs").write_text("//@ expect: reject\n// edited\n")

    names = ra.changed_case_names(repo / "cases", base)
    assert names == {"touched", "old"}


# --- a reject case credits no verification it does not declare ---------------
#
# The process verdict is a whole-crate summary, so one FAILING function makes the
# run a rejection while a SECOND function in the same crate is credited `verified`
# on a contract that is false. These pin the per-function half of the gate.

VERIFIED_AND_FAILED = (
    "trust-wp: helper verified ✓\n"
    "trust-wp: target FAILED ✗\n"
    "trust-wp: 1 verified, 1 failed, 0 errors\n" + wire(base=1, verified=1, failed=1)
)


def test_verified_functions_reads_every_credited_spelling():
    output = (
        "trust-wp: plain verified ✓\n"
        "trust-wp: axiomatic verified* (depends on 1 unverified axiom(s))\n"
        "trust-wp: empty verified ✓ (vacuous: explicit #[requires(false)])\n"
        "trust-wp: beaten FAILED ✗\n"
    )
    assert ra.verified_functions(output) == ["plain", "axiomatic", "empty"]


def test_undeclared_verified_function_loses_teeth():
    ok, note = ra.evaluate(case(), ra.FAILED, VERIFIED_AND_FAILED, exit_code=1)
    assert not ok
    assert "TEETH LOST" in note and "helper" in note


def test_declared_verified_function_is_credited():
    ok, _ = ra.evaluate(
        case(**{"also-verified": "helper"}), ra.FAILED, VERIFIED_AND_FAILED, exit_code=1
    )
    assert ok


def test_declaration_is_a_list_and_does_not_cover_a_new_name():
    output = VERIFIED_AND_FAILED.replace("helper verified", "other verified")
    ok, note = ra.evaluate(
        case(**{"also-verified": "helper, third"}), ra.FAILED, output, exit_code=1
    )
    assert not ok and "other" in note


def test_also_verified_is_reject_only(tmp_path):
    (tmp_path / "c.rs").write_text(
        "//@ expect: verify\n//@ mechanism: m\n//@ also-verified: f\nfn main() {}\n"
    )
    with pytest.raises(RuntimeError, match="only apply to `expect: reject`"):
        ra.load_cases(tmp_path, None)


def test_also_verified_may_not_be_repeated(tmp_path):
    (tmp_path / "c.rs").write_text(
        "//@ expect: reject\n//@ mechanism: m\n//@ also-verified: a\n//@ also-verified: b\nfn main(){}\n"
    )
    with pytest.raises(RuntimeError):
        ra.load_cases(tmp_path, None)


def test_a_lane_credit_is_not_a_contract_credit():
    # These name the lane that passed and claim nothing about the function's contract.
    # A recursive function can carry `verified ✓ (termination)` while the call-site
    # precondition merged into its own obligations is false in the very same run.
    assert ra.verified_functions("trust-wp: countdown2 verified ✓ (termination)\n") == []
    assert ra.verified_functions("trust-wp: f verified ✓ (loop invariant, 2 of 2)\n") == []
    assert ra.verified_functions("trust-wp: foo refinement verified ✓\n") == []
    assert ra.verified_functions("trust-wp: proof_assert in c::f verified ✓\n") == []


def test_an_axiom_dependent_credit_is_still_a_credit():
    out = "trust-wp: a verified* (depends on 1 unverified axiom(s))\n"
    assert ra.verified_functions(out) == ["a"]


def test_the_run_summary_is_not_read_as_a_function_name():
    assert ra.verified_functions("trust-wp: 3 verified, 1 failed, 0 errors\n") == []
    assert ra.verified_functions("trust-wp: proof_assert: 3 verified, 0 failed, 2 errors\n") == []


# --- a withdrawn credit is not a credit --------------------------------------
#
# The driver prints `verified` when a function finishes and withdraws the credit at
# the end of the run when it rests, through any chain of calls, on a trait contract
# an impl never discharged. The `verified` line cannot be unprinted, so the gate has
# to read the withdrawal.

WITHDRAWN = (
    "trust-wp: gen_read verified ✓\n"
    "trust-wp: go verified ✓\n"
    "trust-wp: unrelated verified ✓\n"
    "trust-wp: <W as Rd>::rd trait refinement FAILED ✗\n"
    "trust-wp: gen_read error: verdict withdrawn - it assumed trait method contract "
    "`Rd::rd` (`<W as Rd>::rd` did not establish the refinement goal)\n"
    "  a caller may not assume a trait contract its impl never discharged\n"
    "trust-wp: go error: verdict withdrawn - through `gen_read`, it assumed trait method "
    "contract `Rd::rd` (`<W as Rd>::rd` did not establish the refinement goal)\n"
    "  a caller may not assume a trait contract its impl never discharged\n"
    "trust-wp: 1 verified, 1 failed, 2 errors\n" + wire(base=1, verified=1, failed=1, errors=2)
)


def test_a_withdrawn_credit_is_subtracted_from_the_verified_functions():
    assert ra.withdrawn_functions(WITHDRAWN) == ["gen_read", "go"]
    assert ra.verified_functions(WITHDRAWN) == ["unrelated"]


def test_a_withdrawn_credit_needs_no_declaration():
    ok, note = ra.evaluate(
        case(**{"also-verified": "unrelated"}), ra.FAILED, WITHDRAWN, exit_code=1
    )
    assert ok, note


def test_a_standing_credit_beside_a_withdrawal_still_needs_its_declaration():
    ok, note = ra.evaluate(case(), ra.FAILED, WITHDRAWN, exit_code=1)
    assert not ok
    assert "unrelated" in note and "gen_read" not in note and "go," not in note


def test_only_the_withdrawal_line_withdraws():
    # The name has to be the one the withdrawal line opens with: a mention inside
    # another function's blame text, or an ordinary error, withdraws nothing.
    out = (
        "trust-wp: go verified ✓\n"
        "trust-wp: gen_read verified ✓\n"
        "trust-wp: other error: verdict withdrawn - through `go`, it assumed trait "
        "method contract `Rd::rd` (`<W as Rd>::rd` did not prove it)\n"
        "trust-wp: gen_read error: body extraction incomplete\n"
    )
    assert ra.withdrawn_functions(out) == ["other"]
    assert ra.verified_functions(out) == ["go", "gen_read"]


# --- a function whose own assertion fails is not verified ---------------------

CONTRADICTED = (
    "trust-wp: inc verified ✓\n"
    "trust-wp: copy_source_wrong verified ✓\n"
    "trust-wp: proof_assert in creusot_test::copy_source_wrong FAILED ✗\n"
    "trust-wp: 2 verified, 0 failed, 0 errors\n" + wire(base=1, verified=2, proof_assert_failed=1)
)


def test_a_credit_beside_its_own_failed_assertion_is_contradicted():
    assert ra.contradicted_credits(CONTRADICTED) == ["copy_source_wrong"]


def test_an_unknown_assertion_contradicts_the_credit_too():
    out = CONTRADICTED.replace("FAILED ✗", "unknown (sort-coercion bridge)")
    assert ra.contradicted_credits(out) == ["copy_source_wrong"]


def test_declaring_a_contradicted_credit_does_not_excuse_it():
    ok, note = ra.evaluate(
        case(**{"also-verified": "inc, copy_source_wrong"}), ra.FAILED, CONTRADICTED, exit_code=1
    )
    assert not ok and "proof_assert is not proved: copy_source_wrong" in note


def test_a_lane_credit_beside_its_own_unproved_assertion_is_contradicted():
    # The loop-invariant and termination lanes own the verdict of a function they
    # credit; its own assertion is part of that verdict all the same.
    for lane in ("(loop invariant)", "(loop invariant + call obligations)", "(termination)"):
        out = (
            f"trust-wp: f verified ✓ {lane}\n"
            "trust-wp: proof_assert in creusot_test::f FAILED ✗\n"
            + wire(base=1, verified=1, proof_assert_failed=1)
        )
        assert ra.contradicted_credits(out) == ["f"], lane


def test_a_lane_credit_beside_a_refuted_contract_is_not_contradicted():
    # Only an unproved ASSERTION contradicts a lane credit here; a lane credit beside
    # a function-level FAILED is the lane-only rule's business, not this one's.
    out = (
        "trust-wp: f verified ✓ (termination)\n"
        "trust-wp: f FAILED ✗ (postcondition)\n" + wire(base=1, verified=1, failed=1)
    )
    assert ra.contradicted_credits(out) == []


def test_a_refinement_credit_is_not_a_verdict_on_the_body():
    out = (
        "trust-wp: f refinement verified ✓\n"
        "trust-wp: proof_assert in creusot_test::f FAILED ✗\n"
        + wire(base=1, proof_assert_failed=1)
    )
    assert ra.contradicted_credits(out) == []


def test_an_assertion_in_another_function_contradicts_nothing():
    out = CONTRADICTED.replace("in creusot_test::copy_source_wrong", "in creusot_test::other")
    assert ra.contradicted_credits(out) == []


def control(**directives: str) -> ra.Case:
    return ra.Case(path=Path("x.rs"), name="x", directives={"expect": "verify", "mechanism": "m", **directives})


FAILED_RUN = "trust-wp: g FAILED\n\ntrust-wp: 1 verified, 1 failed, 0 errors\n" + wire(base=1, verified=1, failed=1)
UNKNOWN_RUN = "trust-wp: g unknown (refutation withheld)\n\ntrust-wp: 1 verified, 0 failed, 1 errors\n" + wire(errors=1)


def test_an_xfail_control_may_be_rejected_with_any_flavour_by_default():
    c = control(xfail="priced")
    assert ra.evaluate(c, ra.classify(False, FAILED_RUN, 1), FAILED_RUN, 1)[0]
    assert ra.evaluate(c, ra.classify(False, UNKNOWN_RUN, 2), UNKNOWN_RUN, 2)[0]


def test_a_pinned_xfail_control_that_starts_failing_is_an_over_refusal():
    c = control(xfail="priced", **{"xfail-verdict": "unknown"})
    assert ra.classify(False, FAILED_RUN, 1) == ra.FAILED
    ok, note = ra.evaluate(c, ra.FAILED, FAILED_RUN, 1)
    assert not ok and "xfail-verdict: unknown" in note
    assert ra.evaluate(c, ra.classify(False, UNKNOWN_RUN, 2), UNKNOWN_RUN, 2)[0]
    assert ra.evaluate(c, ra.ACCEPTED, "", 0)[0], "an xpass is still reported as one"


@pytest.mark.parametrize(
    "header",
    [
        "//@ expect: verify\n//@ mechanism: m\n//@ xfail-verdict: unknown\n",
        "//@ expect: verify\n//@ mechanism: m\n//@ xfail: r\n//@ xfail-verdict: maybe\n",
        "//@ expect: verify\n//@ mechanism: m\n//@ xfail: r\n//@ xfail-verdict: unknown\n"
        "//@ xfail-verdict: failed\n",
    ],
)
def test_a_malformed_xfail_verdict_is_a_load_error(tmp_path, header):
    (tmp_path / "bad.rs").write_text(header + "fn f() {}\n")
    with pytest.raises(RuntimeError):
        ra.load_cases(tmp_path, None)


# --- a trait impl's credit is read by its qualified name ----------------------
#
# The driver names a function by `def_path_str`, and a trait impl method's path has
# spaces: `<S as Inc>::inc`. A name read up to the first space stopped at `<S`, so every
# impl credit in the reject corpus was invisible to the undeclared-credit and the
# contradicted-credit checks alike.

IMPL_CREDITS = (
    "trust-wp: <S as Inc>::inc verified ✓\n"
    "trust-wp: <Zero as creusot_std::Invariant>::invariant verified ✓\n"
    "trust-wp: <W as Rd>::rd verified* (depends on 1 unverified axiom(s))\n"
    "trust-wp: <V as Rd>::rd verified ✓ (vacuous: explicit #[requires(false)])\n"
    "trust-wp: target FAILED ✗\n"
    "trust-wp: 4 verified, 1 failed, 0 errors, 1 verified* (unproven axiom deps)\n"
    + wire(base=1, verified=4, failed=1, verified_with_axiom_deps=1)
)


def test_an_impl_credit_is_read_by_its_qualified_name():
    assert ra.verified_functions(IMPL_CREDITS) == [
        "<S as Inc>::inc",
        "<Zero as creusot_std::Invariant>::invariant",
        "<W as Rd>::rd",
        "<V as Rd>::rd",
    ]


@pytest.mark.parametrize(
    "name",
    [
        "m::<impl Tr for S>::f",
        "<(u8, u16) as Tr<(i32, bool)>>::m",
        "<[u8; 4] as Tr>::m",
        "<fn(u8) -> u8 as Tr>::m",
        "<&'a mut S as Tr>::m",
        "<S as Inc>::inc::{closure#0}",
    ],
)
def test_every_def_path_spelling_is_one_name(name):
    assert ra.verified_functions(f"trust-wp: {name} verified ✓\n") == [name]


def test_an_undeclared_impl_credit_loses_teeth():
    ok, note = ra.evaluate(case(), ra.FAILED, IMPL_CREDITS, exit_code=1)
    assert not ok and "TEETH LOST" in note
    assert "<S as Inc>::inc" in note and "<Zero as creusot_std::Invariant>::invariant" in note


def test_an_impl_credit_is_declared_exactly_as_printed():
    declared = (
        "<S as Inc>::inc, <Zero as creusot_std::Invariant>::invariant, "
        "<W as Rd>::rd, <V as Rd>::rd"
    )
    ok, note = ra.evaluate(
        case(**{"also-verified": declared}), ra.FAILED, IMPL_CREDITS, exit_code=1
    )
    assert ok, note
    # The bare method name is a different function, and so is another impl of it.
    for partial in ("inc, invariant, rd", declared.replace("<S as Inc>", "<T as Inc>")):
        ok, note = ra.evaluate(
            case(**{"also-verified": partial}), ra.FAILED, IMPL_CREDITS, exit_code=1
        )
        assert not ok and "<S as Inc>::inc" in note, partial


@pytest.mark.parametrize(
    "line",
    [
        "trust-wp: 3 verified, 1 failed, 0 errors",
        "trust-wp: 3 verified, 1 failed, 0 errors, 2 verified* (unproven axiom deps)",
        "trust-wp: proof_assert: 3 verified, 0 failed, 2 errors",
        "trust-wp: <S as Inc>::inc verified ✓ (termination)",
        "trust-wp: <S as Inc>::inc verified ✓ (loop invariant)",
        "trust-wp: <S as Inc>::inc verified ✓ (loop invariant + call obligations)",
        "trust-wp: <S as Inc>::inc verified ✓ (loop invariant vacuous: explicit #[requires(false)])",
        "trust-wp: <S as Inc>::inc refinement verified ✓",
        "trust-wp: proof_assert in creusot_test::<S as Inc>::inc verified ✓",
        "trust-wp: proof_assert in creusot_test::<S as Inc>::inc verified ✓ (vacuous: explicit #[requires(false)])",
        "trust-wp: <S as Inc>::inc loop invariant verified ✓ — continuing to post-loop verification",
        "trust-wp: <S as Inc>::inc loop induction verified ✓, postcondition deferred to function-level path",
        "trust-wp:   variant decrease verified at call site 0 (1 path condition(s))",
    ],
)
def test_no_other_verified_spelling_is_a_contract_credit(line):
    assert ra.verified_functions(line + "\n") == []
    assert ra.unattributed_credit_lines(line + "\n") == []


@pytest.mark.parametrize(
    "line",
    [
        "trust-wp: <S as Inc>::inc (native) verified ✓",
        "trust-wp: <S as Inc verified ✓",
        "trust-wp:  f verified ✓",
    ],
)
def test_a_tick_the_gate_cannot_attribute_loses_teeth(line):
    # An unread credit is how every impl method escaped; a new spelling is reported
    # until the gate is taught it, never skipped.
    out = line + "\ntrust-wp: target FAILED ✗\n" + wire(base=1, failed=1)
    assert ra.verified_functions(out) == []
    assert ra.unattributed_credit_lines(out) == [line.removeprefix("trust-wp: ").strip()]
    ok, note = ra.evaluate(case(), ra.FAILED, out, exit_code=1)
    assert not ok and "cannot attribute" in note


def test_an_impl_credit_is_contradicted_by_its_own_assertion_only():
    out = (
        "trust-wp: <S as Inc>::inc verified ✓\n"
        "trust-wp: <T as Inc>::inc verified ✓ (termination)\n"
        "trust-wp: inc verified ✓\n"
        "trust-wp: proof_assert in creusot_test::<S as Inc>::inc FAILED ✗\n"
        + wire(base=1, verified=3, proof_assert_failed=1)
    )
    assert ra.contradicted_credits(out) == ["<S as Inc>::inc"]
    lane = out.replace("proof_assert in creusot_test::<S as", "proof_assert in creusot_test::<T as")
    assert ra.contradicted_credits(lane.replace("FAILED ✗", "unknown (x)")) == ["<T as Inc>::inc"]


def test_an_impl_credit_is_withdrawn_by_its_qualified_name():
    out = (
        "trust-wp: <W as Rd2>::rd2 verified ✓\n"
        "trust-wp: <W as Rd2>::rd2 error: verdict withdrawn - through `go`, it assumed "
        "trait method contract `Rd::rd` (`<W as Rd>::rd` did not establish the refinement goal)\n"
    )
    assert ra.withdrawn_functions(out) == ["<W as Rd2>::rd2"]
    assert ra.verified_functions(out) == []


def test_a_declaration_splits_only_at_top_level_commas():
    assert ra.parse_def_path_list("a, <(u8, u16) as Tr>::m,<S as Inc>::inc ,") == [
        "a",
        "<(u8, u16) as Tr>::m",
        "<S as Inc>::inc",
    ]


@pytest.mark.parametrize("value", ["a b", "a, b c", "<S as Inc::inc", "S>::inc"])
def test_a_declaration_that_is_not_a_def_path_list_is_a_load_error(tmp_path, value):
    (tmp_path / "c.rs").write_text(
        f"//@ expect: reject\n//@ mechanism: m\n//@ also-verified: {value}\nfn main(){{}}\n"
    )
    with pytest.raises(RuntimeError, match="also-verified"):
        ra.load_cases(tmp_path, None)


def test_a_logic_function_credit_is_contradicted_by_its_own_assertion():
    # A logic function's credit carries the crate, exactly as its assertion line does
    # (`logic_fn_verify` prints the crate-qualified path), so the path with the crate
    # removed is not its name; a DECLARED logic credit beside its own failed assertion
    # must still be flagged.
    out = (
        "trust-wp: creusot_test::one verified ✓\n"
        "trust-wp: one is a logic function (postcondition will be verified)\n"
        "trust-wp: proof_assert in creusot_test::one FAILED ✗\n"
        + wire(base=1, verified=1, proof_assert_failed=1)
    )
    assert ra.contradicted_credits(out) == ["creusot_test::one"]
    ok, note = ra.evaluate(
        case(**{"also-verified": "creusot_test::one"}), ra.FAILED, out, exit_code=1
    )
    assert not ok and "proof_assert is not proved: creusot_test::one" in note


# --- an unproved assertion is unproved whatever the word ----------------------
#
# Every spelling the driver can print for a `proof_assert!` outcome, read off its
# source. The gate used to read only `FAILED` and `unknown` as contradicting a credit,
# so an assertion reported `error`, `assumed`, `inconclusive` or as an evidence gap
# let its function's credit stand.

PROVED, NOT_A_GOAL, UNPROVED, UNNAMED, NOT_AN_OUTCOME = (
    "proved",
    "not-a-goal",
    "unproved",
    "unnamed",
    "not-an-outcome",
)

# Keyed by the driver's literal with every placeholder written `{}` and the ticks
# decoded. `test_the_table_is_every_spelling_the_driver_prints` keeps it complete.
ASSERTION_SPELLINGS = {
    "trust-wp: proof_assert in {} verified ✓": PROVED,
    "trust-wp: proof_assert in {} verified ✓ (vacuous: explicit #[requires(false)])": PROVED,
    "trust-wp: proof_assert in {} trusted (skipped)": NOT_A_GOAL,
    "trust-wp: proof_assert in {}::{} trusted: not assumed ({}); the function is proved "
    "without it": NOT_A_GOAL,
    "trust-wp: proof_assert in {} proved, not credited: the function's postcondition is "
    "not proved": NOT_A_GOAL,
    "trust-wp: proof_assert in {} FAILED ✗": UNPROVED,
    "trust-wp: proof_assert in {} unknown ({})": UNPROVED,
    "trust-wp: proof_assert in {} unknown": UNPROVED,
    "trust-wp: error: logic function body for {} parsed without one of its proof_assert!s, "
    "a goal of the function; refused": UNPROVED,
    "trust-wp: proof_assert in {} error: {}": UNPROVED,
    # D-237 cannot prove a goal whose binding identity is unresolved. A
    # dropped trusted assumption, in contrast, adds no unproved user goal.
    "trust-wp: proof_assert in {} error: `{}` is bound more than once in the body "
    "and the binding the assertion names cannot be told (fail-closed)": UNPROVED,
    # D-129's refusals: a final value of a borrow the asserted value holds, and a local
    # a holder of its borrow may have written before the assertion.
    "trust-wp: proof_assert in {} error: final value refused (fail-closed): {}": UNPROVED,
    "trust-wp: proof_assert in {} error: stale read refused (fail-closed): `{}` is read after "
    "a write through a value that holds a borrow of it, which this lane does not apply to "
    "`{}`": UNPROVED,
    # D-185's refusal: a name whose memory a write may have changed before the
    # assertion, read where the walk recorded no value for it.
    "trust-wp: proof_assert in {} error: stale read refused (fail-closed): `{}` is read at "
    "the assertion, but {}; its current value is not known to this lane": UNPROVED,
    "trust-wp: proof_assert in {} error: {}; refusing instead of binding the fields in "
    "the order they were written, which would bind one field as another": UNPROVED,
    "trust-wp: proof_assert in {} error: {} (in a post-loop assumption); refusing instead "
    "of binding the fields in the order they were written, which would bind one field as "
    "another": UNPROVED,
    "trust-wp: proof_assert in {} assumed ({}) — counted as error": UNPROVED,
    "trust-wp: proof_assert in {} inconclusive ({}) — function has no contracts": UNPROVED,
    "trust-wp: proof_assert in {} evidence gap ({})": UNPROVED,
    "trust-wp: proof_assert in {} has no expression text": UNPROVED,
    "trust-wp: {} proof_assert skipped (crate wall-clock budget exhausted) (#2674)": UNPROVED,
    "trust-wp: {} ay solver panic during proof_assert: {}": UNPROVED,
    "trust-wp: {} panicked during proof_assert: {}": UNPROVED,
    "trust-wp: {} ay solver panic during standalone proof_assert: {}": UNPROVED,
    "trust-wp: {} panicked during standalone proof_assert: {}": UNPROVED,
    "trust-wp: {} FAILED ✗ (proof_assert)": UNPROVED,
    "trust-wp: {} unknown (proof_assert not proved)": UNPROVED,
    "trust-wp: {} error: verdict withdrawn - its own proof_assert was not proved": UNPROVED,
    "trust-wp: error: failed to parse proof_assert '{}': {}": UNNAMED,
    "trust-wp: frontend diagnostic: mismatched types in proof_assert '{}' at {}: expected "
    "`bool`, found a non-boolean expression": UNNAMED,
    "trust-wp: proof_assert: {}": NOT_AN_OUTCOME,
    "trust-wp: verifying proof_assert in {} ({} contract preconditions)": NOT_AN_OUTCOME,
    "trust-wp: warning: dropped trusted proof_assert in {}: '{}': {}": NOT_AN_OUTCOME,
    "trust-wp: warning: dropped trusted proof_assert in {}: `{}` names no one binding "
    "there (D-237)": NOT_AN_OUTCOME,
    "trust-wp: {} proof_assert assumption(s) injected without proof": NOT_AN_OUTCOME,
    # D-139's refusals of a ghost compared in program code; they name `proof_assert!`
    # only as the place to write the comparison instead.
    "trust-wp: ghost values are compared outside ghost!(...); `==` on a `Ghost` or "
    "`Snapshot` is `true` at run time whatever the values. Compare them in ghost!(...) or "
    "a proof_assert!": NOT_AN_OUTCOME,
    "trust-wp: a value holding a `Ghost` or `Snapshot` is compared or hashed outside "
    "ghost!(...); the ghost's run-time `eq` is `true` and its `hash` a constant whatever "
    "the values. Compare them in ghost!(...) or a proof_assert!": NOT_AN_OUTCOME,
}
# Printed by `report_snapshot_error` as `trust-wp: error: {reason}`, so the literal the
# driver holds is only the reason and the scan below does not see it.
SNAPSHOT_ERROR_SPELLING = "trust-wp: error: proof_assert in {} missing MIR location"

_DRIVER_SRC = Path(__file__).resolve().parents[2] / "crates" / "trust-wp-driver" / "src"


def _driver_assertion_literals() -> set[str]:
    """Every `"trust-wp: ..."` literal in the driver that mentions `proof_assert`."""
    import re

    literals: set[str] = set()
    for path in _DRIVER_SRC.rglob("*.rs"):
        if "tests" in path.relative_to(_DRIVER_SRC).parts or path.stem.endswith("tests"):
            continue
        source = path.read_text(encoding="utf-8")
        for match in re.finditer(r'"(trust-wp: (?! )(?:[^"\\]|\\.|\\\n)*)"', source):
            text = re.sub(r"\\\n\s*", "", match.group(1))
            text = text.replace("\\u{2713}", "✓").replace("\\u{2717}", "✗")
            text = re.sub(r"\{[^{}]*\}", "{}", text)
            if "proof_assert" in text:
                literals.add(text)
    return literals


def test_the_table_is_every_spelling_the_driver_prints():
    # A new outcome spelling in the driver fails here until someone decides what it
    # means for a credit, and a retired one leaves the table.
    assert _DRIVER_SRC.is_dir(), _DRIVER_SRC
    assert _driver_assertion_literals() == set(ASSERTION_SPELLINGS)


def _instantiate(spelling: str) -> str:
    """A concrete line: the function is `f` (crate-qualified after `proof_assert in`)."""
    line = spelling.replace("proof_assert in {}", "proof_assert in creusot_test::f", 1)
    line = line.replace("logic function body for {}", "logic function body for creusot_test::f", 1)
    if line.startswith("trust-wp: {}"):
        line = "trust-wp: f" + line[len("trust-wp: {}"):]
    return line.replace("{}", "x")


@pytest.mark.parametrize(
    "spelling, kind",
    sorted({**ASSERTION_SPELLINGS, SNAPSHOT_ERROR_SPELLING: UNPROVED}.items()),
)
def test_every_assertion_spelling_is_read_for_what_it_means(spelling, kind):
    line = _instantiate(spelling) + "\n"
    credited = "trust-wp: f verified ✓\n" + line
    assert (ra.assertion_credits(line) == ["creusot_test::f"]) == (kind == PROVED)
    assert ("f" in ra.unproved_assertion_functions(line)) == (kind == UNPROVED)
    assert bool(ra.unnamed_unproved_assertion_lines(line)) == (kind == UNNAMED)
    assert ra.contradicted_credits(credited) == (["f"] if kind == UNPROVED else [])
    assert ra.unattributed_credit_lines(line) == []


@pytest.mark.parametrize(
    "outcome",
    ["assumed (x) — counted as error", "inconclusive (x) — function has no contracts",
     "evidence gap (x)", "error: unsupported"],
)
def test_a_declared_credit_beside_an_unproved_assertion_loses_teeth(outcome):
    out = (
        "trust-wp: f verified ✓\n"
        f"trust-wp: proof_assert in creusot_test::f {outcome}\n"
        "trust-wp: g FAILED ✗\n" + wire(base=1, verified=1, failed=1, proof_assert_errors=1)
    )
    ok, note = ra.evaluate(case(**{"also-verified": "f"}), ra.FAILED, out, exit_code=1)
    assert not ok and "proof_assert is not proved: f" in note


def test_an_assertion_outcome_the_gate_has_never_met_is_not_a_proof():
    out = "trust-wp: f verified ✓\ntrust-wp: proof_assert in creusot_test::f withheld (x)\n"
    assert ra.contradicted_credits(out) == ["f"]
    assert ra.assertion_credits(out) == []


def test_an_unfamiliar_tick_on_an_assertion_is_reported_not_read():
    line = "proof_assert in creusot_test::f verified ✓ (native only)"
    out = f"trust-wp: {line}\ntrust-wp: g FAILED ✗\n" + wire(base=1, failed=1)
    assert ra.assertion_credits(out) == []
    assert ra.unattributed_credit_lines(out) == [line]
    ok, note = ra.evaluate(case(), ra.FAILED, out, exit_code=1)
    assert not ok and "cannot attribute" in note


def test_an_unnamed_unproved_assertion_blocks_every_credit_beside_it():
    out = (
        "trust-wp: f verified ✓\n"
        "trust-wp: error: failed to parse proof_assert 'x >': unexpected end\n"
        "trust-wp: g FAILED ✗\n" + wire(base=1, verified=1, failed=1, parse_errors=1)
    )
    ok, note = ra.evaluate(case(**{"also-verified": "f"}), ra.FAILED, out, exit_code=1)
    assert not ok and "names no function" in note and "f" in note
    alone = out.replace("trust-wp: f verified ✓\n", "")
    ok, note = ra.evaluate(case(), ra.FAILED, alone, exit_code=1)
    assert ok, note


def test_a_trusted_assertion_contradicts_nothing():
    out = "trust-wp: f verified ✓\ntrust-wp: proof_assert in creusot_test::f trusted (skipped)\n"
    assert ra.contradicted_credits(out) == []


# --- an assertion credit in a reject case is declared -------------------------
#
# `proof_assert in X verified ✓` is a credit on a claim about the program at one point.
# The process verdict says nothing about it: a reject case whose FALSE assertion is
# printed verified passed as [ok] while its function failed for another reason.

ASSERTION_CREDIT = (
    "trust-wp: proof_assert in creusot_test::k verified ✓\n"
    "trust-wp: k FAILED ✗ (postcondition)\n"
    "trust-wp: 0 verified, 1 failed, 0 errors\n"
    "trust-wp: proof_assert: 1 verified, 0 failed, 0 errors\n"
    + wire(base=1, failed=1, proof_assert_verified=1)
)


def test_an_undeclared_assertion_credit_loses_teeth():
    ok, note = ra.evaluate(case(), ra.FAILED, ASSERTION_CREDIT, exit_code=1)
    assert not ok and "TEETH LOST" in note
    assert "also-verified-assertion" in note and "creusot_test::k (1 verified, 0 declared)" in note


def test_a_declared_assertion_credit_is_credited():
    c = case(**{"also-verified-assertion": "creusot_test::k"})
    ok, note = ra.evaluate(c, ra.FAILED, ASSERTION_CREDIT, exit_code=1)
    assert ok, note


def test_a_function_declaration_does_not_declare_its_assertions_and_back():
    for directives in ({"also-verified": "k"}, {"also-verified": "creusot_test::k"}):
        ok, note = ra.evaluate(case(**directives), ra.FAILED, ASSERTION_CREDIT, exit_code=1)
        assert not ok and "also-verified-assertion" in note, directives
    both = ASSERTION_CREDIT.replace("k FAILED ✗ (postcondition)", "k verified ✓")
    c = case(**{"also-verified-assertion": "creusot_test::k"})
    ok, note = ra.evaluate(c, ra.FAILED, both + "trust-wp: g FAILED ✗\n", exit_code=1)
    assert not ok and "`//@ also-verified:`: k" in note


def test_each_assertion_credit_is_declared_once():
    # The line names the function, not the assertion: a second proved assertion in a
    # declared function is a second credit, and only the count can tell.
    twice = ASSERTION_CREDIT.replace(
        "trust-wp: k FAILED", "trust-wp: proof_assert in creusot_test::k verified ✓\ntrust-wp: k FAILED"
    ).replace("proof_assert_verified=1", "proof_assert_verified=2")
    ok, note = ra.evaluate(
        case(**{"also-verified-assertion": "creusot_test::k"}), ra.FAILED, twice, exit_code=1
    )
    assert not ok and "creusot_test::k (2 verified, 1 declared)" in note
    ok, note = ra.evaluate(
        case(**{"also-verified-assertion": "creusot_test::k, creusot_test::k"}),
        ra.FAILED,
        twice,
        exit_code=1,
    )
    assert ok, note


def test_a_vacuous_assertion_credit_is_a_credit():
    out = ASSERTION_CREDIT.replace(
        "verified ✓\n", "verified ✓ (vacuous: explicit #[requires(false)])\n", 1
    )
    assert ra.assertion_credits(out) == ["creusot_test::k"]
    ok, note = ra.evaluate(case(), ra.FAILED, out, exit_code=1)
    assert not ok and "creusot_test::k (1 verified, 0 declared)" in note


def test_an_impl_or_closure_assertion_credit_is_read_by_its_qualified_name():
    out = (
        "trust-wp: proof_assert in creusot_test::<S as Inc>::inc verified ✓\n"
        "trust-wp: proof_assert in creusot_test::k::{closure#0} verified ✓\n"
    )
    assert ra.assertion_credits(out) == ["creusot_test::<S as Inc>::inc", "creusot_test::k::{closure#0}"]


def test_an_unproved_assertion_is_not_an_assertion_credit():
    out = ASSERTION_CREDIT.replace("verified ✓\n", "FAILED ✗\n", 1)
    assert ra.assertion_credits(out) == []


@pytest.mark.parametrize(
    "value, error",
    [
        ("k", "crate first"),
        ("creusot_test::k, m::<S as Tr>::f", None),
        ("creusot_test::k creusot_test::j", "not one def path"),
    ],
)
def test_an_assertion_declaration_is_spelled_as_the_line_prints_it(tmp_path, value, error):
    (tmp_path / "c.rs").write_text(
        f"//@ expect: reject\n//@ mechanism: m\n//@ also-verified-assertion: {value}\nfn main(){{}}\n"
    )
    if error is None:
        assert ra.load_cases(tmp_path, None)[0].directives["also-verified-assertion"] == value
    else:
        with pytest.raises(RuntimeError, match=error):
            ra.load_cases(tmp_path, None)


def test_also_verified_assertion_is_reject_only_and_single(tmp_path):
    (tmp_path / "c.rs").write_text(
        "//@ expect: verify\n//@ mechanism: m\n//@ also-verified-assertion: c::f\nfn main() {}\n"
    )
    with pytest.raises(RuntimeError, match="only apply to `expect: reject`"):
        ra.load_cases(tmp_path, None)
    (tmp_path / "c.rs").write_text(
        "//@ expect: reject\n//@ mechanism: m\n//@ also-verified-assertion: c::f\n"
        "//@ also-verified-assertion: c::g\nfn main() {}\n"
    )
    with pytest.raises(RuntimeError, match="repeated"):
        ra.load_cases(tmp_path, None)


# --- a withdrawn assertion credit is not a credit -----------------------------
#
# A trait-contract withdrawal takes back every credit its item banked, its proof_asserts
# included (D-94): `trait_credit_withdrawn_calls_away` prints `pa_user`'s FALSE
# assertion verified and then withdraws `pa_user`, and the run counts it an error.

TRAIT_WITHDRAWN_ASSERTION = (
    "trust-wp: <W as Rd>::rd FAILED ✗ (postcondition)\n"
    "trust-wp: proof_assert in creusot_test::pa_user verified ✓\n"
    "trust-wp: pa_user error: verdict withdrawn - through `go` -> `gen_read`, it assumed "
    "trait method contract `Rd::rd` (`<W as Rd>::rd` did not satisfy the contract it inherited)\n"
    "  a caller may not assume a trait contract its impl never discharged\n"
    "trust-wp: 0 verified, 1 failed, 1 errors\n"
    "trust-wp: proof_assert: 0 verified, 0 failed, 1 errors\n"
    + wire(base=1, failed=1, errors=1, proof_assert_errors=1)
)


def test_a_trait_withdrawal_takes_back_the_assertion_credits_of_its_function():
    assert ra.assertion_credits(TRAIT_WITHDRAWN_ASSERTION) == ["creusot_test::pa_user"]
    assert ra.standing_assertion_credits(TRAIT_WITHDRAWN_ASSERTION) == []
    ok, note = ra.evaluate(case(), ra.FAILED, TRAIT_WITHDRAWN_ASSERTION, exit_code=1)
    assert ok, note


@pytest.mark.parametrize(
    "blame",
    [
        "it assumed trait method contract `Rd::rd` (`<W as Rd>::rd` did not prove it)",
        "it reaches `m::f`, whose MIR the credit walk could not read while a trait method "
        "contract is undischarged",
        "through `go`, it reaches `m::f`, whose MIR the credit walk could not read",
    ],
)
def test_every_trait_withdrawal_spelling_takes_back_assertion_credits(blame):
    out = TRAIT_WITHDRAWN_ASSERTION.replace(
        "through `go` -> `gen_read`, it assumed trait method contract `Rd::rd` "
        "(`<W as Rd>::rd` did not satisfy the contract it inherited)",
        blame,
    )
    assert ra.standing_assertion_credits(out) == []


def test_the_own_assertion_withdrawal_leaves_the_assertion_credits_standing():
    # It takes back the FUNCTION's credit because another assertion of its own did not
    # prove; the assertions that did prove still count, in the driver and here.
    out = (
        "trust-wp: proof_assert in creusot_test::k verified ✓\n"
        "trust-wp: proof_assert in creusot_test::k FAILED ✗\n"
        "trust-wp: k error: verdict withdrawn - its own proof_assert was not proved\n"
        + wire(base=1, failed=1, errors=1, proof_assert_verified=1, proof_assert_failed=1)
    )
    assert ra.standing_assertion_credits(out) == ["creusot_test::k"]
    ok, note = ra.evaluate(case(), ra.FAILED, out, exit_code=1)
    assert not ok and "creusot_test::k (1 verified, 0 declared)" in note


def test_the_gate_and_the_driver_agree_on_the_standing_assertion_credits():
    # A withdrawal read that the driver did not make would hide a credit it still
    # counts; an assertion counted without a line this gate reads would too.
    hidden = TRAIT_WITHDRAWN_ASSERTION.replace("proof_assert_verified=0", "proof_assert_verified=1")
    ok, note = ra.evaluate(case(), ra.FAILED, hidden, exit_code=1)
    assert not ok and "the driver counts 1 proof_assert credit(s) standing and this gate reads 0" in note
    unread = ASSERTION_CREDIT.replace("proof_assert_verified=1", "proof_assert_verified=2")
    c = case(**{"also-verified-assertion": "creusot_test::k"})
    ok, note = ra.evaluate(c, ra.FAILED, unread, exit_code=1)
    assert not ok and "the driver counts 2" in note
