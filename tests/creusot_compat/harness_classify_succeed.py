#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Should-succeed and parse-only policy for the harness classifier."""

from __future__ import annotations

import re

try:
    from tests.creusot_compat.harness_classify_signals import (
        _check_output_unsupported,
        _check_source_unsupported,
        _detect_infrastructure_failure,
        _dropped_obligation_warning_count,
        _has_caught_panic_marker,
        _has_lra_unsupported_failures,
        _has_panic_exit_status,
        _has_rustc_panic,
        _has_timeout_caused_errors,
        _has_verified_contracts,
        _last_contract_block_output,
        _last_contract_count,
        _last_proof_assert_summary_counts,
        _last_verification_summary_counts,
        _wire_line_shows_pa_only_failure,
    )
    from tests.creusot_compat.harness_model import parse_wire_line, WIRE_PREFIX
except ModuleNotFoundError:
    from harness_classify_signals import (
        _check_output_unsupported,
        _check_source_unsupported,
        _detect_infrastructure_failure,
        _dropped_obligation_warning_count,
        _has_caught_panic_marker,
        _has_lra_unsupported_failures,
        _has_panic_exit_status,
        _has_rustc_panic,
        _has_timeout_caused_errors,
        _has_verified_contracts,
        _last_contract_block_output,
        _last_contract_count,
        _last_proof_assert_summary_counts,
        _last_verification_summary_counts,
        _wire_line_shows_pa_only_failure,
    )
    from harness_model import parse_wire_line, WIRE_PREFIX


NO_REPLAY_PASS_PREFIX = "Parse-only (NO_REPLAY):"
NO_REPLAY_STRICT_ERROR_MESSAGE = (
    "NO_REPLAY marker is not accepted by the strict compatibility gate"
)
_EXPLICIT_FALSE_REQUIRES_RE = re.compile(r"#\s*\[\s*requires\s*\(\s*false\s*\)\s*\]")
_USER_CONTRACT_ATTR_RE = re.compile(r"#\s*\[\s*(requires|ensures|invariant|variant)\s*\(")


def _is_no_replay_source(source: str) -> bool:
    """Return True when source contains the ``// NO_REPLAY`` marker."""
    return bool(re.search(r"//\s*NO_REPLAY", source))


# Creusot NO_REPLAY tests whose contract is GENUINELY UNPROVABLE (Creusot itself
# only translates them — its NO_REPLAY mode never runs the prover — and no sound
# verifier can prove them). For these, and ONLY these, a "creusot replacement"
# matches Creusot's translate-only pass. Everything else marked NO_REPLAY must be
# VERIFIED WITH PROOF by trust-wp (strictly superior to Creusot, which skips it).
#   - bug/653: ensures(result@ == n@*(n@+1)/2) on `fn omg(n)->usize { n }` is FALSE
#     for n>=2 (a translation-regression test for Creusot issue #653).
#   - traits/04: ensures(result == false) on `user<T: A>(a,b) -> bool` whose body is
#     `a.func1(b) && b.func2(a) && a.func3(b)`. Trait `A`'s methods have NO contracts
#     (return unconstrained bool), so `result` can be true => `result == false` is FALSE.
#     ay correctly returns a validated SAT counterexample; no sound verifier can prove it.
#   - spec_tests: ensures(T::A == T::B) [distinct enum variants] and
#     ensures(S(0u32,true) == S(1u32,false)) [0u32 != 1u32] are both FALSE by inspection.
#   - closures/01_basic: a `// NO_REPLAY` test with NO user contracts at all (just
#     `(|| y)()`, `|a,b| a+b`, `move || *a += 1`, `move || x = new_ref()`). There is
#     nothing to prove, so a translate-only pass cannot false-accept anything (zero
#     obligations); trust-wp translates it with a fully clean frontend (0 errors/
#     panics/parse/erasure/termination/logic-recursion) and emits base_exit_code=2
#     only because it has zero verifiable obligations — exactly the NO_REPLAY parse-
#     only shape Creusot accepts. The _no_replay_translation_clean guard still
#     requires the clean frontend, so a real closure-translation bug would NOT pass.
# All are `// NO_REPLAY` in the Creusot reference (the why3 prover never runs on them
# — why3tests/tests/why3.rs:220 is parse/translate-only), so translate-only is the
# faithful Creusot match and a sound disposition (false-contract or no-contract).
_NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST: tuple[str, ...] = (
    "bug/653",
    "traits/04",
    "spec_tests",
    "closures/01_basic",
)


def _is_translate_only_allowed(test_name: str | None) -> bool:
    """True iff this NO_REPLAY test is on the documented genuinely-unprovable
    allowlist, for which translate-only is the faithful Creusot match."""
    if not test_name:
        return False
    return any(marker in test_name for marker in _NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST)


# Should-succeed tests whose proof_assert "counterexample" is SPURIOUS BY
# CONSTRUCTION: every proof_assert (and in-body contract obligation) in the
# file is a TRUE statement under RustHorn/Creusot prophecy semantics, so no
# genuine refuting model exists — any reported counterexample is an artifact
# of a documented encoding gap, not a refutation. For these tests (and ONLY
# these), a wire line showing clean function-level results with
# proof_assert-only failures classifies as "unknown" (inconclusive verifier,
# same bucket as the rusthorn prophecy-gap siblings inc_max_3 /
# inc_some_2_list / …) instead of "fail".
#
# This mirrors the LRA spurious-SAT guard (#2674), which also demotes
# counterexamples the solver could not have validated against real semantics
# to "unknown". It deliberately does NOT restore the pre-hardening #2700
# "pass" credit: baselines 2026-04-18/19 passed these files while the driver
# emitted 4 proof_assert counterexamples (verified=1, proof_assert_failed=4)
# — a false parity credit the wire-line hardening was built to remove.
# Creusot itself proves these proof_asserts via why3 replay, so an
# unconditional "pass" would overstate parity; a "fail" would misreport a
# spurious refutation as a genuine one.
#
#   - closures/09_fnonce_resolve: semantic ground truth — x=1,y=1; the
#     FnOnce closure moves Box(&mut x) / Box(Box(&mut y)), adds 1 to exactly
#     one pointee, and drops both loans at body end, so the prophecy finals
#     satisfy ^bx + ^by == 3 in both branches and resolve gives the caller
#     x@+y@ == 3. Every proof_assert is true. The caller-side proof_assert
#     VC however (a) checks the closure's *requires* `(**bx)@ == 1` against
#     post-call resolve facts (`bx@ == ^x`), (b) instantiates the closure
#     ensures over capture expressions `old(^x)` that flatten to fresh,
#     untethered atoms (`old_x_final_current_final`), and (c) carries
#     `let mut x = 1` only as `call_4_current == 1` with no tie to `bx` —
#     so ay finds a model of the (incomplete) VC with x=0,y=0 and reports a
#     "validated" counterexample that corresponds to no execution. Tracked
#     as the "closure resolve counterexample" cluster
#     (internal campaign-session log, 2026-07-04); the driver-side fix needs
#     pre-/post-call state staging plus capture-loan prophecy linkage
#     (#2318) and is false-accept-sensitive.
#
# EXIT CRITERION: remove an entry when the caller-side call staging fix
# lands and the file's proof_asserts verify (the wire line then shows
# proof_assert_failed=0 / proof_assert_errors=0 and the normal pass path
# applies; this table is consulted only when the PA-only-failure signature
# fires, so a fixed test cannot be masked by a stale entry).
_KNOWN_SPURIOUS_PA_COUNTEREXAMPLE_TESTS: dict[str, str] = {
    "tests/should_succeed/closures/09_fnonce_resolve.rs": (
        "spurious proof_assert counterexample: all asserts are true under "
        "prophecy semantics (x@+y@==3 follows from the closure ensures and "
        "resolve); the caller-side VC is temporally collapsed and leaves the "
        "instantiated closure ensures untethered from the prophecy finals, "
        "so the model refutes the encoding, not the program (closure resolve "
        "counterexample cluster, 2026-07-04)"
    ),
}


def _check_spurious_pa_counterexample(test_name: str | None) -> str | None:
    """Return the documented reason iff this test's proof_assert-only failure
    is a known spurious counterexample (see table above), else None."""
    if not test_name:
        return None
    return _KNOWN_SPURIOUS_PA_COUNTEREXAMPLE_TESTS.get(test_name)


def classify_no_replay_result(
    output: str,
    exit_code: int | None = None,
    test_name: str | None = None,
) -> tuple[str, str | None]:
    """Classify a NO_REPLAY test result — STRICTLY SUPERIOR to Creusot.

    Creusot's NO_REPLAY mode translates the program and PARSES the output but never
    runs the prover. A trust-wp that merely matched that would throw away its real
    advantage. So the primary gate REQUIRES trust-wp to actually VERIFY the test
    (clean verification telemetry) — asserting more than Creusot. Only a small,
    documented allowlist of GENUINELY-UNPROVABLE Creusot contracts (bug/653) is
    allowed to pass translate-only, which is the faithful Creusot match for those
    (and only those) since Creusot does not prove them either. Anything else marked
    NO_REPLAY that trust-wp fails to verify is a real gap (or regression) and is an
    error, not a silent pass.
    """
    if _has_rustc_panic(output):
        return "error", None
    # Faithful-minimum path: the documented genuinely-unprovable allowlist
    # (bug/653, traits/04, spec_tests) is checked BEFORE the _has_panic_exit_status
    # heuristic. These tests EXPECT a non-zero exit: Creusot's NO_REPLAY mode skips
    # the prover, but trust-wp runs it, (correctly) refutes the false contract, and
    # cargo wraps that failed step as exit 101 with no compile diagnostic — which
    # _has_panic_exit_status would otherwise misread as a suppressed panic and error.
    # _no_replay_translation_clean is the authoritative guard: it requires a clean
    # TRUST_WP_RESULT wire line with panics==0 (and zero parse/termination/
    # logic-recursion/erasure errors), so a genuine suppressed panic — which either
    # bumps the panics counter or omits the wire line entirely — still falls through
    # to the error paths below. (Without this ordering the allowlist never fired in
    # the direct harness; bug/653 only passed under the heavier review gate.)
    if _is_translate_only_allowed(test_name) and _no_replay_translation_clean(output):
        return "pass", None
    if _has_panic_exit_status(output, exit_code):
        return "error", None
    if (infra := _detect_infrastructure_failure(output)) is not None:
        return "error", infra
    # Strictly-superior path: trust-wp VERIFIED it (more than Creusot's parse-only).
    if _no_replay_verified_clean(output, exit_code):
        return "pass", None
    return "error", None


def _no_replay_verified_clean(output: str, exit_code: int | None) -> bool:
    """True when trust-wp VERIFIED the NO_REPLAY program cleanly — zero failures,
    errors, panics, proof_assert issues, frontend errors, and a zero exit code.

    This is the STRICTLY-SUPERIOR bar: Creusot's NO_REPLAY mode never runs the
    prover (why3tests/tests/why3.rs:220 — it only parses the translated output), so
    a trust-wp that actually PROVES the contract asserts strictly more than Creusot.
    Every NO_REPLAY test except the documented genuinely-unprovable allowlist must
    clear this bar; a NO_REPLAY test that trust-wp fails to verify is a real gap or
    regression, never a silent pass.
    """
    if exit_code not in (None, 0):
        return False
    for line in reversed(output.split("\n")):
        stripped = line.strip()
        if not stripped.startswith(WIRE_PREFIX):
            continue
        telemetry = parse_wire_line(stripped)
        if telemetry is None:
            return False
        return (
            telemetry.failed == 0
            and telemetry.errors == 0
            and telemetry.panics == 0
            and telemetry.proof_assert_failed == 0
            and telemetry.proof_assert_errors == 0
            and telemetry.parse_errors == 0
            and telemetry.termination_errors == 0
            and telemetry.logic_recursion_errors == 0
            and telemetry.erasure_errors == 0
            and telemetry.base_exit_code == 0
        )
    return False


def _no_replay_translation_clean(output: str) -> bool:
    """True when trust-wp TRANSLATED the program cleanly (frontend telemetry clean),
    IGNORING the proof verdict — matching Creusot's NO_REPLAY parse-only check
    (why3.rs:220). Used ONLY for the documented genuinely-unprovable allowlist
    (bug/653), where Creusot itself does not prove the contract so translate-only is
    the faithful match. Requires parse/termination/logic-recursion/erasure errors
    and panics to be zero; deliberately ignores failed/errors/proof_assert_* /
    base_exit_code (the prover step Creusot skips).
    """
    for line in reversed(output.split("\n")):
        stripped = line.strip()
        if not stripped.startswith(WIRE_PREFIX):
            continue
        telemetry = parse_wire_line(stripped)
        if telemetry is None:
            return False
        return (
            telemetry.panics == 0
            and telemetry.parse_errors == 0
            and telemetry.termination_errors == 0
            and telemetry.logic_recursion_errors == 0
            and telemetry.erasure_errors == 0
        )
    return False


def _classify_failure_marker_status(
    output: str, output_lower: str
) -> tuple[str, str | None] | None:
    # Distinguish function-level failures from proof_assert-only failures (#2700).
    # When all function contracts verify but proof_asserts fail, the compat test
    # should not be classified as "fail" — the function-level verification succeeded
    # and the proof_assert failures reflect missing encoding support, not wrong behavior.
    has_function_failed = any(
        "failed" in line.lower()
        and "proof_assert" not in line.lower()
        and "(logic postcondition)" not in line.lower()
        and not re.search(r"trust-wp:\s*\d+\s+verified,", line, re.IGNORECASE)
        for line in output.split("\n")
        if "failed" in line.lower() and "trust-wp:" in line.lower()
    )
    has_proof_assert_failed = any(
        "proof_assert" in line.lower() and "failed" in line.lower()
        for line in output.split("\n")
        if "trust-wp:" in line.lower()
    )
    has_counterexample = "counterexample" in output_lower
    has_failed_marker = has_function_failed or (has_counterexample and not has_proof_assert_failed)
    has_unknown_marker = any(
        "unknown (" in line and "proof_assert" not in line
        for line in output_lower.split("\n")
        if "trust-wp:" in line
    )
    if has_failed_marker:
        # LRA unsupported guard (#2674): when ay's LRA theory reports
        # "unsupported" atoms, the DPLL(T) solver may produce SAT results
        # (with counterexamples) that violate theory constraints. These
        # counterexamples are spurious — the solver couldn't handle the
        # formula. Classify as "unknown" so the should-succeed lane records
        # an inconclusive verifier result instead of a Rust compile error.
        if _has_lra_unsupported_failures(output):
            return "unknown", None
        return "fail", None
    if has_unknown_marker:
        # Timeout-caused unknowns (#2690): when ALL per-function unknown
        # reasons are timeout-related, reclassify as "error" so the error
        # category sub-classifier labels them "timeout".  This prevents
        # solver timeout results from inflating the "unknown" count.
        if _has_timeout_caused_errors(output):
            return "error", None
        return "unknown", None

    if "error[E" in output or "cannot find" in output:
        return "error", None

    if "could not compile" in output:
        if _last_verification_summary_counts(output) is None:
            return "error", None
        return None

    if (
        "unexpectedly panicked" in output
        and "ay solver panic during verification" not in output
        and not _has_caught_panic_marker(output)
    ):
        return "error", None

    return None


def _is_logic_only_source(source: str) -> bool:
    return bool(re.search(r"#\s*\[\s*logic", source)) or "proof_assert!" in source


def _source_has_user_contracts(source: str) -> bool:
    """Check whether the source file contains user-written contract annotations.

    Contract annotations inside ``extern_spec!`` blocks are excluded because
    extern specs declare specifications for external items and do not produce
    verification obligations in trust-wp. Only annotations in regular function
    definitions are counted. (#2675)
    """
    # Strip extern_spec! blocks before searching. These declare specs for
    # external items and don't produce trust-wp verification obligations.
    stripped = _strip_extern_spec_blocks(source)
    if re.search(r"#\s*\[\s*(requires|ensures|invariant|variant)\s*\(", stripped):
        return True
    if "proof_assert!" in stripped:
        return True
    return False


def _strip_extern_spec_blocks(source: str) -> str:
    """Remove ``extern_spec! { ... }`` macro invocations from source text.

    Uses brace-depth tracking to handle nested braces inside the macro body.
    Returns the source with extern_spec blocks replaced by whitespace (to
    preserve line numbering for error messages).
    """
    result = []
    i = 0
    pattern = "extern_spec!"
    while i < len(source):
        idx = source.find(pattern, i)
        if idx == -1:
            result.append(source[i:])
            break
        result.append(source[i:idx])
        # Find the opening brace
        brace_start = source.find("{", idx + len(pattern))
        if brace_start == -1:
            # Malformed extern_spec! — keep the rest as-is
            result.append(source[idx:])
            break
        # Track brace depth to find matching close
        depth = 1
        j = brace_start + 1
        while j < len(source) and depth > 0:
            if source[j] == "{":
                depth += 1
            elif source[j] == "}":
                depth -= 1
            j += 1
        # Replace the extern_spec! block with spaces (preserve line count)
        block = source[idx:j]
        replacement = "".join("\n" if c == "\n" else " " for c in block)
        result.append(replacement)
        i = j
    return "".join(result)


def _all_contracts_axiomatized(output: str, contract_count: int) -> bool:
    """Check whether all found functions are logic functions."""
    if contract_count == 0:
        return False
    block_output = _last_contract_block_output(output)
    logic_definition_count = block_output.count(
        "is a logic function (definition registered)"
    ) + block_output.count("is a logic function (axiomatized, not verified)")
    verified_count = block_output.count(
        "is a logic function (postcondition will be verified)"
    )
    return (logic_definition_count + verified_count) == contract_count


def _all_contracts_non_verifiable(output: str, contract_count: int) -> bool:
    """Check whether all found functions are accounted for by non-verifiable skips."""
    if contract_count == 0:
        return False
    block_output = _last_contract_block_output(output)
    trusted_count = block_output.count("trusted (skipped)")
    logic_definition_count = block_output.count(
        "is a logic function (definition registered)"
    ) + block_output.count("is a logic function (axiomatized, not verified)")
    assumed_count = block_output.count("assumed (axiom-only function")
    logic_verified_count = block_output.count(
        "is a logic function (postcondition will be verified)"
    )
    bodyless_count = block_output.count(
        "is a trait method declaration (spec only, not verified)"
    )
    accounted = (
        trusted_count
        + logic_definition_count
        + assumed_count
        + logic_verified_count
        + bodyless_count
    )
    return accounted >= contract_count


def _classify_no_contract_case(
    output_lower: str,
    source: str,
    last_contract_count: int,
    exit_code: int | None,
    gap_only_exit: bool = False,
) -> tuple[str, str | None] | None:
    logic_only = _is_logic_only_source(source)
    if "trust-wp: error:" in output_lower:
        return "error", None
    if last_contract_count == 0:
        if logic_only:
            if exit_code not in (None, 0) and not gap_only_exit:
                # Logic/proof-only source text is not proof evidence. A
                # failed cargo-trust-wp process must not be upgraded to a
                # compatibility pass merely because there were no ordinary
                # function contracts to count.
                return "error", None
            if "proof_assert!" in source:
                # A proof_assert-only crate is a pass only when the dedicated
                # proof-assert summary below reports at least one proved
                # assertion. Defer to that classifier instead of treating
                # the source marker itself as success evidence.
                return None
            return "pass", None
        if _source_has_user_contracts(source):
            return None
        if exit_code not in (None, 0) and not gap_only_exit:
            # A clean-looking summary cannot override the process result. In
            # particular, the substring also matches "0 verified", which used
            # to turn arbitrary failed no-contract and extern-spec-only runs
            # into compatibility passes. (A deliberate soundness-gap exit on a
            # failure-free wire line — e.g. `#[trusted]` derived impls — is
            # the one exception; see _is_soundness_gap_only_exit.)
            return "error", None
        return "pass", None
    return None


def _classify_no_verified_contracts(
    output: str,
    source: str,
    last_contract_count: int,
    exit_code: int | None = None,
    gap_only_exit: bool = False,
) -> tuple[str, str | None]:
    if exit_code not in (None, 0) and not gap_only_exit:
        # Non-verifying markers (trusted/assumed/logic-only/bodyless) explain
        # why no proof was attempted; they do not override a failed verifier
        # process. In particular, cargo-trust-wp deliberately exits non-zero
        # for soundness-gap telemetry — but only a wire-authenticated
        # soundness-gap-only exit (_is_soundness_gap_only_exit) may fall
        # through to the content classifiers; accepting any other nonzero
        # exit here would make the review lane fail open.
        return "error", None
    if _all_contracts_axiomatized(output, last_contract_count):
        return "pass", None
    if _all_contracts_non_verifiable(output, last_contract_count):
        return "pass", None
    if not _source_has_user_contracts(source):
        return "pass", None
    # When trust-wp exits cleanly (code 0) and found no verifiable contracts
    # (last_contract_count == 0), the source's contract annotations are in
    # non-verifiable contexts (e.g., extern_spec! blocks, #[trusted] items).
    # This is correct behavior — classify as "pass", not "skip". (#2675)
    if (
        exit_code == 0
        and last_contract_count == 0
        and "proof_assert!" not in _strip_extern_spec_blocks(source)
    ):
        return "pass", None

    # Wire-line fallback (#2701): when _last_contract_count returns 0 but the
    # TRUST_WP_RESULT wire line shows that all discovered functions were accounted
    # for by trusted/assumed/vacuous dispositions (with no failures/errors), the
    # test should pass. This handles tests where the "found N functions with
    # contracts" discovery line is absent but trust-wp still processed functions.
    wire_pairs = _extract_wire_line_pairs(output)
    if wire_pairs is not None:
        w_verified = wire_pairs.get("verified", 0)
        w_failed = wire_pairs.get("failed", 0)
        w_errors = wire_pairs.get("errors", 0)
        w_trusted = wire_pairs.get("trusted", 0)
        w_assumed = wire_pairs.get("assumed", 0)
        w_panics = wire_pairs.get("panics", 0)
        w_exit = wire_pairs.get("base_exit_code", -1)
        # All functions trusted/assumed with no failures
        if w_failed == 0 and w_errors == 0 and w_panics == 0:
            if w_trusted > 0 or w_assumed > 0:
                return "pass", None
            # Clean exit with nothing to verify (e.g., extern_spec only). A
            # source containing proof_assert! still needs its dedicated proof
            # summary; an all-zero wire record cannot prove the assertion ran.
            if (
                w_exit == 0
                and w_verified == 0
                and not _source_has_user_contracts(source)
            ):
                return "pass", None

    # Vacuous proof fallback: preserve compatibility status when the summary
    # shows vacuous proofs with no failures/errors. Strict true-100/tier
    # accounting still treats vacuity as incomplete proof evidence.
    output_lower = output.lower()
    has_vacuous_result = (
        wire_pairs is not None and wire_pairs.get("vacuous", 0) > 0
    ) or "vacuous proof" in output_lower or bool(
        re.search(r"\b[1-9]\d*\s+vacuous\b", output_lower)
    )
    if has_vacuous_result:
        counts = _last_verification_summary_counts(output)
        if counts is not None:
            _, failed, errors = counts
            if failed == 0 and errors == 0:
                return "pass", None
    return "error", None


def _is_soundness_gap_only_exit(output: str, exit_code: int | None) -> bool:
    """True when a nonzero process exit is fully explained by soundness-gap
    telemetry (trusted/assumed/skipped/vacuous/axiom-dependent/evidence-gap
    dispositions) on an otherwise failure-free wire line.

    The driver deliberately exits 2 whenever the crate is not a CLEAN proof
    (``has_soundness_gap``), even when every attempted obligation verified.
    Creusot corpus sources routinely contain ``#[trusted]`` items (e.g. a
    trusted ``main`` or ``swap`` helper), so a blanket "nonzero exit is an
    error" rule would hard-error the entire lane. The compatibility lane
    instead records such runs through the ordinary content classifiers —
    a compat-lenient pass at most, with the strict/tier accounting still
    treating the gap as incomplete proof evidence (``strict_pass`` stays 0).

    Fail-closed: the carve-out requires the authoritative TRUST_WP_RESULT
    wire line to be present, to claim ``base_exit_code=2`` itself, to record
    at least one VERIFIED obligation (zero-proof runs — trusted-only or
    extern-spec-only crates — never qualify and stay hard errors), to show
    zero failure-shaped counters, and to attribute the gap to at least one
    recognized disposition. Any other nonzero exit remains a hard error.
    """
    if exit_code != 2:
        return False
    wire = _extract_wire_line_pairs(output)
    if wire is None:
        return False
    if wire.get("base_exit_code", -1) != 2:
        return False
    if wire.get("verified", 0) <= 0:
        # Function-contract wire counter shows no proofs. A proof_assert-only
        # crate can still carry real machine-checked evidence: the driver
        # counts proof_assert verifications only in the dedicated summary
        # line, never in the wire `verified` counter, so e.g.
        # bug/negative_int_pats (7/7 proof_asserts verified + 1 trusted item,
        # exit 2) hard-errored despite a failure-free wire line. Accept that
        # shape only when the summary shows at least one verified
        # proof_assert and zero failed/errored ones — the wire line's own
        # proof_assert_failed/proof_assert_errors counters are additionally
        # checked below, so a failure-bearing run still never qualifies.
        pa_counts = _last_proof_assert_summary_counts(output)
        if pa_counts is None:
            return False
        pa_verified, pa_failed, pa_errors = pa_counts
        if pa_verified <= 0 or pa_failed > 0 or pa_errors > 0:
            return False
    failure_keys = (
        "failed",
        "errors",
        "panics",
        "proof_assert_failed",
        "proof_assert_errors",
        "parse_errors",
        "termination_errors",
        "logic_recursion_errors",
        "erasure_errors",
    )
    if any(wire.get(key, 0) for key in failure_keys):
        return False
    gap_keys = (
        "trusted",
        "assumed",
        "skipped",
        "vacuous",
        "verified_with_axiom_deps",
        "unverified_axioms",
        "evidence_gaps",
    )
    return any(wire.get(key, 0) for key in gap_keys)


def _extract_wire_line_pairs(output: str) -> dict[str, int] | None:
    """Extract key=value pairs from the last complete TRUST_WP_RESULT wire line."""
    for line in reversed(output.split("\n")):
        stripped = line.strip()
        if not stripped.startswith(WIRE_PREFIX):
            continue
        telemetry = parse_wire_line(stripped)
        if telemetry is None:
            return None
        return telemetry.to_dict()
    return None


def _failed_or_error_count(counts: tuple[int, int, int] | None) -> int:
    if counts is None:
        return 0
    _, failed_count, error_count = counts
    return failed_count + error_count


def _classify_by_proof_assert(output: str) -> tuple[str, str | None] | None:
    """Classify based on proof_assert results when function-level is empty."""
    pa_counts = _last_proof_assert_summary_counts(output)
    if pa_counts is None:
        return None
    pa_verified, pa_failed, pa_errors = pa_counts
    if pa_verified > 0 and pa_failed == 0 and pa_errors == 0:
        return "pass", None
    if pa_failed > 0 or pa_errors > 0:
        return "fail", None
    return None


def _classify_explicit_false_precondition_vacuity(
    output: str,
    output_lower: str,
    source: str,
    last_contract_count: int,
) -> tuple[str, str | None] | None:
    """Treat a single explicit impossible precondition as a compat pass.

    This is intentionally narrow: one contracted function, exactly one
    `#[requires(false)]`, and no proof_assert surface. That keeps the compat
    harness aligned with Creusot's accepted single-function vacuity cases
    without weakening the generic vacuity guard for multi-contract or
    proof-assert scenarios.
    """
    if (
        "vacuous proof: base assertions are unsat without the negated postcondition"
        not in output_lower
    ):
        return None
    if len(_EXPLICIT_FALSE_REQUIRES_RE.findall(source)) != 1:
        return None
    if len(_USER_CONTRACT_ATTR_RE.findall(source)) != 1:
        return None
    if "proof_assert!" in source:
        return None
    counts = _last_verification_summary_counts(output)
    if counts is None:
        return None
    verified_count, failed_count, error_count = counts
    if verified_count == 0 and failed_count == 0 and error_count > 0:
        return "pass", None
    return None


def classify_failure(
    output: str,
    source: str,
    exit_code: int | None = None,
    test_name: str | None = None,
) -> tuple[str, str | None]:
    """Classify a should-succeed test result into status and reason."""
    output_lower = output.lower()

    if _has_rustc_panic(output):
        return "error", None

    if _is_no_replay_source(source):
        return classify_no_replay_result(
            output, exit_code=exit_code, test_name=test_name
        )

    # The ordinary should-succeed lane is only successful when the command
    # itself succeeds.  Textual summaries and wire telemetry are emitted before
    # cargo/wrapper teardown can fail, so neither can authenticate a later
    # non-zero process result.  NO_REPLAY has its own translate-only classifier
    # above and is deliberately kept outside this rule.  The single documented
    # exception is the driver's deliberate soundness-gap exit (2) on a
    # failure-free wire line — see _is_soundness_gap_only_exit — which falls
    # through to the content classifiers so ``#[trusted]``-bearing corpus
    # sources keep their compat-lenient (never strict) classification.
    gap_only_exit = _is_soundness_gap_only_exit(output, exit_code)
    if exit_code not in (None, 0) and not gap_only_exit:
        return "error", None

    if _check_source_unsupported(source) is not None:
        return "error", None

    if _check_output_unsupported(output_lower) is not None:
        return "error", None

    # Caught per-function panics (#1975, #2690, #2687): the driver caught a
    # panic during encoding/solving for one or more functions. The
    # ``panicked during <phase>:`` marker identifies non-ay trust-wp-side
    # panics (encoding bugs) — the ay solver emits its own ``ay solver
    # panic during <phase>`` markers (matched via ``_has_ay_panic_marker``)
    # that are handled by ``classify_error_category`` with the ay_panic
    # category. Both signal an "error" status at this layer — the
    # sub-category distinction happens later. The helper matches all
    # phase-qualified variants (``panicked during proof_assert:``,
    # ``panicked during loop verification:``, ``panicked during check_sat:``,
    # etc.), not just the verification phase.
    if _has_caught_panic_marker(output):
        return "error", None

    if "ghost validation error(s)" in output_lower:
        return "fail", None

    has_panic_exit = _has_panic_exit_status(output, exit_code)
    if has_panic_exit:
        summary = _last_verification_summary_counts(output)
        if summary is not None:
            verified, failed, errors = summary
            if verified > 0 or failed > 0 or errors > 0:
                pass
            elif _last_proof_assert_summary_counts(output) is not None:
                pass
            else:
                return "error", None
        else:
            return "error", None

    if (infra_failure := _detect_infrastructure_failure(output)) is not None:
        return "error", infra_failure

    # Wire-line proof_assert hardening: when valid TRUST_WP_RESULT telemetry shows
    # clean function-level results but proof_assert failures/errors, fail closed
    # instead of reporting a plain pass. The wire line is the authoritative
    # aggregate for multi-crate output where last-summary parsing is ambiguous.
    #
    # Documented exception: tests on the spurious-PA-counterexample table
    # (all asserts semantically true — no genuine refuting model exists)
    # classify as "unknown" with the table's reason instead of "fail",
    # matching the LRA spurious-SAT precedent (#2674). They never classify
    # as a plain pass while the PA-only-failure signature persists.
    if _wire_line_shows_pa_only_failure(output):
        if (
            spurious_reason := _check_spurious_pa_counterexample(test_name)
        ) is not None:
            return "unknown", spurious_reason
        return "fail", None

    if (marker_status := _classify_failure_marker_status(output, output_lower)) is not None:
        return marker_status

    last_contract_count = _last_contract_count(output)
    if (
        explicit_false_status := _classify_explicit_false_precondition_vacuity(
            output, output_lower, source, last_contract_count
        )
    ) is not None:
        return explicit_false_status

    if (
        contract_status := _classify_no_contract_case(
            output_lower, source, last_contract_count, exit_code, gap_only_exit
        )
    ) is not None:
        return contract_status

    dropped_warnings = _dropped_obligation_warning_count(output)
    if dropped_warnings > 0:
        return "error", f"obligations dropped ({dropped_warnings})"

    counts = _last_verification_summary_counts(output)
    if _failed_or_error_count(counts) == 0 and not _has_verified_contracts(output):
        if (pa_status := _classify_by_proof_assert(output)) is not None:
            return pa_status
        return _classify_no_verified_contracts(
            output, source, last_contract_count, exit_code, gap_only_exit
        )

    if counts is not None:
        verified_count, failed_count, error_count = counts
        if failed_count == 0 and error_count == 0 and verified_count > 0:
            return "pass", None
        if failed_count == 0 and error_count == 0 and verified_count == 0:
            if (pa_status := _classify_by_proof_assert(output)) is not None:
                return pa_status
        if failed_count == 0 and error_count > 0:
            # Solver-level "Unknown" results that are caused by timeouts should
            # be classified as "error" (timeout category) rather than "unknown"
            # (#2690).  This prevents timeout-caused solver unknowns from being
            # counted in the "unknown" bucket, which inflates the genuine
            # unknown count.
            if _has_timeout_caused_errors(output):
                return "error", None
            return "unknown", None

    return "fail", None


__all__ = [
    "NO_REPLAY_PASS_PREFIX",
    "NO_REPLAY_STRICT_ERROR_MESSAGE",
    "_KNOWN_SPURIOUS_PA_COUNTEREXAMPLE_TESTS",
    "_all_contracts_axiomatized",
    "_all_contracts_non_verifiable",
    "_check_spurious_pa_counterexample",
    "_is_no_replay_source",
    "classify_failure",
    "classify_no_replay_result",
]
