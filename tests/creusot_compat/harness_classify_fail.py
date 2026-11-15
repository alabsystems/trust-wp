#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Should-fail and error-category policy for the harness classifier."""

from __future__ import annotations

import re
import urllib.parse

try:
    from tests.creusot_compat.harness_classify_signals import (
        _check_source_unsupported,
        _detect_infrastructure_failure,
        _dropped_obligation_warning_count,
        _has_caught_panic_marker,
        _has_panic_exit_status,
        _has_rustc_panic,
        _has_snapshot_self_reference_rejection,
        _has_timeout_caused_errors,
        _has_verified_contracts,
        _has_verification_failures,
        _has_ay_panic_marker,
        _last_proof_assert_summary_counts,
    )
    from tests.creusot_compat.harness_classify_succeed import (
        classify_failure,
        _extract_wire_line_pairs,
        _source_has_user_contracts,
    )
except ModuleNotFoundError:
    from harness_classify_signals import (
        _check_source_unsupported,
        _detect_infrastructure_failure,
        _dropped_obligation_warning_count,
        _has_caught_panic_marker,
        _has_panic_exit_status,
        _has_rustc_panic,
        _has_snapshot_self_reference_rejection,
        _has_timeout_caused_errors,
        _has_verified_contracts,
        _has_verification_failures,
        _has_ay_panic_marker,
        _last_proof_assert_summary_counts,
    )
    from harness_classify_succeed import (
        classify_failure,
        _extract_wire_line_pairs,
        _source_has_user_contracts,
    )


def _is_should_fail_test(test_name: str) -> bool:
    """Return True if test_name belongs to the should_fail lane."""
    return test_name.startswith("tests/should_fail/")


STRICT_PASS_PREFIX = "Correctly rejected (strict):"

BACKEND_PASS_PREFIX = "Backend superseded (pass):"

# Every should_fail pass is stored as ``Correctly rejected (<credit>)`` where
# <credit> names the classifier gate that credited the rejection:
# ``validated counterexample: <def_path> <kind>``, ``termination check
# failed``, ``frontend: <diagnostic>``, ``compile: error[E0499]``, ... so
# every pass row is auditable from the stored JSON alone (the raw driver
# output is discarded for pass rows). A bare ``wire failed=N`` /
# ``proof_assert failed=M`` counter is never a credit (D-28).
REJECTION_PASS_PREFIX = "Correctly rejected"


def rejection_pass_message(credit: str | None) -> str:
    """Format the stored message for a credited should_fail rejection."""
    if credit:
        return f"{REJECTION_PASS_PREFIX} ({credit})"
    return REJECTION_PASS_PREFIX


def is_rejection_pass_message(message: object) -> bool:
    """True for any should_fail rejection pass message (credited or legacy).

    Deliberately excludes the should_succeed strict-rejection prefix
    ``Correctly rejected (strict):`` only by lane — callers in the should_fail
    lane never see it.
    """
    return isinstance(message, str) and (
        message == REJECTION_PASS_PREFIX
        or message.startswith(REJECTION_PASS_PREFIX + " (")
    )

from verification_grade import STRICT_REJECTION_REASONS as _KNOWN_STRICT_REJECTION_TESTS

_KNOWN_FALSE_ACCEPT_TESTS: dict[str, str] = {
    # Known false accepts: should_fail tests trust-wp verifies although Creusot
    # rejects them. An entry is classified "fail", never "skip" -- the ledger
    # attributes a hole, it never hides one (D-17). The dict stays while empty
    # because the exact ratchet
    # test_r4_false_accept_ledger_is_exact_and_other_residuals_are_empty
    # asserts get_residual_summary()["false_accept"] is the empty set: any
    # future false accept must be ledgered here explicitly, never silently,
    # and that ratchet must move with the entry. count_known_false_accepts and
    # reclassify_results read the dict.
}

def count_known_false_accepts() -> int:
    """Return the number of documented false-accept tests (#2690).

    False-accepts are should-fail tests where trust-wp incorrectly verifies
    code that Creusot correctly rejects.  These represent real unsoundness
    gaps (ghost-type escape, snapshot self-reference) that need to be
    fixed in the verification engine.
    """
    return len(_KNOWN_FALSE_ACCEPT_TESTS)


def get_false_accept_summary() -> dict[str, str]:
    """Return a copy of the known false-accept test dict for documentation (#2690).

    This exposes the false-accept inventory for use by reporting and
    baseline tooling without leaking the mutable original.
    """
    return dict(_KNOWN_FALSE_ACCEPT_TESTS)


def get_residual_summary() -> dict[str, dict[str, str]]:
    """Return a structured summary of all should-fail residual categories (#2686).

    Groups all non-pass tests by category with resolution status:
    - ``false_accept``: Tests where trust-wp incorrectly accepts (soundness gap)
    - ``api_divergence``: Tests where trust-wp-std API differs from creusot-std
    - ``spec_infrastructure``: Tests requiring spec-level validation trust-wp lacks
    - ``backend_superseded``: Tests where trust-wp's ay backend correctly supersedes
      Why3/Pearlite limitations (counted as pass, listed here for completeness)

    Each entry maps test path -> reason string.
    """
    result: dict[str, dict[str, str]] = {
        "false_accept": dict(_KNOWN_FALSE_ACCEPT_TESTS),
        "api_divergence": {
            k: v
            for k, v in _KNOWN_EXPECTED_DIVERGENCE_TESTS.items()
            if v.startswith("API divergence:")
        },
        "spec_infrastructure": {
            k: v
            for k, v in _KNOWN_EXPECTED_DIVERGENCE_TESTS.items()
            if v.startswith("Spec infrastructure")
        },
        "backend_superseded": dict(_KNOWN_BACKEND_SUPERSEDED_TESTS),
    }
    return result


_KNOWN_BACKEND_SUPERSEDED_TESTS: dict[str, str] = {
    # Backend-superseded tests: Creusot rejects these due to Why3/Pearlite
    # limitations that do not apply to trust-wp's ay backend. trust-wp correctly
    # handles this code, which is a feature of the MIR-based ay approach.
    # These count as "pass" in the should_fail lane because trust-wp's correct
    # handling supersedes the backend limitation. (#2686)
    #
    # An entry's justification must show that the Creusot goal is a backend
    # limitation and not a real obligation: a program whose goal is genuinely
    # unprovable (an `Add overflow` on `const { N + 1 }` for N = u32::MAX) must
    # be credited by a real verification failure (D-18), never listed here.
    # Likewise a program the trust-wp frontend refuses with Creusot's own
    # diagnostic is credited through _FRONTEND_REJECTION_MARKERS, not here:
    # this allowlist is not review-grade rejection evidence.
    # --- Pearlite restrictions not applicable to ay encoding ---
    "tests/should_fail/unsupported/char_pattern.rs": (
        "ay encodes char matches via MIR discriminant values; "
        "Why3 char match encoding limitation does not apply"
    ),
    # --- Spec-trait gating not applicable to trust-wp-std ---
    #
    # Creusot-std gates standard Rust traits (PartialEq, Iterator, collect)
    # on specification traits (DeepModel, IteratorSpec, FromIteratorSpec).
    # trust-wp-std deliberately does NOT gate standard traits on spec traits,
    # using minimal API divergence from standard Rust. These tests fail in
    # Creusot because the spec-trait prerequisite is missing, but trust-wp
    # correctly compiles and verifies the code. (#2686)
    "tests/should_fail/bug/1544_2.rs": (
        "trust-wp-std uses standard Rust #[derive(PartialEq)] without DeepModel; "
        "creusot-std spec-trait gating does not apply"
    ),
    "tests/should_fail/bug/1610-crash.rs": (
        "trust-wp-std does not gate collect() on FromIteratorSpec; "
        "creusot-std spec-trait gating does not apply"
    ),
    "tests/should_fail/bug/603.rs": (
        "trust-wp-std does not gate Iterator impl on IteratorSpec; "
        "creusot-std spec-trait gating does not apply"
    ),
}


def _check_backend_superseded(test_name: str) -> str | None:
    """Return reason if this test is backend-superseded (counts as pass), else None."""
    return _KNOWN_BACKEND_SUPERSEDED_TESTS.get(test_name)


def count_backend_superseded() -> int:
    """Return the number of backend-superseded tests (#2686).

    Backend-superseded tests are should-fail tests where Creusot rejects
    the code due to Why3/Pearlite limitations that don't apply to trust-wp's
    ay backend. trust-wp's correct handling of this code is a feature.
    """
    return len(_KNOWN_BACKEND_SUPERSEDED_TESTS)


_KNOWN_EXPECTED_DIVERGENCE_TESTS: dict[str, str] = {
    # Should-fail tests whose outcome is an expected divergence from Creusot,
    # neither a rejection nor a false accept. A reason starts with
    # "API divergence:" (trust-wp-std's API differs from creusot-std) or
    # "Spec infrastructure" (spec-level validation trust-wp lacks);
    # get_residual_summary groups on those prefixes. An entry is classified
    # "error", never "pass": a divergence is not rejection evidence. Code
    # Creusot rejects only through a Why3/Pearlite limitation belongs in
    # _KNOWN_BACKEND_SUPERSEDED_TESTS instead.
}

# Should-fail tests whose EXPECTED outcome is a plain rustc compile rejection
# (borrow-check, exhaustiveness, type, coherence, unsafety). Each entry was
# cross-checked against the Creusot reference test: the test ships a `.stderr`
# and NO `why3session.xml`, i.e. Creusot also rejects it at compile time and
# never reaches verification. Crediting these as "pass" is categorically
# sound: the program fails rustc before any MIR is produced, so trust-wp can
# never *falsely verify* it -- a false-accept is impossible by construction.
#
# Each value is a tuple of stable fragments that must ALL be present in the
# output (the rustc error code plus a distinctive message token), so a future
# trust-wp regression that rejected the same file for a *different* reason
# would not be silently credited. Tests excluded on purpose:
#   - bug/869.rs: Creusot compiles it and attempts a proof (why3session.xml
#     present) -- it is a verification-failure test, so trust-wp's E0499 there
#     is a divergence, not a matching compile rejection.
#   - bug/436_0.rs: trust-wp rejects via an incidental E0308 type mismatch, not
#     the prophetic-in-logic defect the test targets; crediting could mask a
#     latent prophetic-handling gap.
#   - builtin_with_contract.rs: credited via _FRONTEND_REJECTION_MARKERS —
#     purity_validation.rs emits the intended builtin+contract conflict
#     rejection, so no rustc-code entry is needed here.
_KNOWN_EXPECTED_COMPILE_REJECTION_EVIDENCE: dict[str, tuple[str, ...]] = {
    "tests/should_fail/bad_borrow.rs": (
        "error[E0499]",
        "cannot borrow `x` as mutable more than once",
    ),
    "tests/should_fail/bug/borrowed_ghost.rs": (
        "error[E0503]",
        "cannot use `x` because it was mutably borrowed",
    ),
    "tests/should_fail/bug/ice-final-borrows.rs": (
        "error[E0594]",
        "cannot assign to `*x`, which is behind a `&` reference",
    ),
    "tests/should_fail/bug/211.rs": (
        "error[E0004]",
        "non-exhaustive patterns",
        "E::B",
    ),
    "tests/should_fail/inexhaustive_match.rs": (
        "error[E0004]",
        "non-exhaustive patterns",
        "Option::Some(_)",
    ),
    "tests/should_fail/infinite_size.rs": (
        "error[E0072]",
        "recursive type",
        "infinite size",
    ),
    "tests/should_fail/unsafe.rs": (
        "error[E0133]",
        "call to unsafe function `evil`",
        "requires unsafe",
    ),
    "tests/should_fail/bug/snapshot_typecheck.rs": (
        "error[E0282]",
        "type annotations needed",
        "creusot_std::Snapshot",
    ),
    "tests/should_fail/bug/1519.rs": (
        "error[E0046]",
        "not all trait items implemented",
        "idemp",
    ),
    "tests/should_fail/bug/1544_1.rs": (
        "error[E0046]",
        "not all trait items implemented",
        "`Output`, `add`",
    ),
    "tests/should_fail/structural_resolve.rs": (
        "error[E0046]",
        "not all trait items implemented",
        "resolve_coherence",
    ),
    # Creusot's .stderr is exactly this rustc E0308 (the assertion is an
    # integer, not a bool); trust-wp's spec type-check vehicle reproduces it.
    "tests/should_fail/non_bool_assertion.rs": (
        "error[E0308]",
        "mismatched types",
        "proof_assert! { 1 }",
    ),
    # Creusot's .stderr: E0599, `S` does not satisfy `IndexLogic<_>` (logic
    # indexing of a type without `IndexLogic`); the spec type-check vehicle
    # reports the same unsatisfied bound.
    "tests/should_fail/diagnostics/index_unimplemented.rs": (
        "error[E0599]",
        "doesn't satisfy `S: creusot_std::logic::ops::IndexLogic<_>`",
    ),
    # Creusot's .stderr: E0277, the loop variant's type `S` does not implement
    # `WellFounded`, required by `variant_check`; the spec type-check vehicle
    # places the loop variant in the same `variant_check` call.
    "tests/should_fail/terminates/invalid_variant_type.rs": (
        "error[E0277]",
        "WellFounded` is not satisfied",
        "variant_check",
    ),
    "tests/should_fail/diagnostics/view_unimplemented.rs": (
        "error[E0277]",
        "creusot_std::View",
        "is not satisfied",
    ),
}


def _check_known_false_accept(test_name: str) -> str | None:
    """Return skip reason if this test is a known false-accept, else None."""
    return _KNOWN_FALSE_ACCEPT_TESTS.get(test_name)


def _check_expected_divergence(test_name: str) -> str | None:
    """Return skip reason if this test is expected Creusot/Why3 divergence."""
    return _KNOWN_EXPECTED_DIVERGENCE_TESTS.get(test_name)


def _classify_should_fail_known_skip(source: str, test_name: str) -> str | None:
    """Classify known-skip should_fail tests.

    Note: known false-accepts are NOT returned here — they are handled
    separately in classify_should_fail_result as "fail" (not "skip")
    because they represent real unsoundness gaps (#2690).
    """
    if (source_skip := _check_source_unsupported(source)) is not None:
        return source_skip
    return _check_expected_divergence(test_name)


_PER_FUNCTION_STATUS_RE = re.compile(
    r"^\s*trust-wp:\s+\S+.*\s+(verified|failed|unknown|error|trusted|assumed|vacuous|incomplete)\b",
    re.MULTILINE,
)


def _output_shows_function_status(output: str) -> bool:
    """Return True if output has any per-function verification status line.

    Looks for ``trust-wp: <ident> <status>`` lines (e.g.
    ``trust-wp: Foo::add unknown (timeout)``) that the driver emits for each
    contracted function it processed. Used by the vacuous-accept guard to
    distinguish silent skips (no per-function lines) from real rejections
    (per-function ``unknown``/``failed``/etc.).
    """
    for match in _PER_FUNCTION_STATUS_RE.finditer(output):
        # Skip the aggregate summary line ``0 verified, 0 failed, 0 errors``
        # which also matches the regex on the word "verified".
        line = match.group(0)
        if re.search(r"\d+\s+verified,\s+\d+\s+failed", line):
            continue
        return True
    return False


def _is_vacuous_should_fail_accept(
    output: str, source: str, require_user_contracts: bool = True
) -> bool:
    """Detect a vacuous should_fail accept.

    A vacuous accept is a should_fail test where:
    - The source contains user contracts (#[ensures], #[requires], #[invariant],
      #[variant], or proof_assert!) outside ``extern_spec!`` blocks
    - The output shows no verification activity (no per-function status lines,
      no ``verified ✓``/``failed ✗`` markers, no compile errors)
    - The wire-line telemetry (if present) shows ``verified=0 failed=0 errors=0
      base_exit_code=0`` — i.e., trust-wp exited cleanly without verifying
      anything user-claimed

    This pattern indicates trust-wp silently bypassed verification of the
    user-claimed contracts. Without this guard such a run flows through the
    logic-only ``pass`` branch of ``classify_failure`` and is flipped to
    ``fail`` (false-accept). The guard reclassifies it as ``error`` so the
    false_accept_count does not inflate when the driver silently skips
    contract obligations.

    A saved output can also lose its per-function status lines to truncation
    (log spam pushing them out of the stored message), as on
    ``tests/should_fail/unsupported/hash_map.rs``; the guard keeps the
    classifier fail-closed when the saved output lacks any signal that
    user-claimed contracts were actually verified or rejected.
    """
    # In the should_fail lane the caller passes require_user_contracts=False so
    # that a no-contract-surface source is NOT given a free pass here: a clean
    # no-activity run must still be caught as vacuous below. A no-contract
    # source that genuinely rejected is excluded by the activity/marker guards
    # that follow (it produces output signals), so legitimate rejections of
    # contract-free programs stay credited.
    if require_user_contracts and not _source_has_user_contracts(source):
        return False
    if _has_verified_contracts(output):
        return False
    if _has_verification_failures(output):
        return False
    if _output_shows_function_status(output):
        return False
    # Reject obvious compile errors / infra failures — those are handled by
    # the existing classifier branches and represent real rejections.
    if "error[E" in output or "cannot find" in output:
        return False
    if _detect_infrastructure_failure(output) is not None:
        return False
    # Exclude outputs that contain explicit trust-wp rejection markers
    # handled by the dedicated branches in ``classify_should_fail_result``
    # (logic recursion, termination check, ghost type escape, etc.). These
    # produce no per-function status line and no wire-line counters because
    # they fail during compilation/discovery, but they are valid rejections
    # rather than silent vacuous accepts.
    for marker in (
        "logic recursion check failed",
        "termination check failed",
        "ghost type escape",
        "trusted contract validation",
        "duplicate/conflicting extern_spec",
        "snapshot self-reference",
    ):
        if marker in output:
            return False
    wire = _extract_wire_line_pairs(output)
    if wire is not None:
        if (
            wire.get("verified", 0) > 0
            or wire.get("failed", 0) > 0
            or wire.get("errors", 0) > 0
            or wire.get("panics", 0) > 0
            or wire.get("proof_assert_failed", 0) > 0
            or wire.get("proof_assert_errors", 0) > 0
            or wire.get("parse_errors", 0) > 0
            or wire.get("termination_errors", 0) > 0
            or wire.get("logic_recursion_errors", 0) > 0
            or wire.get("erasure_errors", 0) > 0
            or wire.get("base_exit_code", 0) != 0
        ):
            return False
    return True


def _has_proof_assert_error_rejection(output: str) -> bool:
    if "proof_assert:" not in output or "errors" not in output:
        return False
    match = re.search(
        r"proof_assert:\s*\d+\s+verified,\s*\d+\s+failed,\s*(\d+)\s+errors",
        output,
    )
    return bool(match) and int(match.group(1)) > 0


def _has_proof_assert_failure_rejection(output: str) -> bool:
    """Detect proof_assert failures as a valid rejection signal.

    A test may have 0 function-level failures but proof_assert failures (e.g.
    final_borrows.rs where all functions are uncontracted but proof_asserts
    within function bodies fail).
    """
    if "proof_assert:" not in output:
        return False
    match = re.search(
        r"proof_assert:\s*\d+\s+verified,\s*(\d+)\s+failed,\s*\d+\s+errors",
        output,
    )
    return bool(match) and int(match.group(1)) > 0


# Frontend rejection diagnostics (#2686 follow-up). Each string is emitted only
# when the trust-wp frontend deliberately refuses to compile/encode a program
# for a specific semantic reason (raw-pointer deref, ghost/program context
# violations, logic-op gaps, law/trait-refinement mismatches, etc.). Their
# presence in a should_fail run is therefore a valid rejection, exactly like the
# already-credited markers ("ghost type escape", "termination check failed",
# "logic recursion check failed", ...). They are checked only after the
# false-accept and panic guards in classify_should_fail_result, so a clean
# accept can never be miscredited as a rejection. Plain rustc compile errors
# (E0499 etc.) are intentionally NOT listed here; those route through the
# stricter, test-name-keyed allowlist instead.
_FRONTEND_REJECTION_MARKERS: tuple[str, ...] = (
    "Laws cannot have additional generic parameters or trait constraints",
    "as specified by the trait declaration",
    "Dereference of a raw pointer is forbidden in creusot",
    "Forbidden constructor or field access of opaque type",
    # builtin_with_contract.rs: purity_validation.rs emits the same
    # builtin+contract conflict rejection Creusot does at compile time —
    # the intended defect, credited as a clean frontend reject.
    "cannot specify both `#[builtin]` and a contract on the same definition",
    "called prophetic logic function/final-state expression in non-prophetic logic context",
    "proof_assert!(false) inside a loop is an unsatisfied proof obligation",
    "can only be used for the body of",
    "Cannot divide primitive integers in logic",
    "cannot calculate the remainder of primitive integers in logic",
    "the type cannot be indexed in logic",
    "cannot move non-ghost value in ghost block",
    "ghost blocks cannot contain ",
    "cannot create a ghost variable in program context",
    "cannot dereference a ghost value in program context",
    # generic_deref_ghost.rs / generic_deref_snap.rs: the program-context ghost
    # validator refuses a call whose bound runs a ghost's `Deref` or a logic
    # type's operation at run time (D-193, `program_context`), before the
    # ghost type escape check sees the function. Creusot's `Ghost::deref`
    # requires `false` there, so its verification fails on the same call.
    "where its run-time body is not the logical operation the verifier reads",
    "cannot read which impl this call's bound",
    "in ghost block requires #[variant",
    "Cannot make a less-visible logic function transparent",
    "This trait method overrides a sealed implementation",
    "may only be called in the entry main function",
    "permission identity cannot be validated for this ghost permission",
    "used the `#[trusted]` attribute",
    "failed #[erasure] check for ",
    "#[erasure] target must have a body",
    "Pattern matching literals on Int are unsupported by Pearlite",
    # unsupported/hash_map.rs: the driver refuses the HashMap/BTreeMap Entry API
    # (entry/or_insert/or_default/and_modify) up front because those ops have no
    # functional contract in trust-wp-std (havoc-only extern specs). Creusot
    # likewise flags them as "calling external function ... with no contract will
    # yield an impossible precondition" (unsupported/hash_map.stderr), so the
    # obligation is never dischargeable. A frontend refusal is the correct
    # should_fail outcome (the program is never verified → false-accept
    # impossible). The distinctive phrase below is emitted only by
    # purity_validation's UNSUPPORTED_MAP_ENTRY_API_MESSAGE.
    "the HashMap/BTreeMap Entry API",
    # Creusot frontend refusals (callbacks/creusot_frontend_checks.rs and
    # purity_validation.rs). Each phrase is emitted only by the named check,
    # each of which stops compilation before any VC exists.
    # unsupported/macros.rs: Pearlite refuses non-pearlite macros in logic.
    "macros other than `pearlite!`, `proof_assert!` or `seq!` are unsupported in Pearlite code",
    # terminates/invalid_variant_type.rs: variant type lacks WellFounded (E0277).
    "the variant type does not implement `WellFounded`",
    # lints/contractless_external_function.rs: the denied creusot lint.
    "with no contract will yield an impossible precondition",
    # unsound_dyn.rs: `dyn Trait` outside the logically dyn-compatible traits.
    "forbidden dyn type: dyn ",
    # bug/436_0.rs: prophetic logic call inside a snapshot! capture.
    "in logic context (snapshot! is not a prophetic context)",
    # Non-prophetic logic body calling a free #[logic(prophetic)] function
    # (purity_validation::validate_logic_prophetic_calls).
    "in logic context (from non-prophetic logic function",
)

# Two-token frontend rejections: both fragments must be present so the generic
# leading phrase ("called logic function") cannot match unrelated log lines.
_FRONTEND_REJECTION_MARKER_PAIRS: tuple[tuple[str, str], ...] = (
    ("called non-ghost function", "in ghost context"),
    ("called logic function", "in program context"),
)


def _frontend_rejection_marker(output: str) -> str | None:
    """Return the frontend rejection diagnostic present in output, else None."""
    for marker in _FRONTEND_REJECTION_MARKERS:
        if marker in output:
            return marker.strip()
    for a, b in _FRONTEND_REJECTION_MARKER_PAIRS:
        if a in output and b in output:
            return f"{a} ... {b}"
    return None


def _has_frontend_rejection_diagnostic(output: str) -> bool:
    """Return True when output carries a trust-wp frontend rejection diagnostic."""
    return _frontend_rejection_marker(output) is not None


# Any per-obligation ``FAILED \u2717`` verdict line. Used only to DETECT an
# unvalidated failure signal (which is ``unknown``), never to credit one.
_DISPROOF_LINE_RE = re.compile(r"trust-wp:.*\bfailed\s+\u2717", re.IGNORECASE)

# A per-obligation verdict line, split into (proof_assert prefix, name). The
# driver prints ``trust-wp: <def_path> FAILED \u2717[ (kind)]`` for function
# contracts / loops / variants (callbacks/reporting.rs, loop_verify/reporting.rs,
# recursive_verify.rs, loop_contract/obligation.rs),
# ``trust-wp: <def_path> trait refinement FAILED \u2717`` for trait refinement
# (trait_refinement/report.rs) and ``trust-wp: proof_assert in <def_path>
# FAILED \u2717`` for proof_asserts.
_FAILED_VERDICT_LINE_RE = re.compile(
    r"^\s*trust-wp:\s+(proof_assert in\s+)?(\S.*?)(?:\s+trait refinement)?"
    r"\s+FAILED\s+\u2717",
    re.MULTILINE,
)

_DIAGNOSTIC_LINE_RE = re.compile(r"^TRUST_WP_DIAGNOSTIC:v1\s+(.*)$", re.MULTILINE)


def _diagnostic_records(output: str) -> list[dict[str, str]]:
    """Parse every ``TRUST_WP_DIAGNOSTIC:v1 key=value ...`` line in output."""
    records = []
    for match in _DIAGNOSTIC_LINE_RE.finditer(output):
        record: dict[str, str] = {}
        for token in match.group(1).split():
            key, sep, value = token.partition("=")
            if sep:
                record[key] = value
        records.append(record)
    return records


def _diagnostic_is_validated_refutation(record: dict[str, str]) -> bool:
    """A diagnostic whose failure carries a VALIDATED refutation.

    ``status=failed`` alone is not enough: the driver also labels solver-limited
    Unknown results promoted to Failed (verify/pipeline.rs), axiom-light base
    SAT (``ay_result=trust-wp-structural-provenance``), plain SAT whose model was
    never validated (``ay_result=sat model_validated=false``) and syntactic
    shortcuts with no solver call (``ay_result=none model_validated=unknown``)
    as ``status=failed reason=counterexample``. Only ``ay_result=sat`` with
    ``model_validated=true`` (or the forward-compatible explicit
    ``refutation=validated`` field) is a checked counterexample.
    """
    if record.get("status") != "failed":
        return False
    if record.get("refutation") == "validated":
        return True
    return record.get("ay_result") == "sat" and record.get("model_validated") == "true"


def _def_path_matches_verdict_name(def_path: str, name: str) -> bool:
    """True when a diagnostic def_path names the obligation of a verdict line.

    def_path is percent-encoded on the wire; obligation-qualified paths extend
    the function path with ``::<obligation>`` (e.g.
    ``f::variant_decrease[1]``, ``<T as Tr>::m::trait precondition implies
    impl precondition``).
    """
    decoded = urllib.parse.unquote(def_path)
    return decoded == name or decoded.startswith(name + "::")


def _validated_disproof(
    output: str,
    wire: dict[str, int] | None,
    pa_counts: tuple[int, int, int] | None,
) -> str | None:
    """Credit label for a validated, counted refutation in output, else None.

    Requires a ``TRUST_WP_DIAGNOSTIC`` record that is a validated refutation
    (see ``_diagnostic_is_validated_refutation``) AND matches a failure the
    driver counted: a ``proof_assert`` record needs a
    ``proof_assert in <def_path> FAILED \u2717`` line plus a non-zero
    proof_assert failed count (summary line or wire ``proof_assert_failed``);
    any other kind needs a ``<def_path> FAILED \u2717`` line plus wire
    ``failed>0``. A ``FAILED \u2717`` line or failed counter with no such
    record is NOT a refutation.
    """
    wire_failed = wire.get("failed", 0) if wire is not None else 0
    pa_failed = max(
        pa_counts[1] if pa_counts is not None else 0,
        wire.get("proof_assert_failed", 0) if wire is not None else 0,
    )
    verdicts = [
        (bool(m.group(1)), m.group(2).strip())
        for m in _FAILED_VERDICT_LINE_RE.finditer(output)
    ]
    for record in _diagnostic_records(output):
        if not _diagnostic_is_validated_refutation(record):
            continue
        def_path = record.get("def_path", "")
        kind = record.get("kind", "")
        if not def_path or not kind:
            continue
        is_pa = kind == "proof_assert"
        if (pa_failed if is_pa else wire_failed) <= 0:
            continue
        if any(
            verdict_is_pa == is_pa
            and _def_path_matches_verdict_name(def_path, name)
            for verdict_is_pa, name in verdicts
        ):
            return (
                "validated counterexample: "
                f"{urllib.parse.unquote(def_path)} {kind}"
            )
    return None


def _has_unvalidated_failure_signal(
    output: str,
    wire: dict[str, int] | None,
    pa_counts: tuple[int, int, int] | None,
) -> bool:
    """True when the driver reported a failure the gate could not validate."""
    if wire is not None and (
        wire.get("failed", 0) > 0 or wire.get("proof_assert_failed", 0) > 0
    ):
        return True
    if pa_counts is not None and pa_counts[1] > 0:
        return True
    return bool(_DISPROOF_LINE_RE.search(output))


def _disproof_evidence(output: str) -> str | None:
    """Return deterministic ghost-validation rejection evidence, else None.

    A should_fail rejection reached through the generic should_succeed
    classifier (``raw_status == "fail"``) is credited ONLY on the ghost-block
    validation rejection, a frontend refusal. ``FAILED \u2717`` verdict lines
    are NOT evidence here: the driver prints them for unvalidated results too,
    so a solver refutation is credited only by ``_validated_disproof``.
    Solver ``unknown``/timeout verdicts and ``K errors`` counters are never
    disproofs (D-28).
    """
    if "ghost validation error" in output.lower():
        return "ghost validation error(s)"
    return None


def _has_allowlisted_compile_rejection_evidence(
    output: str, test_name: str
) -> bool:
    """Return True when a broad compile error matches a named should-fail case.

    Generic Rust/Cargo compile markers such as ``error[E...]`` and
    ``could not compile`` are too broad to prove that a should-fail test was
    rejected for its expected reason.  Tests that intentionally rely on a
    plain compile diagnostic must name stable diagnostic evidence here instead
    of passing through the broad compile fallback.
    """
    return _allowlisted_compile_rejection_evidence(output, test_name) is not None


def _allowlisted_compile_rejection_evidence(
    output: str, test_name: str
) -> str | None:
    """Return the matched compile-rejection evidence (its rustc code), else None."""
    expected_evidence = _KNOWN_EXPECTED_COMPILE_REJECTION_EVIDENCE.get(test_name)
    # An empty/absent evidence tuple must NEVER vacuously credit a rejection:
    # ``all(... for ... in ())`` is True, which would silently pass any compile
    # error for that test. Require at least one fragment, all of which must hit.
    if not expected_evidence:
        return None
    if all(fragment in output for fragment in expected_evidence):
        return expected_evidence[0]
    return None


def classify_should_fail_result(
    success: bool,
    output: str,
    source: str,
    test_name: str = "",
    exit_code: int | None = None,
) -> tuple[str, str | None]:
    """Classify a should_fail test result (status, skip_reason).

    Thin wrapper over :func:`classify_should_fail_result_with_credit` that
    drops the crediting-gate label; the runner uses the credited form so the
    stored pass message records WHY the rejection was credited.
    """
    status, skip_reason, _credit = classify_should_fail_result_with_credit(
        success, output, source, test_name, exit_code=exit_code
    )
    return status, skip_reason


def _wire_base_exit_code(wire: dict[str, int] | None) -> int | None:
    if wire is None:
        return None
    value = wire.get("base_exit_code")
    return value if isinstance(value, int) else None


def classify_should_fail_result_with_credit(
    success: bool,
    output: str,
    source: str,
    test_name: str = "",
    exit_code: int | None = None,
) -> tuple[str, str | None, str | None]:
    """Classify a should_fail test result as ``(status, skip_reason, credit)``.

    ``credit`` is non-None exactly when ``status == "pass"`` and names the
    gate that credited the rejection (see ``rejection_pass_message``).

    Gate order (D-28: no ``FAILED`` without a validated counterexample model):
    every pass requires POSITIVE rejection evidence — a VALIDATED
    counterexample (a ``TRUST_WP_DIAGNOSTIC`` record with ``ay_result=sat
    model_validated=true`` matching a counted failure; see
    ``_validated_disproof``), a deterministic frontend refusal (termination /
    logic-recursion / parse / extern_spec / trusted-contract / ghost-escape /
    snapshot-self-reference / named frontend diagnostic), or an allowlisted
    rustc compile rejection. Solver timeouts and ``unknown`` verdicts are never
    rejections (``error``/``unknown``); a ``wire failed>0`` /
    ``proof_assert failed>0`` / ``FAILED \u2717`` signal with no validated
    refutation record is ``unknown`` (the driver labels solver-limited Unknown,
    structural-provenance base SAT, unvalidated SAT and no-solver shortcuts
    ``failed``); a ``proof_assert: ... K errors`` count
    with zero failed proof_asserts and zero wire ``failed`` is ``unknown``, not
    pass; a driver exit 101 without a compile diagnostic, or any
    signal-terminated process, is an ``error`` whatever it printed first.
    """
    # Backend-superseded tests (#2686): Creusot rejects these due to Why3/Pearlite
    # limitations that don't apply to trust-wp's ay backend. trust-wp correctly
    # handling this code is a feature, not a failure. Count as "pass".
    # The reason is carried in the message (via BACKEND_PASS_PREFIX) by the
    # runner, not as a skip_reason, since the test is not being skipped.
    if (backend_reason := _check_backend_superseded(test_name)) is not None:
        if _detect_infrastructure_failure(output) is not None:
            return "error", None, None
        if _has_timeout_caused_errors(output):
            return "error", None, None
        if _has_rustc_panic(output):
            return "error", None, None
        if _has_panic_exit_status(output, exit_code):
            return "error", None, None
        if _has_ay_panic_marker(output):
            return "error", None, None
        if _has_caught_panic_marker(output):
            return "error", None, None
        if not success and _classify_error_category(
            output, exit_code, include_driver_verdict=False
        ) == "compile":
            return "error", None, None
        return "pass", None, f"backend superseded: {backend_reason}"

    if _classify_should_fail_known_skip(source, test_name) is not None:
        return "error", None, None

    # Known false-accepts (#2690): should_fail tests where trust-wp incorrectly
    # verifies code that Creusot correctly rejects. These represent real
    # unsoundness gaps (ghost-type escape, snapshot self-reference) and must
    # be classified as "fail" (not "skip") so the false-accept count is
    # accurate and visible in reporting.
    if (false_accept_reason := _check_known_false_accept(test_name)) is not None:
        return "fail", false_accept_reason, None

    if success:
        # Vacuous-accept guard (see _is_vacuous_should_fail_accept):
        # When trust-wp reports success but the output shows no verification
        # activity at all (no per-function status, no wire-line counters,
        # no compile error) and the source has user contracts, trust-wp
        # silently bypassed the user-claimed obligations. Reclassify as
        # "error" so the false_accept_count is not inflated by silent skips.
        # This guard only runs in the success path because non-success paths
        # below already detect genuine rejection signals (logic recursion,
        # trusted contract validation, ghost type escape, parse errors, etc.)
        # before reaching the vacuous-accept check; placing the guard here
        # avoids intercepting those rejection patterns.
        if _is_vacuous_should_fail_accept(output, source, require_user_contracts=False):
            return "error", "vacuous accept: no verification activity", None
        return "fail", None, None

    # Guard: detect false-accepts even when the success flag is wrong (#2690).
    # During reclassification the success flag is inferred from stored output;
    # if the exit-code extraction misses the wire format, success may be False
    # while the output clearly shows clean verification.  Treat that as a
    # false-accept (fail) rather than a correct rejection (pass).
    if _has_verified_contracts(output) and not _has_verification_failures(output):
        return "fail", None, None

    if _has_rustc_panic(output):
        return "error", None, None

    # ay solver panics (#2690): any phase-qualified ay panic variant
    # (check_sat, verification, loop, proof_assert, etc.) is an internal
    # solver error and must classify as "error" in should_fail, not "pass".
    # Without this, phase variants like ``ay solver panic during check_sat``
    # fall through to later reason gates and get silently counted as valid
    # rejections.
    if _has_ay_panic_marker(output):
        return "error", None, None

    # Caught per-function panics (#1975, #2690): the driver caught a panic
    # during encoding/solving for one or more functions.  These are internal
    # errors, not genuine rejections — classify as "error" in the should_fail
    # lane too.  Without this, caught panics fall through to the delegate
    # classifier which returns ("error", None), and the reason-gate below
    # would silently convert them to "pass" (incorrectly counted as a
    # valid rejection).  The helper matches all phase-qualified variants
    # (``panicked during proof_assert:``, ``panicked during loop verification:``,
    # ``panicked during check_sat:``, etc.), not just the verification phase.
    if _has_caught_panic_marker(output):
        return "error", None, None

    wire = _extract_wire_line_pairs(output)

    # Driver crash exits. Cargo reports EVERY failed compilation as exit
    # 101, so a 101 accompanied by a compile diagnostic (``error[E..]``,
    # ``aborting due to N previous errors``) is the ordinary transport of a
    # frontend refusal and falls through to the evidence gates below. A 101 —
    # from the process, the wire line's ``base_exit_code``, or echoed as
    # ``exit status: 101`` — WITHOUT a compile diagnostic, or with ``panicked``
    # text, is a suppressed driver crash and is ALWAYS ``error``: a frontend
    # marker substring seen before the crash is not rejection evidence (the
    # driver's span_err markers, e.g. lints/trusted_code ``used the
    # `#[trusted]` attribute``, print rustc's abort line and so never land
    # here). A process terminated by a signal is a crash regardless of what it
    # printed first.
    if _ABNORMAL_TERMINATION_RE.search(output):
        return "error", None, None
    exit_101 = (
        exit_code == 101
        or _wire_base_exit_code(wire) == 101
        or bool(re.search(r"exit status:\s*101\b", output))
    )
    if exit_101 and ("panicked" in output.lower() or not _has_compile_diagnostic(output)):
        return "error", None, None

    # Validated refutations are correct should_fail rejections (D-28). The
    # wire ``failed`` / ``proof_assert_failed`` counters, the ``proof_assert: N
    # verified, M failed`` summary and the ``FAILED \u2717`` verdict line are
    # NOT evidence on their own: the driver
    # increments / prints them for results with no validated model — a
    # solver-limited Unknown turned into Failed (trust-wp-ay
    # verify/pipeline.rs), axiom-light base SAT
    # (``ay_result=trust-wp-structural-provenance``), plain SAT whose model was
    # never validated (``ay_result=sat model_validated=false``) and syntactic
    # shortcuts with no solver call (``ay_result=none``). A refutation is
    # credited only when a ``TRUST_WP_DIAGNOSTIC`` record with ``ay_result=sat
    # model_validated=true`` names a counted failure. This is consulted before
    # the coarse should_succeed heuristics (``_has_lra_unsupported_failures``,
    # #2674) so a mixed output with a validated refutation (e.g.
    # terminates/incorrect_variant.rs) stays credited. The false-accept, panic
    # and infra guards have all run above.
    pa_counts = _last_proof_assert_summary_counts(output)
    if (credit := _validated_disproof(output, wire, pa_counts)) is not None:
        return "pass", None, credit

    # Deterministic frontend refusals (termination / logic recursion / parse /
    # extern_spec / trusted-contract / ghost escape / snapshot self-reference /
    # named frontend diagnostics). See ``_frontend_rejection_credit``.
    if (credit := _frontend_rejection_credit(output, wire)) is not None:
        return "pass", None, credit

    # Solver timeouts are never rejections. Every positive rejection channel
    # has been consulted above; a run whose only remaining signal is
    # ``unknown (timeout)`` / ``hard timeout expired`` is an inconclusive
    # verifier, recorded as an error in the timeout category.
    if _has_timeout_caused_errors(output):
        return "error", None, None

    # Validated-refutation rule (D-28): a failed counter / ``FAILED \u2717``
    # line with no validated refutation record (see above) and no deterministic
    # frontend refusal is an inconclusive verifier, not a rejection. An
    # allowlisted rustc compile rejection is still deterministic evidence.
    if _has_unvalidated_failure_signal(output, wire, pa_counts):
        if (
            _classify_error_category(
                output, exit_code, include_driver_verdict=False
            ) == "compile"
            and (
                evidence := _allowlisted_compile_rejection_evidence(output, test_name)
            )
            is not None
        ):
            return "pass", None, f"compile: {evidence}"
        return "unknown", None, None

    # ``proof_assert: N verified, 0 failed, K errors``
    # with no wire ``failed`` is NOT a rejection. The driver counts solver
    # Unknown (incl. timeout/demoted), Assumed and encoding errors in that K
    # (reporting.rs report_proof_assert_verification_result), none of which
    # refutes the program. Record it as ``unknown`` so the false_accept_count
    # stays honest and the row is visible as inconclusive.
    if _has_proof_assert_error_rejection(output):
        return "unknown", None, None

    # A non-zero process status is the expected transport for this lane, so use
    # the should-succeed classifier only to interpret its semantic diagnostics.
    # Crash/panic/infrastructure exits were screened above; forwarding the
    # process code here would trigger the ordinary lane's fail-closed success
    # guard and erase genuine should-fail rejection evidence.
    raw_status, raw_reason = classify_failure(output, source, exit_code=None)
    if raw_status == "skip":
        return "error", None, None
    if raw_status == "unknown":
        return "unknown", None, None
    if raw_status == "error":
        error_category = _classify_error_category(
            output, exit_code, include_driver_verdict=False
        )
        if error_category == "compile":
            if (
                evidence := _allowlisted_compile_rejection_evidence(output, test_name)
            ) is not None:
                return "pass", None, f"compile: {evidence}"
            return "error", raw_reason, None
        return "error", raw_reason, None
    if raw_status == "pass":
        # Vacuous-accept guard (see _is_vacuous_should_fail_accept):
        # ``classify_failure`` returned "pass" because the source looks
        # logic-only or otherwise has no real verification surface in the
        # output. When the source actually has user contracts and the output
        # shows zero verification activity (no per-function status, no
        # rejection markers, no wire-line counters), trust-wp silently
        # bypassed the user-claimed obligations. Reclassify as "error" so
        # the false_accept_count is not inflated by this silent-skip pattern.
        # The earlier branches above already catch real rejection markers
        # (logic recursion, ghost type escape, parse errors, etc.), so
        # this guard only intercepts genuine vacuous accepts.
        if _is_vacuous_should_fail_accept(output, source, require_user_contracts=False):
            return "error", "vacuous accept: no verification activity", None
        return "fail", None, None
    if raw_status == "fail":
        # The generic classifier's "fail" is credited only on the deterministic
        # ghost validation rejection. Validated
        # solver refutations were credited above and unvalidated ``FAILED
        # \u2717`` / failed counters were recorded as ``unknown`` above; its
        # other "fail" sources — a bare ``proof_assert_errors>0`` wire counter,
        # or the fall-through default — carry no refutation and are ``unknown``.
        if (evidence := _disproof_evidence(output)) is not None:
            return "pass", None, evidence
        return "unknown", None, None

    return "error", None, None


# Signal / abnormal process termination as reported by cargo or the shell.
_ABNORMAL_TERMINATION_RE = re.compile(
    r"\(signal:\s*\d+|\bSIG(?:SEGV|ABRT|BUS|ILL|FPE|TRAP)\b|has overflowed its stack"
)


def _has_compile_diagnostic(output: str) -> bool:
    """True when output carries a rustc/cargo compile diagnostic.

    Mirrors the compile-diagnostic carve-out in ``_has_panic_exit_status``:
    cargo's exit 101 accompanied by one of these is a compile failure, not a
    suppressed panic.
    """
    lower = output.lower()
    return (
        "error[e" in lower
        or "cannot find" in lower
        or "failed to parse" in lower
        or "due to previous error" in lower
        or bool(re.search(r"due to \d+ previous error", lower))
    )


def _frontend_rejection_credit(
    output: str, wire: dict[str, int] | None
) -> str | None:
    """Credit label for a deterministic frontend refusal present in output.

    Each channel is a driver diagnostic emitted only when trust-wp refuses the
    program for a named semantic reason before/independently of the solver:
    ``termination check failed`` (callbacks), ``logic recursion check failed``,
    ``parse_errors>0`` (wire), duplicate/conflicting extern_spec (duplicate_specs),
    trusted contract validation (bug/1762), ghost type escape
    (generic_deref_ghost), snapshot self-reference (bug/436_2), and the named
    ``_FRONTEND_REJECTION_MARKERS``. Returns None when none is present. No
    solver verdict (failed / unknown / timeout / errors counter) is consulted.
    """
    if "termination check failed" in output:
        return _counted_credit("termination check failed", wire, "termination_errors")
    if "logic recursion check failed" in output:
        return _counted_credit(
            "logic recursion check failed", wire, "logic_recursion_errors"
        )
    parse_match = re.search(r"\bparse_errors=([1-9]\d*)\b", output)
    if parse_match is not None:
        return f"parse_errors={parse_match.group(1)}"
    if "duplicate/conflicting extern_spec" in output:
        return "duplicate/conflicting extern_spec"
    if "trusted contract validation" in output:
        return "trusted contract validation"
    if "ghost type escape" in output:
        return "ghost type escape"
    if _has_snapshot_self_reference_rejection(output):
        return "snapshot self-reference"
    marker = _frontend_rejection_marker(output)
    if marker is not None:
        return f"frontend: {marker}"
    return None


def _counted_credit(label: str, wire: dict[str, int] | None, key: str) -> str:
    """``label`` plus the wire counter for ``key`` when the wire line has it."""
    if wire is not None and wire.get(key, 0) > 0:
        return f"{label} ({key}={wire[key]})"
    return label


def classify_error_category(
    output: str,
    exit_code: int | None = None,
) -> str:
    """Sub-classify an error result into a specific failure category."""
    return _classify_error_category(output, exit_code, include_driver_verdict=True)


def _classify_error_category(
    output: str,
    exit_code: int | None,
    *,
    include_driver_verdict: bool,
) -> str:
    # Rejection-credit callers retain their existing evidence decisions. The
    # richer driver categories describe diagnostics only, never grant credit.
    infra_reason = _detect_infrastructure_failure(output)
    if infra_reason is not None:
        if infra_reason == "timeout":
            return "timeout"
        return "infrastructure"

    # Solver-level timeouts (#2690): when verify functions report
    # "unknown (timeout)" or "hard timeout expired", the root cause is
    # solver/hard timeout, not a generic unknown error.  Check before
    # panic/compile checks because timeout takes priority when the solver
    # hits its time limit.
    if _has_timeout_caused_errors(output):
        return "timeout"

    # ay solver panic takes priority over caught_panic and driver_panic
    # regardless of phase variant (#2690): check_sat / loop / proof_assert /
    # per-function ``ay solver panicked`` emissions, not only ``during
    # verification``.
    if _has_ay_panic_marker(output):
        return "ay_panic"

    # Caught per-function panics take priority over driver_panic (#2690), and
    # every phase variant counts: ``panicked during proof_assert:`` and
    # ``panicked during loop verification:`` are caught panics too, not
    # driver panics.
    if _has_caught_panic_marker(output):
        return "caught_panic"

    if _has_rustc_panic(output):
        return "driver_panic"

    if _has_panic_exit_status(output, exit_code):
        return "driver_panic"

    if _dropped_obligation_warning_count(output) > 0:
        return "obligations_dropped"

    if "error[E" in output or "cannot find" in output:
        return "compile"

    output_lower = output.lower()

    # Ghost block validation errors (#2690): when trust-wp emits "ghost validation
    # error(s)", the test has compile-time ghost constraint violations (e.g.,
    # ghost block uses non-ghost variable, ghost context mismatch). These are
    # compile-time semantic errors, not runtime panics or driver crashes.
    if "ghost validation error" in output_lower:
        return "ghost_validation"

    if (
        "trust-wp: error:" in output_lower
        or (include_driver_verdict and (
            re.search(r"(?m)^error: trust-wp:", output_lower)
            or re.search(r"(?m)^error: ghost type escape:", output_lower)
        ))
    ):
        return "encoding"

    # Cargo prints the same compilation-failed trailer when our driver rejects
    # a VC. A complete driver result identifies that outcome independently of
    # the wrapper exit; it is not evidence that rustc could not compile Rust.
    # This changes diagnostic categories only, never status or proof credit.
    wire = _extract_wire_line_pairs(output) if include_driver_verdict else None
    if wire is not None:
        if any(wire.get(key, 0) for key in (
            "parse_errors", "termination_errors", "logic_recursion_errors",
            "erasure_errors",
        )):
            return "encoding"
        if wire.get("failed", 0) or wire.get("proof_assert_failed", 0):
            return "verification"
        if wire.get("base_exit_code") in (1, 2, 3):
            return "unknown"

    if "could not compile" in output:
        return "compile"

    return "unknown"


def classify_unknown_category(output: str) -> str:
    """Sub-classify an unknown result into a specific unknown sub-category (#2690).

    When the harness classifies a test as "unknown", the per-function status
    lines carry diagnostic detail that can be surfaced as a sub-category.
    This allows reporting to distinguish genuine solver incompleteness from
    encoding limitations (demoted), quantifier gaps, and timeout-adjacent
    resource exhaustion.

    Categories (checked in priority order):
    - ``demoted`` — encoding approximations demoted the result
    - ``quantifier_unhandled`` — quantifier pattern not handled by ay
    - ``quantifier_cegqi`` — CEGQI incomplete for the quantifier structure
    - ``incomplete`` — solver returned incomplete (generic)
    - ``solver_unknown`` — fallback when no specific sub-category matches
    """
    has_demoted = False
    has_quantifier_unhandled = False
    has_quantifier_cegqi = False
    has_incomplete = False

    for line in output.split("\n"):
        lower = line.lower().strip()
        if "trust-wp:" not in lower:
            continue
        if "unknown (" not in lower:
            continue
        # Skip proof_assert lines — they are secondary signals
        if "proof_assert" in lower:
            continue
        if "demoted" in lower:
            has_demoted = True
        elif "quantifier-unhandled" in lower:
            has_quantifier_unhandled = True
        elif "quantifier-cegqi" in lower or "cegqi" in lower:
            has_quantifier_cegqi = True
        elif "incomplete" in lower:
            has_incomplete = True

    # Return the most informative category.  Demoted takes priority because
    # it indicates a known encoding limitation (actionable by fixing the
    # unsoundness approximation).
    if has_demoted:
        return "demoted"
    if has_quantifier_unhandled:
        return "quantifier_unhandled"
    if has_quantifier_cegqi:
        return "quantifier_cegqi"
    if has_incomplete:
        return "incomplete"
    return "solver_unknown"


__all__ = [
    "BACKEND_PASS_PREFIX",
    "REJECTION_PASS_PREFIX",
    "STRICT_PASS_PREFIX",
    "classify_should_fail_result_with_credit",
    "is_rejection_pass_message",
    "rejection_pass_message",
    "_KNOWN_BACKEND_SUPERSEDED_TESTS",
    "_KNOWN_STRICT_REJECTION_TESTS",
    "_is_should_fail_test",
    "classify_error_category",
    "classify_should_fail_result",
    "classify_unknown_category",
    "count_backend_superseded",
    "count_known_false_accepts",
    "get_false_accept_summary",
    "get_residual_summary",
]
