#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Should-fail and error-category policy for the harness classifier."""

from __future__ import annotations

import re

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

_KNOWN_STRICT_REJECTION_TESTS: dict[str, str] = {
    "tests/should_succeed/termination/warn_unneeded_variant.rs": (
        "trust-wp correctly detects non-decreasing variant (x passed unchanged); "
        "Creusot only warns"
    ),
}

_KNOWN_FALSE_ACCEPT_TESTS: dict[str, str] = {
    # R4-b ledger (2026-07-22): the five status=fail rows of
    # baseline-20260706.json, explicitly xfail-ledgered per the R4 gate
    # ("each of the 5 known false-accepts is fixed or explicitly
    # xfail-ledgered and barred from Certified"). Entries stay classified
    # "fail" — the ledger attributes them, it never hides them. Fix order
    # per the 2026-07-22 R4 recon: int-shift-full first (a missing
    # obligation in one encoding), then the termination trio + impl_arg
    # (soundness-critical callgraph work in the driver).
    #
    # EMPTY as of 2026-07-24: all five rows are fixed (see the dated NOTEs
    # below). The dict and its exact-ratchet test remain so any future
    # false-accept must be ledgered here explicitly, never silently.
    #
    # NOTE: bug/int-shift-full.rs removed from false-accepts (2026-07-24).
    # The shift lowering now emits the missing shift-amount-in-range side
    # obligation: the driver wraps machine-int `<<`/`>>` amounts in the
    # `__trust_wp_shift_amount_in_range_{bits}` marker, the ay encoder
    # collects the path-guarded `0 <= amount < bits` proof obligation
    # through the same channel as the `divisor != 0` obligations, the MIR
    # shift-overflow assert is no longer assumed as a fact (it is proved),
    # and the pipeline proves body side obligations even for an empty
    # postcondition set. `1u8 >> 8` now fails verification with a
    # counterexample and is classified as a valid rejection by the
    # should_fail classifier.
    #
    # NOTE: recursive_types/impl_arg.rs, terminates/trait_where.rs, and
    # terminates/trait_where_supertrait.rs removed from false-accepts
    # (2026-07-24). The driver now ports Creusot's "Illegal recursive trait"
    # check (validate/recursive_types.rs `add_trait`): a logic method of a
    # trait whose bound graph (supertraits + method where-clause/impl-Trait-
    # argument bounds + associated-type bounds) cycles back to itself is
    # rejected at the definition — the typing context lets the definition
    # dispatch back into itself (`x.f(x)` on `x: impl Q` inside `Q::f`,
    # `self.f(self)` under `where Self: Tr<Self>`, or through a supertrait
    # `P: Q` bound), an edge no body walk can see. The rejection is emitted
    # as "logic recursion check failed" (exit 2), which the should_fail
    # classifier credits as a valid rejection.
    #
    # NOTE: terminates/trait_impl_where.rs removed from false-accepts
    # (2026-07-24). The termination callgraph now threads self-named
    # self-dispatch: `self.f()` inside the logic fn named `f` provably
    # dispatches back into the caller (via the enclosing impl or its
    # where-clause bound), but short-name resolution dropped the edge
    # whenever the trait declaration and impls shared the name — exactly the
    # recursive case. The walker now records the self-edge with real
    # actual-args/path-conditions, and the identity self-call is rejected as
    # "unconditional self-recursion without #[variant(...)]" ("logic
    # recursion check failed", exit 2), a valid should_fail rejection.
    # NOTE: generic_deref_ghost.rs and generic_deref_snap.rs removed from
    # false-accepts (2026-04-18). Ghost type escape is now detected by the
    # check_ghost_type_escape validation pass in the driver, which rejects
    # non-logic, non-ghost functions with Ghost/Snapshot parameters that
    # return non-ghost types. The "ghost type escape" error output is
    # classified as a valid rejection by the should_fail classifier. (#2686)
    #
    # NOTE: bug/436_2.rs removed from false-accepts (2026-04-23).
    # The driver now rejects recursive Snapshot<&mut T> types with
    # "snapshot self-reference: type Bad contains Snapshot<&mut T>", which is
    # classified as a valid should-fail rejection below.
    # NOTE: bug/1966.rs removed from false-accepts (2026-04-13).
    # Unconditional self-recursion is now detected and rejected by the
    # logic recursion checker. The "logic recursion check failed" output
    # is classified as a valid rejection by the should_fail classifier.
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
    # --- Backend divergence: Why3 limitations not applicable to ay ---
    "tests/should_fail/ignore_overflow.rs": (
        "ay backend handles overflow via integer semantics; "
        "Why3 requires explicit overflow proof obligations"
    ),
    # --- Pearlite restrictions not applicable to ay encoding ---
    # NOTE: unsupported/1827/test{1,2}.rs were REMOVED from this allowlist
    # (2026-06-02). trust-wp's driver frontend genuinely rejects them with
    # "Pattern matching literals on Int are unsupported by Pearlite" (the same
    # message Creusot emits, same path as the already-credited sibling
    # test3/test4), so they are now credited as a real strict rejection via
    # _FRONTEND_REJECTION_MARKERS rather than this non-review-grade allowlist.
    "tests/should_fail/unsupported/char_pattern.rs": (
        "ay encodes char matches via MIR discriminant values; "
        "Why3 char match encoding limitation does not apply"
    ),
    "tests/should_fail/unsupported/macros.rs": (
        "ay extracts logic bodies from MIR, not surface syntax; "
        "Pearlite restriction on macros in logic fn bodies does not apply"
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
    # NOTE: bug/1544_2.rs, bug/1610-crash.rs, bug/603.rs moved to
    # _KNOWN_BACKEND_SUPERSEDED_TESTS (2026-04-18, #2686). trust-wp's
    # deliberate non-gating of standard Rust traits on spec traits is a
    # design improvement over Creusot's approach, not a divergence.
    # They now count as "pass" instead of "skip".
    #
    # --- Spec infrastructure divergence ---
    #
    # NOTE: bug/1762.rs removed from known-divergence (2026-04-24).
    # The trusted contract validation pass now rejects #[trusted] functions
    # whose contracts reference #[check(ghost)] functions; the should_fail
    # classifier treats that diagnostic as a valid rejection below.
    # NOTE: duplicate_specs.rs removed from known-divergence (2026-04-14).
    # trust-wp now detects duplicate/conflicting extern_spec declarations and
    # rejects them with exit code 2. (#2686)
    # NOTE: test3.rs and test4.rs removed from known-divergence (2026-04-14).
    # Both tests are correctly rejected by trust-wp (compile error from or-pattern
    # and nested option/tuple match with Int literals). Even though the rejection
    # reason differs from Creusot's Pearlite restriction, a correct rejection
    # should count as pass, not skip. (#2675)
    # --- Terminates checking ---
    # All 6 terminates/ divergence entries removed (2026-04-14, #2665):
    # - terminates/complicated_traits_recursion.rs: Fixed by 9926f5e76
    # - terminates/default_function_non_logic.rs: Fixed by 9926f5e76
    # - terminates/loops_in_terminates.rs: Now correctly rejects (termination_errors)
    # - terminates/mutual_recursion_trait.rs: Now correctly rejects (termination_errors)
    # - terminates/terminates-calls-nonterminate.rs: Now correctly rejects
    #   (validate_terminates_call_targets, #2665)
    # - terminates/trait_def_and_impl_disagree.rs: Now correctly rejects
    #   (terminates marker consistency checking, #2665)
    # NOTE: ghost/non_ghost.rs removed from known-divergence (2026-04-14).
    # trust-wp now correctly rejects this test -- the terminates infrastructure
    # detects the ghost block calling a terminates-checked function. (#2675)
    # NOTE: traits/17_impl_refinement.rs removed from known-divergence (2026-04-14).
    # trust-wp's logic-fn trait refinement checking correctly rejects the
    # weakened #[requires] on the impl. (#2675)
    # NOTE: Backend/Pearlite divergence tests moved to _KNOWN_BACKEND_SUPERSEDED_TESTS
    # (2026-04-15, #2686). These are not true divergences but backend superiority:
    # trust-wp's ay/MIR approach correctly handles code that Why3/Pearlite cannot.
    # They now count as "pass" instead of "skip".
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
#   - builtin_with_contract.rs: NOW CREDITED via _FRONTEND_REJECTION_MARKERS —
#     purity_validation.rs emits the intended builtin+contract conflict
#     rejection (the earlier "unsupported attribute" note was stale). (#route-100 r1)
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
    """Detect a vacuous should_fail accept (Phase 12A, hash_map regression).

    A vacuous accept is a should_fail test where:
    - The source contains user contracts (#[ensures], #[requires], #[invariant],
      #[variant], or proof_assert!) outside ``extern_spec!`` blocks
    - The output shows no verification activity (no per-function status lines,
      no ``verified ✓``/``failed ✗`` markers, no compile errors)
    - The wire-line telemetry (if present) shows ``verified=0 failed=0 errors=0
      base_exit_code=0`` — i.e., trust-wp exited cleanly without verifying
      anything user-claimed

    This pattern indicates trust-wp silently bypassed verification of the
    user-claimed contracts. In the should_fail lane, that historically flowed
    through the logic-only ``pass`` branch of ``classify_failure`` and was
    flipped to ``fail`` (false-accept). The vacuous-accept guard reclassifies
    this as ``error`` so the false_accept_count does not inflate when the
    driver silently skips contract obligations.

    Origin: ``tests/should_fail/unsupported/hash_map.rs`` regressed from
    ``status=error`` to ``status=fail`` after Wave 11 baseline truncation
    swallowed the per-function status lines (theory-conflict log spam
    pushed them out of the saved message). Adding this guard makes the
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
    # the intended defect, credited as a clean frontend reject. (#route-100 r1)
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
)

# Two-token frontend rejections: both fragments must be present so the generic
# leading phrase ("called logic function") cannot match unrelated log lines.
_FRONTEND_REJECTION_MARKER_PAIRS: tuple[tuple[str, str], ...] = (
    ("called non-ghost function", "in ghost context"),
    ("called logic function", "in program context"),
)


def _has_frontend_rejection_diagnostic(output: str) -> bool:
    """Return True when output carries a trust-wp frontend rejection diagnostic."""
    if any(marker in output for marker in _FRONTEND_REJECTION_MARKERS):
        return True
    return any(a in output and b in output for a, b in _FRONTEND_REJECTION_MARKER_PAIRS)


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
    expected_evidence = _KNOWN_EXPECTED_COMPILE_REJECTION_EVIDENCE.get(test_name)
    # An empty/absent evidence tuple must NEVER vacuously credit a rejection:
    # ``all(... for ... in ())`` is True, which would silently pass any compile
    # error for that test. Require at least one fragment, all of which must hit.
    if not expected_evidence:
        return False
    return all(fragment in output for fragment in expected_evidence)


def classify_should_fail_result(
    success: bool,
    output: str,
    source: str,
    test_name: str = "",
    exit_code: int | None = None,
) -> tuple[str, str | None]:
    """Classify a should_fail test result."""
    # Backend-superseded tests (#2686): Creusot rejects these due to Why3/Pearlite
    # limitations that don't apply to trust-wp's ay backend. trust-wp correctly
    # handling this code is a feature, not a failure. Count as "pass".
    # The reason is carried in the message (via BACKEND_PASS_PREFIX) by the
    # runner, not as a skip_reason, since the test is not being skipped.
    if _check_backend_superseded(test_name) is not None:
        if _detect_infrastructure_failure(output) is not None:
            return "error", None
        if _has_timeout_caused_errors(output):
            return "error", None
        if _has_rustc_panic(output):
            return "error", None
        if _has_panic_exit_status(output, exit_code):
            return "error", None
        if _has_ay_panic_marker(output):
            return "error", None
        if _has_caught_panic_marker(output):
            return "error", None
        if not success and classify_error_category(output, exit_code) == "compile":
            return "error", None
        return "pass", None

    if _classify_should_fail_known_skip(source, test_name) is not None:
        return "error", None

    # Known false-accepts (#2690): should_fail tests where trust-wp incorrectly
    # verifies code that Creusot correctly rejects. These represent real
    # unsoundness gaps (ghost-type escape, snapshot self-reference) and must
    # be classified as "fail" (not "skip") so the false-accept count is
    # accurate and visible in reporting.
    if (false_accept_reason := _check_known_false_accept(test_name)) is not None:
        return "fail", false_accept_reason

    if success:
        # Vacuous-accept guard (Phase 12A, hash_map.rs regression):
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
            return "error", "vacuous accept: no verification activity"
        return "fail", None

    # Guard: detect false-accepts even when the success flag is wrong (#2690).
    # During reclassification the success flag is inferred from stored output;
    # if the exit-code extraction misses the wire format, success may be False
    # while the output clearly shows clean verification.  Treat that as a
    # false-accept (fail) rather than a correct rejection (pass).
    if _has_verified_contracts(output) and not _has_verification_failures(output):
        return "fail", None

    if _has_rustc_panic(output):
        return "error", None
    if _has_panic_exit_status(output, exit_code):
        return "error", None

    # ay solver panics (#2690): any phase-qualified ay panic variant
    # (check_sat, verification, loop, proof_assert, etc.) is an internal
    # solver error and must classify as "error" in should_fail, not "pass".
    # Without this, phase variants like ``ay solver panic during check_sat``
    # fall through to later reason gates and get silently counted as valid
    # rejections.
    if _has_ay_panic_marker(output):
        return "error", None

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
        return "error", None

    # Genuine obligation failures are correct should_fail rejections (#route-100).
    # When the trust-wp wire line reports ``failed > 0``, at least one proof
    # obligation was DISPROVEN with a validated counterexample — the program does
    # not verify, which is exactly the correct outcome for a should_fail test.
    # This must be credited even when a coarse should_succeed-oriented heuristic
    # (``_has_lra_unsupported_failures``, #2674) would otherwise demote the mixed
    # output to "unknown" via ``classify_failure`` because unrelated theory-
    # unsupported log spam co-occurs (e.g. terminates/incorrect_variant.rs: the
    # loop-variant decrease obligation fails with a model-validated counterexample
    # while a sibling logic postcondition churns). It is sound: ``failed > 0`` is
    # incompatible with a clean program-level accept — the false-accept guards
    # above already handled the ``verified>0 / failed==0`` pattern, and every
    # panic/infra guard has run — so a program-level false-accept is impossible
    # on this path. This gate only fires for should_fail tests the narrower
    # rejection gates below miss; it never turns a "pass" into a non-pass.
    wire_failed = _extract_wire_line_pairs(output)
    if wire_failed is not None and wire_failed.get("failed", 0) > 0:
        return "pass", None

    if _has_proof_assert_error_rejection(output):
        return "pass", None

    # Detect proof_assert failures as valid rejections (#2686).
    # A test with proof_assert_failed > 0 was correctly rejected even when the
    # function-level summary shows 0 failures (e.g. final_borrows.rs where all
    # functions are uncontracted but proof_asserts fail).
    if _has_proof_assert_failure_rejection(output):
        return "pass", None

    # Detect termination check errors as valid rejections (#2686).
    # When the driver detects structural termination problems (mutual recursion,
    # missing variant, etc.), it emits errors and exits with code 2 before
    # verification runs. These are correct rejections for should_fail tests that
    # exercise termination checking (e.g., terminates/ tests).
    if "termination check failed" in output:
        return "pass", None

    # Detect logic recursion check errors as valid rejections (#2686).
    # When the driver detects unconditional self-recursion or unsupported mutual
    # recursion among logic functions, it emits errors and compilation fails.
    # These are correct rejections (e.g., bug/1966.rs).
    if "logic recursion check failed" in output:
        return "pass", None

    # Detect frontend parse rejections as valid should-fail results. These are
    # source-level specification errors (e.g., unsupported array expressions in
    # contracts or empty Pearlite matches), not solver unknowns.
    if re.search(r"\bparse_errors=([1-9]\d*)\b", output):
        return "pass", None

    # Detect duplicate/conflicting extern_spec declarations as valid rejections
    # (#2686). When the driver detects that a local extern_spec! conflicts with
    # a built-in trust-wp-std spec or another local extern_spec!, it emits errors
    # and stops compilation. This is a correct rejection (e.g., duplicate_specs.rs).
    if "duplicate/conflicting extern_spec" in output:
        return "pass", None

    # Detect trusted contract validation errors as valid rejections (#2686).
    # This covers bug/1762.rs, where a #[trusted] program function has a
    # #[requires] clause that calls a #[check(ghost)] function.
    if "trusted contract validation" in output:
        return "pass", None

    # Detect ghost type escape errors as valid rejections (#2686).
    # When the driver detects that a non-logic, non-ghost function accepts
    # Ghost<T>/Snapshot<T> parameters and returns a non-ghost type, it emits
    # errors and stops compilation. This catches unsound extraction of ghost
    # values into program context (e.g., generic_deref_ghost.rs).
    if "ghost type escape" in output:
        return "pass", None

    # Detect recursive Snapshot<&mut T> type errors as valid rejections
    # (#2686). This covers bug/436_2.rs, where the driver now emits
    # "snapshot self-reference: type Bad contains Snapshot<&mut T>" and exits
    # before verification can falsely accept the circular snapshot reasoning.
    if _has_snapshot_self_reference_rejection(output):
        return "pass", None

    # Frontend rejection diagnostics (#2686 follow-up): trust-wp deliberately
    # refused to compile/encode the program for a specific semantic reason
    # (raw-pointer deref, ghost/program-context violations, logic-op gaps,
    # law/trait-refinement mismatches, etc.). This gate runs only after the
    # false-accept and panic guards above, so a clean accept or an internal
    # crash can never be miscredited as a rejection.
    if _has_frontend_rejection_diagnostic(output):
        return "pass", None

    # A non-zero process status is the expected transport for this lane, so use
    # the should-succeed classifier only to interpret its semantic diagnostics.
    # Crash/panic/infrastructure exits were screened above; forwarding the
    # process code here would trigger the ordinary lane's fail-closed success
    # guard and erase genuine should-fail rejection evidence.
    raw_status, raw_reason = classify_failure(output, source, exit_code=None)
    if raw_status == "skip":
        return "error", None
    if raw_status == "unknown":
        return "unknown", None
    if raw_status == "error":
        error_category = classify_error_category(output, exit_code)
        if error_category == "compile":
            if _has_allowlisted_compile_rejection_evidence(output, test_name):
                return "pass", None
            return "error", raw_reason
        return "error", raw_reason
    if raw_status == "pass":
        # Vacuous-accept guard (Phase 12A, hash_map.rs regression):
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
            return "error", "vacuous accept: no verification activity"
        return "fail", None
    if raw_status == "fail":
        return "pass", None

    return "error", None


def classify_error_category(
    output: str,
    exit_code: int | None = None,
) -> str:
    """Sub-classify an error result into a specific failure category."""
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
    # regardless of phase variant (#2690).  Historical check only matched
    # the ``during verification`` variant, missing check_sat / loop /
    # proof_assert / per-function ``ay solver panicked`` emissions.
    if _has_ay_panic_marker(output):
        return "ay_panic"

    # Caught per-function panics take priority over driver_panic (#2690).
    # Phase variants like ``panicked during proof_assert:`` and
    # ``panicked during loop verification:`` were previously misclassified
    # as driver_panic because only the verification variant was matched.
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
    # Previously these fell through to "unknown".
    if "ghost validation error" in output_lower:
        return "ghost_validation"

    if "trust-wp: error:" in output_lower:
        return "encoding"

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
    "STRICT_PASS_PREFIX",
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
