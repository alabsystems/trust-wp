#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Low-level output and source signal helpers for harness classification."""

from __future__ import annotations

import re

try:
    from tests.creusot_compat.harness_model import parse_wire_line, WIRE_PREFIX
except ModuleNotFoundError:
    from harness_model import parse_wire_line, WIRE_PREFIX

INFRASTRUCTURE_FAILURE_PATTERNS: tuple[tuple[re.Pattern[str], str], ...] = (
    (
        re.compile(r"\btimeout after \d+s\b", re.IGNORECASE),
        "timeout",
    ),
    (
        re.compile(r"cargo-trust-wp not built at\b", re.IGNORECASE),
        "missing cargo-trust-wp binary",
    ),
    (
        re.compile(
            r"failed to download from [`\"]?https://index\.crates\.io/config\.json[`\"]?",
            re.IGNORECASE,
        ),
        "network download failure",
    ),
    (
        re.compile(r"failed to query (?:replaced )?source registry", re.IGNORECASE),
        "network registry failure",
    ),
    (
        re.compile(r"spurious network error", re.IGNORECASE),
        "network error",
    ),
)

_OUTPUT_UNSUPPORTED_PATTERNS: tuple[tuple[str, str], ...] = (
    (r"trait.*not.*supported", "trait specs"),
    (r"closure.*not.*supported", "closures"),
    (r"impl.*not.*supported", "impl blocks"),
    (r"derive.*not.*supported", "derive macros"),
)

_SOURCE_UNSUPPORTED_PATTERNS: tuple[tuple[str, str], ...] = (
    (r"snapshot::", "snapshot module"),
    (r"#\s*\[\s*open\s*\]", "open functions"),
    (r"\bFnGhost\b", "ghost closures"),
    # NO_REPLAY tests handled by dedicated _is_no_replay_source() check in
    # harness_runner.py: status-level compatibility pass, but strict
    # true-100/tier accounting treats it as incomplete proof evidence (#2001).
    #
    # Removed patterns (#2685):
    # - dyn Trait: trust-wp correctly rejects unsound dyn usage (failed=2)
    # - or-patterns: rustc desugars or-patterns before MIR; no crash
    #
    # Removed patterns (#2683):
    # - #[logic(prophetic)]: prophetic logic is now supported — Resolve trait
    #   has resolve_coherence, blanket impl removed (892439efc)
)

# The driver prints the offending type and `Snapshot<&mut T>` wrapped in
# rustc-style backticks (e.g. ``type `Bad` contains `Snapshot<&mut T>``), so the
# matcher must tolerate backticks/whitespace between the diagnostic prefix and
# the `Snapshot<&mut` marker. The distinctive ``snapshot self-reference:`` prefix
# is only ever emitted by the driver's self-reference rejection, so anchoring on
# it keeps this from matching ordinary ``Snapshot<&mut T>`` type mentions.
_SNAPSHOT_SELF_REFERENCE_REJECTION_RE = re.compile(
    r"snapshot self-reference:.*?Snapshot<\s*&\s*mut\b",
    re.IGNORECASE | re.DOTALL,
)


def _has_snapshot_self_reference_rejection(output: str) -> bool:
    """Detect the driver's type-level Snapshot<&mut T> self-reference rejection."""
    return bool(_SNAPSHOT_SELF_REFERENCE_REJECTION_RE.search(output))


def _has_ay_panic_marker(output: str) -> bool:
    """Detect any ay solver panic marker in output (#2690).

    ay solver panics are emitted with multiple phase-qualified variants:

    - ``ay solver panic during verification`` — whole-verification catch
    - ``ay solver panic during check_sat`` — ay library-level emit
    - ``ay solver panic during loop verification`` — loop panic boundary
    - ``ay solver panic during proof_assert`` — proof_assert driver
    - ``ay solver panicked:`` — per-function solver panic (setup/tail)
    - ``ay solver panic in loop_entry_may_execute`` — loop entry check

    Historically the classifier only matched the ``during verification``
    variant, which caused ay-sort-mismatch panics emitted during
    ``check_sat`` (e.g. ``binary_search_list.rs``) to be misclassified as
    ``caught_panic`` or ``driver_panic``.  This helper normalizes detection
    so every ay-panic variant takes the ``ay_panic`` category.
    """
    if "ay solver panic during " in output:
        return True
    if "ay solver panicked" in output:
        return True
    if "ay solver panic in " in output:
        return True
    return False


_CAUGHT_PANIC_MARKER_RE = re.compile(r"\bpanicked during\s+\w")


def _has_caught_panic_marker(output: str) -> bool:
    """Detect any phase-qualified caught per-function panic marker (#2690).

    The driver's per-function ``catch_unwind`` (#1975) emits ``panicked
    during <phase>:`` for panics it intercepts while verifying a single
    function.  Historical classification only matched the ``during
    verification`` variant, missing phase-qualified emissions such as:

    - ``panicked during verification:`` — main verification catch
    - ``panicked during proof_assert:`` — proof_assert driver catch
      (observed on ``mapping_test.rs`` in baseline-20260418)
    - ``panicked during loop verification:`` — loop body catch
    - ``panicked during check_sat:`` — check_sat wrapper catch
    - ``panicked during setup:`` / ``panicked during postcondition:`` —
      phase-specific catches

    Note that this helper deliberately does NOT match the ay solver's
    ``ay solver panic during <phase>`` form because that string uses
    ``panic`` (noun), not ``panicked`` (past tense); ay-internal panics are
    handled by ``_has_ay_panic_marker`` and take priority over caught
    per-function panics.  The regex ``\\bpanicked during \\w`` is therefore
    safe against collision with ay panic strings while remaining
    future-proof against new phase names the driver may emit.
    """
    return bool(_CAUGHT_PANIC_MARKER_RE.search(output))


def _has_rustc_panic(output: str) -> bool:
    """Detect rustc panic signatures in output.

    A rustc panic (``thread 'rustc' panicked``) indicates a compiler crash,
    which always takes priority over feature-skip or verification-failure
    classification.  (#883)

    Exception: ay sort panics caught by ``catch_ay_sort_panics`` still emit
    the ``thread 'rustc' panicked`` message via the default panic hook before
    ``catch_unwind`` intercepts them.  The driver then emits a
    ``ay solver panic during <phase>`` line confirming the panic was handled.
    These should not be classified as crashes.  (#885, #2690)

    Exception: per-function catch_unwind (#1975) catches panics during
    individual function verification.  The driver emits
    ``panicked during verification:`` for caught panics and continues with
    the remaining functions.  These are handled panics, not crashes.  (#2687)
    """
    if "thread 'rustc'" not in output or "panicked" not in output:
        return False
    if _has_ay_panic_marker(output):
        return False
    if _has_caught_panic_marker(output):
        return False
    return True


def _has_panic_exit_status(output: str, exit_code: int | None) -> bool:
    """Detect panic-like process termination even when panic text is suppressed."""
    has_status_101 = bool(re.search(r"exit status:\s*101\b", output))
    has_exit_101 = has_status_101 or exit_code == 101
    if not has_exit_101:
        return False

    output_lower = output.lower()
    if "panicked" in output_lower:
        return True

    has_compile_diag = (
        "error[e" in output_lower
        or "cannot find" in output_lower
        or "failed to parse" in output_lower
        or "due to previous error" in output_lower
        or "due to previous errors" in output_lower
        or bool(re.search(r"due to \d+ previous error", output_lower))
    )
    return not has_compile_diag


def _has_cargo_lock_contention(output: str) -> bool:
    """Detect cargo-lock contention in harness output.

    Two distinct contention signatures are treated as transient infrastructure
    noise (and thus retried), never as semantic test failures:

    1. ``[cargo-lock] Waiting for build lock`` -- the harness's own advisory
       build lock around a shared target directory.
    2. ``Blocking waiting for file lock on package cache`` -- cargo racing
       another process for the crates.io registry index/package-cache lock.
       This only appears when a concurrent cargo invocation is mutating the
       shared registry; it is never emitted by a real verification result.
    """
    return (
        "[cargo-lock] Waiting for build lock" in output
        or "Blocking waiting for file lock on package cache" in output
    )


def _detect_infrastructure_failure(output: str) -> str | None:
    """Return infrastructure-failure reason, or None when output is semantic."""
    if _has_cargo_lock_contention(output):
        return "cargo-lock contention"

    for pattern, reason in INFRASTRUCTURE_FAILURE_PATTERNS:
        if pattern.search(output):
            return reason

    return None


def _last_verification_summary_counts(output: str) -> tuple[int, int, int] | None:
    """Return (verified, failed, errors) from the last function-level summary."""
    last_counts: tuple[int, int, int] | None = None
    for line in output.split("\n"):
        if "proof_assert:" in line.lower():
            continue
        match = re.search(
            r"(\d+)\s+verified,\s+(\d+)\s+failed,\s+(\d+)\s+errors", line
        )
        if match:
            last_counts = (
                int(match.group(1)),
                int(match.group(2)),
                int(match.group(3)),
            )
    return last_counts


def _last_proof_assert_summary_counts(output: str) -> tuple[int, int, int] | None:
    """Return (verified, failed, errors) from the proof_assert summary line."""
    last_counts: tuple[int, int, int] | None = None
    for line in output.split("\n"):
        if "proof_assert:" not in line.lower():
            continue
        match = re.search(
            r"proof_assert:\s*(\d+)\s+verified,\s+(\d+)\s+failed,\s+(\d+)\s+errors",
            line,
        )
        if match:
            last_counts = (
                int(match.group(1)),
                int(match.group(2)),
                int(match.group(3)),
            )
    return last_counts


def _dropped_obligation_warning_count(output: str) -> int:
    """Return the count of dropped obligation warnings from the summary line."""
    count = 0
    for line in output.split("\n"):
        if "proof_assert:" in line.lower():
            continue
        match = re.search(
            r"(\d+)\s+warnings?\s+\(obligations?\s+dropped\)", line
        )
        if match:
            count = int(match.group(1))
    return count


def _has_verification_failures(output: str) -> bool:
    """Return True when trust-wp reported any rejected or unknown obligations."""
    if _dropped_obligation_warning_count(output) > 0:
        return True
    counts = _last_verification_summary_counts(output)
    if counts is not None:
        verified, failed, errors = counts
        if failed > 0 or errors > 0:
            return True
        # When function-level shows verified > 0, trust that summary and
        # do not fall through to proof_assert checks — proof_assert results
        # in that context are secondary (#2686 test compatibility).
        if verified > 0:
            return False

    # When function-level summary shows nothing (0/0/0 or absent), also check
    # proof_assert summary — a test can have 0 function-level activity but
    # still have proof_assert failures (e.g. final_borrows.rs where all
    # functions are uncontracted but proof_asserts fail).
    pa_counts = _last_proof_assert_summary_counts(output)
    if pa_counts is not None:
        _, pa_failed, pa_errors = pa_counts
        if pa_failed > 0 or pa_errors > 0:
            return True

    # If we had definitive counts and both showed 0, no need for fallbacks.
    if counts is not None and pa_counts is not None:
        return False

    output_lower = output.lower()
    has_fn_unknown = any(
        "unknown (" in line and "proof_assert" not in line
        for line in output_lower.split("\n")
        if "trust-wp:" in line
    )
    return (
        "failed ✗" in output_lower
        or "counterexample" in output_lower
        or has_fn_unknown
        or "trust-wp: error:" in output_lower
    )


def _verification_run_succeeded(returncode: int, output: str) -> bool:
    """Return True only for clean verification runs."""
    return (
        returncode == 0
        and _has_verified_contracts(output)
        and not _has_verification_failures(output)
    )


def _check_output_unsupported(output_lower: str) -> str | None:
    for pattern, reason in _OUTPUT_UNSUPPORTED_PATTERNS:
        if re.search(pattern, output_lower):
            return reason
    return None


def _check_source_unsupported(source: str) -> str | None:
    for pattern, reason in _SOURCE_UNSUPPORTED_PATTERNS:
        if re.search(pattern, source, re.IGNORECASE):
            return reason
    return None


def _last_contract_block_output(output: str) -> str:
    """Return output from the test crate's contract-discovery block onward."""
    lines = output.split("\n")
    start_idx = 0
    for idx, line in enumerate(lines):
        lower = line.lower()
        if "functions with contracts" not in lower:
            continue
        if re.search(r"found\s+(\d+)\s+functions? with contracts", lower):
            start_idx = idx
        elif re.search(r"functions with contracts found\s+count=(\d+)", lower):
            start_idx = idx
    return "\n".join(lines[start_idx:])


def _last_contract_count(output: str) -> int:
    """Extract the contract count from the last trust-wp invocation in the output."""
    last_count = 0
    for line in output.split("\n"):
        lower = line.lower().strip()
        if "functions with contracts" not in lower:
            continue
        match = re.search(r"found\s+(\d+)\s+functions? with contracts", lower)
        if match:
            last_count = int(match.group(1))
            continue
        match = re.search(r"functions with contracts found\s+count=(\d+)", lower)
        if match:
            last_count = int(match.group(1))
    return last_count


def _has_verified_contracts(output: str) -> bool:
    """Check whether at least one contract was actually verified."""
    test_block = _last_contract_block_output(output)
    if "verified ✓" in test_block:
        return True
    counts = _last_verification_summary_counts(output)
    if counts is None:
        return False
    verified, _, _ = counts
    return verified > 0


def _has_timeout_caused_errors(output: str) -> bool:
    """Return True when verification errors are caused by solver/hard timeouts.

    When the verification summary shows errors > 0 and failed == 0, the errors
    may be solver "Unknown" results.  Some of these are caused by timeouts
    (solver-level or hard timeouts), which should be classified as "error"
    (timeout category) rather than "unknown" (#2690).

    Detection patterns:
    - ``hard timeout expired`` anywhere in output
    - ``unknown (timeout)`` in per-function trust-wp status
    - ``unknown (loop invariant: timeout)`` in per-function trust-wp status
    - ``unknown (loop call obligations: timeout)`` in per-function status
    - ``unknown (...quantifier-round-limit...)`` (timeout-adjacent: solver
      exhausted quantifier instantiation budget)
    - ``incomplete (timeout)`` in per-function trust-wp status
    """
    if "hard timeout expired" in output:
        return True
    for line in output.split("\n"):
        lower = line.lower().strip()
        if "trust-wp:" not in lower:
            continue
        # Match per-function status lines indicating timeout
        if "unknown (timeout)" in lower:
            return True
        if "unknown (" in lower and "timeout" in lower:
            return True
        if "incomplete (timeout)" in lower:
            return True
        # quantifier-round-limit is timeout-adjacent: the solver exhausted
        # its quantifier instantiation budget, which is a resource limit
        # like a timeout (#2690).
        if "unknown (" in lower and "quantifier-round-limit" in lower:
            return True
    return False


def _wire_line_shows_pa_only_failure(output: str) -> bool:
    """Return True when valid telemetry shows proof_assert issues after function
    success.

    The check is deliberately limited to the aggregated ``TRUST_WP_RESULT`` line:
    if the driver produced valid telemetry showing clean function-level results
    and non-zero ``proof_assert_failed`` or ``proof_assert_errors``, the
    should-succeed classifier must not report a plain pass.
    """
    for line in reversed(output.split("\n")):
        stripped = line.strip()
        if not stripped.startswith(WIRE_PREFIX):
            continue
        telemetry = parse_wire_line(stripped)
        if telemetry is None:
            return False
        return (
            telemetry.verified > 0
            and telemetry.failed == 0
            and telemetry.errors == 0
            and telemetry.panics == 0
            and (
                telemetry.proof_assert_failed > 0
                or telemetry.proof_assert_errors > 0
            )
        )
    return False


def _has_lra_unsupported_failures(output: str) -> bool:
    """Return True when ay's LRA theory reports unsupported atoms.

    When ay's LRA (Linear Real Arithmetic) theory solver encounters formula
    atoms it cannot handle, it prints diagnostic messages like:

        LRA check_impl simplex=Sat but unsupported, returning Unknown

    In this state, the DPLL(T) solver may produce SAT results (with
    counterexamples) that violate theory constraints, because the LRA theory
    returned Unknown instead of detecting a conflict. These SAT results and
    their counterexamples are unreliable.

    When this pattern is detected alongside verification failures, the
    failures should be classified as solver errors rather than genuine
    counterexamples. (#2674)
    """
    return "LRA check_impl simplex=Sat but unsupported" in output


__all__ = [
    "INFRASTRUCTURE_FAILURE_PATTERNS",
    "_check_output_unsupported",
    "_check_source_unsupported",
    "_detect_infrastructure_failure",
    "_dropped_obligation_warning_count",
    "_has_cargo_lock_contention",
    "_has_caught_panic_marker",
    "_has_lra_unsupported_failures",
    "_has_panic_exit_status",
    "_has_rustc_panic",
    "_has_timeout_caused_errors",
    "_has_verification_failures",
    "_has_verified_contracts",
    "_has_ay_panic_marker",
    "_last_contract_block_output",
    "_last_contract_count",
    "_last_proof_assert_summary_counts",
    "_last_verification_summary_counts",
    "_verification_run_succeeded",
    "_wire_line_shows_pa_only_failure",
]
