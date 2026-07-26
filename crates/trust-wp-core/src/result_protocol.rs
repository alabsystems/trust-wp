// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structured verification result protocol for `trust-wp-rustc` → `cargo-trust-wp`
//! communication.
//!
//! Replaces brittle stderr text parsing with a fixed ASCII wire format.
//! The wire line is emitted by `trust-wp-rustc` when `TRUST_WP_RESULT_PROTOCOL=1`
//! is set, and parsed by `cargo-trust-wp` to derive exit codes.
//!
//! Wire format:
//! ```text
//! TRUST_WP_RESULT:v1 base_exit_code=1 verified=2 failed=1 errors=0 ...
//! ```
//!
//! Design: `designs/2026-03-12-1690-structured-result-protocol.md`

/// Wire line prefix. Reject lines with unknown schema versions.
pub const WIRE_PREFIX: &str = "TRUST_WP_RESULT:v1";

/// Machine-readable per-obligation diagnostic line prefix.
///
/// `cargo-trust-wp` treats this as ordinary stderr today, so adding this side
/// channel does not change `TRUST_WP_RESULT:v1` parsing or exit-code behavior.
pub const DIAGNOSTIC_WIRE_PREFIX: &str = "TRUST_WP_DIAGNOSTIC:v1";

/// Environment variable that `cargo-trust-wp` sets to request structured output.
pub const RESULT_PROTOCOL_ENV: &str = "TRUST_WP_RESULT_PROTOCOL";

/// Structured verification result record.
///
/// All fields are integer counters. The wire format is a space-separated
/// sequence of `key=value` pairs after the `TRUST_WP_RESULT:v1` prefix.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StructuredVerificationResult {
    /// Base exit code from the driver's `VerificationSummary::exit_code()`.
    pub base_exit_code: i32,
    /// Functions whose contracts were proven correct.
    pub verified: u64,
    /// Functions whose contracts were disproven.
    pub failed: u64,
    /// Functions with encoding/solver errors.
    pub errors: u64,
    /// Dropped obligation warnings.
    pub warnings: u64,
    /// Functions whose contracts were assumed correct.
    pub assumed: u64,
    /// `#[trusted]`-annotated functions skipped by design.
    pub trusted: u64,
    /// Functions skipped (no MIR body).
    pub skipped: u64,
    /// Functions verified but depending on unproven axioms.
    pub verified_with_axiom_deps: u64,
    /// Logic function postconditions that could not be verified.
    pub unverified_axioms: u64,
    /// Functions where verification was vacuous.
    pub vacuous: u64,
    /// Verified-shaped results that lacked accepted proof evidence.
    pub evidence_gaps: u64,
    /// `proof_assert` statements that failed.
    pub proof_assert_failed: u64,
    /// `proof_assert` statements with errors.
    pub proof_assert_errors: u64,
    /// Functions where driver-level processing panicked.
    pub panics: u64,
    /// Functions demoted from Verified to Unknown.
    pub demoted: u64,
    /// Contract/logic parse errors (Slice 2: currently zero in Slice 1).
    pub parse_errors: u64,
    /// Termination check errors (Slice 2: currently zero in Slice 1).
    pub termination_errors: u64,
    /// Logic recursion errors (Slice 2: currently zero in Slice 1).
    pub logic_recursion_errors: u64,
    /// `#[erasure(target)]` validation errors (Phase 5c THIR-equivalence scaffold).
    ///
    /// Counts every `(lhs, rhs)` erasure pair where the driver-side check failed.
    /// The current driver implementation performs a STUB check (target resolvable,
    /// rhs has a non-empty body). Full Creusot-grade THIR-equivalence after
    /// ghost-stripping + A-normal form is deferred. See
    /// `crates/trust-wp-driver/src/callbacks/discovery/erasure.rs`.
    pub erasure_errors: u64,
}

impl StructuredVerificationResult {
    /// Serialize to the wire line format.
    ///
    /// Produces a single line suitable for stderr emission.
    #[must_use]
    pub fn to_wire_line(&self) -> String {
        format!(
            "{WIRE_PREFIX} base_exit_code={} verified={} failed={} errors={} warnings={} \
             assumed={} trusted={} skipped={} verified_with_axiom_deps={} \
             unverified_axioms={} vacuous={} evidence_gaps={} proof_assert_failed={} \
             proof_assert_errors={} panics={} demoted={} \
             parse_errors={} termination_errors={} logic_recursion_errors={} \
             erasure_errors={}",
            self.base_exit_code,
            self.verified,
            self.failed,
            self.errors,
            self.warnings,
            self.assumed,
            self.trusted,
            self.skipped,
            self.verified_with_axiom_deps,
            self.unverified_axioms,
            self.vacuous,
            self.evidence_gaps,
            self.proof_assert_failed,
            self.proof_assert_errors,
            self.panics,
            self.demoted,
            self.parse_errors,
            self.termination_errors,
            self.logic_recursion_errors,
            self.erasure_errors,
        )
    }

    /// Parse a wire line into a `StructuredVerificationResult`.
    ///
    /// Returns `None` if the line doesn't start with the expected prefix or
    /// omits required fields. Unknown keys are ignored for forward
    /// compatibility.
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn from_wire_line(line: &str) -> Option<Self> {
        const SEEN_BASE_EXIT_CODE: u32 = 1 << 0;
        const SEEN_VERIFIED: u32 = 1 << 1;
        const SEEN_FAILED: u32 = 1 << 2;
        const SEEN_ERRORS: u32 = 1 << 3;
        const SEEN_WARNINGS: u32 = 1 << 4;
        const SEEN_ASSUMED: u32 = 1 << 5;
        const SEEN_TRUSTED: u32 = 1 << 6;
        const SEEN_SKIPPED: u32 = 1 << 7;
        const SEEN_AXIOM_DEPS: u32 = 1 << 8;
        const SEEN_UNVERIFIED_AXIOMS: u32 = 1 << 9;
        const SEEN_VACUOUS: u32 = 1 << 10;
        const SEEN_EVIDENCE_GAPS: u32 = 1 << 11;
        const SEEN_PROOF_ASSERT_FAILED: u32 = 1 << 12;
        const SEEN_PROOF_ASSERT_ERRORS: u32 = 1 << 13;
        const SEEN_PANICS: u32 = 1 << 14;
        const SEEN_DEMOTED: u32 = 1 << 15;
        const SEEN_PARSE_ERRORS: u32 = 1 << 16;
        const SEEN_TERMINATION_ERRORS: u32 = 1 << 17;
        const SEEN_LOGIC_RECURSION_ERRORS: u32 = 1 << 18;
        const SEEN_ERASURE_ERRORS: u32 = 1 << 19;
        const REQUIRED_FIELDS: u32 = SEEN_BASE_EXIT_CODE
            | SEEN_VERIFIED
            | SEEN_FAILED
            | SEEN_ERRORS
            | SEEN_WARNINGS
            | SEEN_ASSUMED
            | SEEN_TRUSTED
            | SEEN_SKIPPED
            | SEEN_AXIOM_DEPS
            | SEEN_UNVERIFIED_AXIOMS
            | SEEN_VACUOUS
            | SEEN_EVIDENCE_GAPS
            | SEEN_PROOF_ASSERT_FAILED
            | SEEN_PROOF_ASSERT_ERRORS
            | SEEN_PANICS
            | SEEN_DEMOTED
            | SEEN_PARSE_ERRORS
            | SEEN_TERMINATION_ERRORS
            | SEEN_LOGIC_RECURSION_ERRORS
            | SEEN_ERASURE_ERRORS;

        let rest = line.strip_prefix(WIRE_PREFIX)?.trim_start();
        let mut result = Self::default();
        let mut seen_fields = 0u32;

        for pair in rest.split_whitespace() {
            let (key, value) = pair.split_once('=')?;
            match key {
                "base_exit_code" => {
                    result.base_exit_code = value.parse().ok()?;
                    seen_fields |= SEEN_BASE_EXIT_CODE;
                }
                "verified" => {
                    result.verified = value.parse().ok()?;
                    seen_fields |= SEEN_VERIFIED;
                }
                "failed" => {
                    result.failed = value.parse().ok()?;
                    seen_fields |= SEEN_FAILED;
                }
                "errors" => {
                    result.errors = value.parse().ok()?;
                    seen_fields |= SEEN_ERRORS;
                }
                "warnings" => {
                    result.warnings = value.parse().ok()?;
                    seen_fields |= SEEN_WARNINGS;
                }
                "assumed" => {
                    result.assumed = value.parse().ok()?;
                    seen_fields |= SEEN_ASSUMED;
                }
                "trusted" => {
                    result.trusted = value.parse().ok()?;
                    seen_fields |= SEEN_TRUSTED;
                }
                "skipped" => {
                    result.skipped = value.parse().ok()?;
                    seen_fields |= SEEN_SKIPPED;
                }
                "verified_with_axiom_deps" => {
                    result.verified_with_axiom_deps = value.parse().ok()?;
                    seen_fields |= SEEN_AXIOM_DEPS;
                }
                "unverified_axioms" => {
                    result.unverified_axioms = value.parse().ok()?;
                    seen_fields |= SEEN_UNVERIFIED_AXIOMS;
                }
                "vacuous" => {
                    result.vacuous = value.parse().ok()?;
                    seen_fields |= SEEN_VACUOUS;
                }
                "evidence_gaps" => {
                    result.evidence_gaps = value.parse().ok()?;
                    seen_fields |= SEEN_EVIDENCE_GAPS;
                }
                "proof_assert_failed" => {
                    result.proof_assert_failed = value.parse().ok()?;
                    seen_fields |= SEEN_PROOF_ASSERT_FAILED;
                }
                "proof_assert_errors" => {
                    result.proof_assert_errors = value.parse().ok()?;
                    seen_fields |= SEEN_PROOF_ASSERT_ERRORS;
                }
                "panics" => {
                    result.panics = value.parse().ok()?;
                    seen_fields |= SEEN_PANICS;
                }
                "demoted" => {
                    result.demoted = value.parse().ok()?;
                    seen_fields |= SEEN_DEMOTED;
                }
                "parse_errors" => {
                    result.parse_errors = value.parse().ok()?;
                    seen_fields |= SEEN_PARSE_ERRORS;
                }
                "termination_errors" => {
                    result.termination_errors = value.parse().ok()?;
                    seen_fields |= SEEN_TERMINATION_ERRORS;
                }
                "logic_recursion_errors" => {
                    result.logic_recursion_errors = value.parse().ok()?;
                    seen_fields |= SEEN_LOGIC_RECURSION_ERRORS;
                }
                "erasure_errors" => {
                    result.erasure_errors = value.parse().ok()?;
                    seen_fields |= SEEN_ERASURE_ERRORS;
                }
                _ => {} // Forward compatibility: ignore unknown keys
            }
        }

        (seen_fields == REQUIRED_FIELDS).then_some(result)
    }

    /// Merge another result into this one by summing counters.
    ///
    /// After merging, `base_exit_code` is normalized from the merged counters
    /// while preserving a nonzero producer-provided base code when no counter
    /// explains the failure.
    pub fn merge(&mut self, other: &Self) {
        let producer_base_exit_code =
            preserve_nonzero_exit_code(self.base_exit_code, other.base_exit_code);

        self.verified += other.verified;
        self.failed += other.failed;
        self.errors += other.errors;
        self.warnings += other.warnings;
        self.assumed += other.assumed;
        self.trusted += other.trusted;
        self.skipped += other.skipped;
        self.verified_with_axiom_deps += other.verified_with_axiom_deps;
        self.unverified_axioms += other.unverified_axioms;
        self.vacuous += other.vacuous;
        self.evidence_gaps += other.evidence_gaps;
        self.proof_assert_failed += other.proof_assert_failed;
        self.proof_assert_errors += other.proof_assert_errors;
        self.panics += other.panics;
        self.demoted += other.demoted;
        self.parse_errors += other.parse_errors;
        self.termination_errors += other.termination_errors;
        self.logic_recursion_errors += other.logic_recursion_errors;
        self.erasure_errors += other.erasure_errors;

        self.base_exit_code = producer_base_exit_code;
        self.normalize_exit_code();
    }

    /// Return the fail-closed process/status code represented by this record.
    ///
    /// Structured counters are authoritative whenever they explain a nonzero
    /// result. A producer-provided nonzero `base_exit_code` is preserved only
    /// for older/malformed records where no counter explains the failure.
    #[must_use]
    pub fn effective_exit_code(&self) -> i32 {
        match self.compute_exit_code() {
            0 => self.base_exit_code,
            computed => computed,
        }
    }

    /// Rewrite `base_exit_code` to the fail-closed status represented by this record.
    pub fn normalize_exit_code(&mut self) {
        self.base_exit_code = self.effective_exit_code();
    }

    /// Recompute exit code from counters using driver precedence.
    ///
    /// Priority: parse errors (3) > failures (1) > errors/soundness gaps (2) > 0.
    fn compute_exit_code(&self) -> i32 {
        if self.parse_errors > 0 {
            return 3;
        }
        if self.termination_errors > 0 || self.logic_recursion_errors > 0 || self.erasure_errors > 0
        {
            return 2;
        }

        let has_failed = self.failed > 0 || self.proof_assert_failed > 0;
        let has_errors = self.errors > 0 || self.proof_assert_errors > 0 || self.panics > 0;

        if has_failed {
            1
        } else if has_errors || self.has_soundness_gap() {
            2
        } else {
            0
        }
    }

    fn has_soundness_gap(&self) -> bool {
        self.trusted > 0
            || self.skipped > 0
            || self.assumed > 0
            || self.verified_with_axiom_deps > 0
            || self.unverified_axioms > 0
            || self.vacuous > 0
            || self.evidence_gaps > 0
    }
}

fn preserve_nonzero_exit_code(current: i32, incoming: i32) -> i32 {
    if current != 0 {
        current
    } else {
        incoming
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_default() {
        let result = StructuredVerificationResult::default();
        let line = result.to_wire_line();
        let parsed = StructuredVerificationResult::from_wire_line(&line).unwrap();
        assert_eq!(result, parsed);
    }

    #[test]
    fn roundtrip_with_values() {
        let result = StructuredVerificationResult {
            base_exit_code: 1,
            verified: 5,
            failed: 2,
            errors: 1,
            warnings: 3,
            assumed: 0,
            trusted: 1,
            skipped: 0,
            verified_with_axiom_deps: 0,
            unverified_axioms: 2,
            vacuous: 4,
            evidence_gaps: 5,
            proof_assert_failed: 1,
            proof_assert_errors: 0,
            panics: 0,
            demoted: 0,
            parse_errors: 0,
            termination_errors: 0,
            logic_recursion_errors: 0,
            erasure_errors: 0,
        };
        let line = result.to_wire_line();
        assert!(line.starts_with(WIRE_PREFIX));
        let parsed = StructuredVerificationResult::from_wire_line(&line).unwrap();
        assert_eq!(result, parsed);
    }

    #[test]
    fn from_wire_line_rejects_wrong_prefix() {
        assert!(
            StructuredVerificationResult::from_wire_line("TRUST_WP_RESULT:v2 verified=1").is_none()
        );
        assert!(StructuredVerificationResult::from_wire_line("NOT_TRUST_WP verified=1").is_none());
    }

    #[test]
    fn from_wire_line_ignores_unknown_keys() {
        let line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=3 failed=0 errors=0 warnings=0 \
                     assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 \
                     unverified_axioms=0 vacuous=0 evidence_gaps=0 proof_assert_failed=0 \
                     proof_assert_errors=0 panics=0 demoted=0 \
                     parse_errors=0 termination_errors=0 logic_recursion_errors=0 \
                     erasure_errors=0 future_field=42";
        let parsed = StructuredVerificationResult::from_wire_line(line).unwrap();
        assert_eq!(parsed.verified, 3);
        assert_eq!(parsed.base_exit_code, 0);
    }

    #[test]
    fn from_wire_line_rejects_malformed_value() {
        let line = "TRUST_WP_RESULT:v1 base_exit_code=abc";
        assert!(StructuredVerificationResult::from_wire_line(line).is_none());
    }

    #[test]
    fn merge_sums_counters() {
        let mut a = StructuredVerificationResult {
            base_exit_code: 0,
            verified: 3,
            failed: 0,
            errors: 0,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            base_exit_code: 1,
            verified: 2,
            failed: 1,
            errors: 0,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.verified, 5);
        assert_eq!(a.failed, 1);
        // Recomputed: failed > 0 → exit code 1
        assert_eq!(a.base_exit_code, 1);
    }

    #[test]
    fn merge_recomputes_exit_code_from_merged_counters() {
        let mut a = StructuredVerificationResult {
            base_exit_code: 0,
            verified: 2,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            base_exit_code: 2,
            errors: 3,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.base_exit_code, 2);
    }

    #[test]
    fn merge_preserves_unexplained_nonzero_base_exit_code() {
        let mut a = StructuredVerificationResult {
            base_exit_code: 2,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            verified: 3,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.base_exit_code, 2);
    }

    #[test]
    fn merge_recomputes_failure_precedence_over_soundness_gap() {
        let mut a = StructuredVerificationResult {
            skipped: 1,
            ..Default::default()
        };
        a.normalize_exit_code();

        let b = StructuredVerificationResult {
            base_exit_code: 1,
            failed: 1,
            ..Default::default()
        };

        a.merge(&b);
        assert_eq!(a.base_exit_code, 1);
    }

    #[test]
    fn merge_parse_errors_take_highest_priority() {
        let mut a = StructuredVerificationResult {
            base_exit_code: 1,
            failed: 1,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            parse_errors: 1,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.base_exit_code, 3);
    }

    #[test]
    fn compute_exit_code_assumed_only() {
        let result = StructuredVerificationResult {
            assumed: 2,
            ..Default::default()
        };
        assert_eq!(result.compute_exit_code(), 2);
    }

    #[test]
    fn effective_exit_code_fails_closed_for_structural_error_counters() {
        let parse = StructuredVerificationResult {
            base_exit_code: 0,
            parse_errors: 1,
            ..Default::default()
        };
        assert_eq!(parse.effective_exit_code(), 3);

        let termination = StructuredVerificationResult {
            base_exit_code: 0,
            termination_errors: 1,
            ..Default::default()
        };
        assert_eq!(termination.effective_exit_code(), 2);

        let logic_recursion = StructuredVerificationResult {
            base_exit_code: 0,
            logic_recursion_errors: 1,
            ..Default::default()
        };
        assert_eq!(logic_recursion.effective_exit_code(), 2);
    }

    #[test]
    fn normalize_exit_code_sets_result_status_for_soundness_gaps() {
        let cases = [
            StructuredVerificationResult {
                assumed: 1,
                ..Default::default()
            },
            StructuredVerificationResult {
                trusted: 1,
                ..Default::default()
            },
            StructuredVerificationResult {
                skipped: 1,
                ..Default::default()
            },
        ];

        for mut result in cases {
            result.normalize_exit_code();
            assert_eq!(result.base_exit_code, 2, "{result:?}");
        }
    }

    #[test]
    fn compute_exit_code_axiom_deps_only() {
        let result = StructuredVerificationResult {
            verified_with_axiom_deps: 1,
            ..Default::default()
        };
        assert_eq!(result.compute_exit_code(), 2);
    }

    #[test]
    fn compute_exit_code_trusted_or_skipped_are_soundness_gaps() {
        let trusted = StructuredVerificationResult {
            trusted: 1,
            ..Default::default()
        };
        assert_eq!(trusted.compute_exit_code(), 2);

        let skipped = StructuredVerificationResult {
            skipped: 1,
            ..Default::default()
        };
        assert_eq!(skipped.compute_exit_code(), 2);
    }

    #[test]
    fn compute_exit_code_mixed_soundness_gaps_are_errors() {
        let trusted = StructuredVerificationResult {
            verified: 2,
            trusted: 1,
            ..Default::default()
        };
        assert_eq!(trusted.compute_exit_code(), 2);

        let skipped = StructuredVerificationResult {
            verified: 2,
            skipped: 1,
            ..Default::default()
        };
        assert_eq!(skipped.compute_exit_code(), 2);

        let assumed = StructuredVerificationResult {
            verified: 2,
            assumed: 1,
            ..Default::default()
        };
        assert_eq!(assumed.compute_exit_code(), 2);

        let axiom_deps = StructuredVerificationResult {
            verified: 2,
            verified_with_axiom_deps: 1,
            ..Default::default()
        };
        assert_eq!(axiom_deps.compute_exit_code(), 2);

        let unverified_axioms = StructuredVerificationResult {
            verified: 2,
            unverified_axioms: 1,
            ..Default::default()
        };
        assert_eq!(unverified_axioms.compute_exit_code(), 2);

        let vacuous = StructuredVerificationResult {
            verified: 2,
            vacuous: 1,
            ..Default::default()
        };
        assert_eq!(vacuous.compute_exit_code(), 2);

        let evidence_gap = StructuredVerificationResult {
            verified: 2,
            evidence_gaps: 1,
            ..Default::default()
        };
        assert_eq!(evidence_gap.compute_exit_code(), 2);
    }

    #[test]
    fn wire_line_is_single_line() {
        let result = StructuredVerificationResult {
            base_exit_code: 1,
            verified: 10,
            failed: 1,
            ..Default::default()
        };
        let line = result.to_wire_line();
        assert!(!line.contains('\n'));
    }

    #[test]
    fn from_wire_line_rejects_incomplete_payload() {
        assert!(StructuredVerificationResult::from_wire_line("TRUST_WP_RESULT:v1").is_none());
        assert!(StructuredVerificationResult::from_wire_line(
            "TRUST_WP_RESULT:v1 base_exit_code=0"
        )
        .is_none());
    }

    #[test]
    fn from_wire_line_rejects_legacy_payload_missing_soundness_gap_fields() {
        let line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=1 failed=0 errors=0 warnings=0 \
                    assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 \
                    proof_assert_failed=0 proof_assert_errors=0 panics=0 demoted=0 \
                    parse_errors=0 termination_errors=0 logic_recursion_errors=0";
        assert!(StructuredVerificationResult::from_wire_line(line).is_none());
    }

    #[test]
    fn from_wire_line_rejects_legacy_payload_missing_evidence_gaps() {
        let line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=1 failed=0 errors=0 warnings=0 \
                    assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 \
                    unverified_axioms=0 vacuous=0 proof_assert_failed=0 \
                    proof_assert_errors=0 panics=0 demoted=0 \
                    parse_errors=0 termination_errors=0 logic_recursion_errors=0";
        assert!(StructuredVerificationResult::from_wire_line(line).is_none());
    }

    #[test]
    fn from_wire_line_rejects_legacy_payload_missing_erasure_errors() {
        // Phase 5c: erasure_errors is a newly required field.
        let line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=1 failed=0 errors=0 warnings=0 \
                    assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 \
                    unverified_axioms=0 vacuous=0 evidence_gaps=0 proof_assert_failed=0 \
                    proof_assert_errors=0 panics=0 demoted=0 \
                    parse_errors=0 termination_errors=0 logic_recursion_errors=0";
        assert!(StructuredVerificationResult::from_wire_line(line).is_none());
    }

    #[test]
    fn effective_exit_code_fails_closed_for_erasure_errors() {
        // Phase 5c: erasure_errors triggers exit code 2 (encoding/structural error).
        let erasure = StructuredVerificationResult {
            base_exit_code: 0,
            erasure_errors: 1,
            ..Default::default()
        };
        assert_eq!(erasure.effective_exit_code(), 2);
    }

    #[test]
    fn merge_sums_erasure_errors() {
        let mut a = StructuredVerificationResult {
            erasure_errors: 1,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            erasure_errors: 2,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.erasure_errors, 3);
        // erasure_errors > 0 should normalize to exit code 2.
        assert_eq!(a.base_exit_code, 2);
    }
}
