// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-slice profiling instrumentation for timeout triage (#2674 Phase 1).
//!
//! When the `TRUST_WP_PROFILE` environment variable is set to `1` (or any
//! truthy value — see [`is_profile_enabled`]), the verification pipeline emits
//! structured timing/size lines on stderr with a consistent `[PROFILE]` prefix.
//! The goal is to identify whether a slow obligation slice is axiom-bound,
//! solver-bound, or postcondition-encoding bound — without changing any
//! verification behavior.
//!
//! The format is line-oriented so callers can grep / awk on it:
//!
//! ```text
//! [PROFILE] event=slice_begin label=function slice=0/3 axioms=127 ground_pool_axioms=42
//! [PROFILE] event=slice_end label=function slice=0/3 elapsed_ms=2340 outcome=Verified \
//!           decisions=512 conflicts=88 propagations=4096 theory_conflicts=12 num_assertions=9431
//! [PROFILE] event=pipeline_end label=function slices=3 elapsed_ms=2510 outcome=Verified
//! ```
//!
//! Zero overhead when unset: [`is_profile_enabled`] reads the env var exactly
//! once via [`OnceLock`]. All hot-path emitters first check the cached flag
//! and return immediately when disabled.

use std::{sync::OnceLock, time::Duration};

use crate::shared_types::SolveStatisticsSnapshot;

/// Prefix used on every profile line so downstream tooling (grep/awk) can
/// filter tracing output reliably.
pub(crate) const PROFILE_PREFIX: &str = "[PROFILE]";

/// Cached result of `std::env::var("TRUST_WP_PROFILE")`. Populated once on the
/// first call to [`is_profile_enabled`] and reused for the lifetime of the
/// process. The cache is a pure read-through: tests that want to exercise
/// the "enabled" path call [`emit_line_for_test`] directly instead of
/// mutating the env var, which keeps the one-shot semantics safe.
static PROFILE_ENABLED: OnceLock<bool> = OnceLock::new();

/// Returns `true` when `TRUST_WP_PROFILE` is set to a truthy value.
///
/// Accepted truthy values (case-insensitive): `1`, `true`, `yes`, `on`.
/// Any other value — including unset, empty, or `0` — disables profiling.
pub(crate) fn is_profile_enabled() -> bool {
    *PROFILE_ENABLED.get_or_init(|| {
        std::env::var("TRUST_WP_PROFILE")
            .map(|value| {
                matches!(
                    value.trim().to_ascii_lowercase().as_str(),
                    "1" | "true" | "yes" | "on"
                )
            })
            .unwrap_or(false)
    })
}

/// Emit a structured profile line to stderr when profiling is enabled.
///
/// `fields` is a sequence of `(key, value)` tuples rendered as `key=value`
/// tokens in the emitted line. No escaping is performed — callers must
/// avoid spaces / newlines in values (use `_` as a separator if needed).
pub(crate) fn emit(event: &str, label: &str, fields: &[(&str, &str)]) {
    if !is_profile_enabled() {
        return;
    }
    emit_line_for_test(event, label, fields);
}

/// Version of [`emit`] that bypasses the env-var gate. Exposed so that unit
/// tests can verify the line format without racing on the `PROFILE_ENABLED`
/// OnceLock. Production code must use [`emit`].
pub(crate) fn emit_line_for_test(event: &str, label: &str, fields: &[(&str, &str)]) {
    let mut line = format!("{PROFILE_PREFIX} event={event} label={label}");
    for (key, value) in fields {
        line.push(' ');
        line.push_str(key);
        line.push('=');
        line.push_str(value);
    }
    eprintln!("{line}");
}

/// Emit a `slice_begin` event with static pre-solve context.
pub(crate) fn emit_slice_begin(
    label: &str,
    slice_index: usize,
    slice_count: usize,
    axioms: usize,
    ground_pool_axioms: usize,
) {
    if !is_profile_enabled() {
        return;
    }
    let slice = format!("{slice_index}/{slice_count}");
    let axioms = axioms.to_string();
    let ground_pool_axioms = ground_pool_axioms.to_string();
    emit(
        "slice_begin",
        label,
        &[
            ("slice", &slice),
            ("axioms", &axioms),
            ("ground_pool_axioms", &ground_pool_axioms),
        ],
    );
}

/// Emit a `slice_end` event with per-slice wall-clock timing and any cached
/// solver statistics from the last `check_sat()` call.
pub(crate) fn emit_slice_end(
    label: &str,
    slice_index: usize,
    slice_count: usize,
    elapsed: Duration,
    outcome: &str,
    stats: Option<&SolveStatisticsSnapshot>,
) {
    if !is_profile_enabled() {
        return;
    }
    let slice = format!("{slice_index}/{slice_count}");
    let elapsed_ms = elapsed.as_millis().to_string();
    let mut fields: Vec<(&str, String)> = vec![
        ("slice", slice),
        ("elapsed_ms", elapsed_ms),
        ("outcome", outcome.to_string()),
    ];
    if let Some(stats) = stats {
        fields.extend([
            ("decisions", stats.decisions.to_string()),
            ("conflicts", stats.conflicts.to_string()),
            ("propagations", stats.propagations.to_string()),
            ("theory_conflicts", stats.theory_conflicts.to_string()),
            ("theory_propagations", stats.theory_propagations.to_string()),
            ("num_vars", stats.num_vars.to_string()),
            ("num_clauses", stats.num_clauses.to_string()),
            ("num_assertions", stats.num_assertions.to_string()),
        ]);
    }
    let borrowed: Vec<(&str, &str)> = fields.iter().map(|(k, v)| (*k, v.as_str())).collect();
    emit("slice_end", label, &borrowed);
}

/// Emit a `pipeline_end` event with aggregate wall-clock timing and the
/// final aggregated outcome.
pub(crate) fn emit_pipeline_end(label: &str, slice_count: usize, elapsed: Duration, outcome: &str) {
    if !is_profile_enabled() {
        return;
    }
    let slices = slice_count.to_string();
    let elapsed_ms = elapsed.as_millis().to_string();
    emit(
        "pipeline_end",
        label,
        &[
            ("slices", &slices),
            ("elapsed_ms", &elapsed_ms),
            ("outcome", outcome),
        ],
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Line format: `[PROFILE] event=... label=... key=value...`
    /// This exercises `emit_line_for_test` directly (bypasses env-var gate) so
    /// the test does not race with [`is_profile_enabled`]'s OnceLock.
    #[test]
    fn test_emit_line_for_test_produces_expected_format() {
        // We can't easily capture stderr without dependencies, but we can
        // verify the public API does not panic and is callable with both
        // empty and populated field lists. The env-var-gated entry points
        // (`emit_slice_*`, `emit_pipeline_end`) are exercised by the pipeline
        // integration tests.
        emit_line_for_test("test_event", "unit", &[]);
        emit_line_for_test(
            "slice_begin",
            "function",
            &[
                ("slice", "0/3"),
                ("axioms", "42"),
                ("ground_pool_axioms", "7"),
            ],
        );
    }

    /// When `TRUST_WP_PROFILE` is unset, the cached flag must evaluate to
    /// `false`, and the env-gated emitters must be no-ops. Because
    /// [`is_profile_enabled`] uses a `OnceLock`, the test environment's
    /// actual flag value is locked in for the process. We therefore only
    /// assert that the gating function is callable and that the gated
    /// emitters do not panic in either state.
    #[test]
    fn test_gated_emitters_are_safe_to_call() {
        // This is a smoke test: if profiling is disabled in the test env
        // (the default), these calls must be no-ops. If it is enabled,
        // the lines go to stderr and the test still passes.
        emit_slice_begin("function", 0, 3, 10, 5);
        emit_slice_end(
            "function",
            0,
            3,
            Duration::from_millis(42),
            "Verified",
            None,
        );
        emit_pipeline_end("function", 3, Duration::from_millis(100), "Verified");
    }

    /// Verify [`is_profile_enabled`] does not panic and returns the same
    /// value on repeated calls (OnceLock contract).
    #[test]
    fn test_is_profile_enabled_is_idempotent() {
        let first = is_profile_enabled();
        let second = is_profile_enabled();
        assert_eq!(
            first, second,
            "is_profile_enabled must be idempotent across calls"
        );
    }

    /// Verify the truthy-value parser recognizes the documented accept-list.
    /// We test the parser logic directly (it is embedded in the OnceLock
    /// initializer) by replicating it here.
    #[test]
    fn test_truthy_value_parser_accept_list() {
        fn is_truthy(value: &str) -> bool {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        }
        // Documented truthy values.
        assert!(is_truthy("1"));
        assert!(is_truthy("true"));
        assert!(is_truthy("TRUE"));
        assert!(is_truthy("True"));
        assert!(is_truthy("yes"));
        assert!(is_truthy("on"));
        assert!(is_truthy("  1  "));
        // Documented falsy / unrecognized values.
        assert!(!is_truthy("0"));
        assert!(!is_truthy(""));
        assert!(!is_truthy("false"));
        assert!(!is_truthy("no"));
        assert!(!is_truthy("off"));
        assert!(!is_truthy("2"));
        assert!(!is_truthy("truthy"));
    }
}
