// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;
use crate::verify::{catch_ay_sort_panics, catch_ay_sort_panics_loop, is_ay_panic};

/// `catch_ay_sort_panics` catches ay Sort mismatch panics and returns Unknown.
///
/// This directly exercises the catch path for &str-payload panics matching
/// "Sort mismatch". Before this test, the catch path was only tested
/// indirectly through `verify_function` integration tests.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_sort_mismatch() {
    let result = catch_ay_sort_panics(|| {
        panic!("Sort mismatch: expected Int, got Bool");
    });
    let inner = result.expect("catch should return Ok, not encoding error");
    match &inner {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("Sort mismatch"),
                "Unknown reason must include the panic message, got: {reason}"
            );
        }
        other => panic!("expected Unknown(...), got: {other:?}"),
    }
}

/// `catch_ay_sort_panics` catches "expects Bool, got" panics (ay-dpll variant).
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_bool_expects_variant() {
    let result = catch_ay_sort_panics(|| {
        panic!("expects Bool, got Int in assert");
    });
    let inner = result.expect("catch should return Ok");
    assert!(
        matches!(inner, VerificationResult::Unknown(_)),
        "Bool-expects panic must be caught and surfaced as Unknown: got {inner:?}"
    );
}

/// `catch_ay_sort_panics` catches "BUG: mk_" panics (ay-dpll internal assertion).
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_bug_mk_variant() {
    let result = catch_ay_sort_panics(|| {
        panic!("BUG: mk_eq called with mismatched sorts");
    });
    let inner = result.expect("catch should return Ok");
    assert!(
        matches!(inner, VerificationResult::Unknown(_)),
        "BUG:mk_ panic must be caught: got {inner:?}"
    );
}

/// `catch_ay_sort_panics` catches model-validation panics and converts them to `Unknown` (#1256).
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_model_validation_panic() {
    let result = catch_ay_sort_panics(|| {
        panic!(
            "BUG: Model validation failed: Err(\"Assertion 5 violated: (not (= (logic_sum self) result_view)) evaluates to false\")"
        );
    });
    let inner = result.expect("catch should return Ok");
    let reason = match inner {
        VerificationResult::Unknown(reason) => reason,
        other => panic!("BUG: Model validation panic must be caught: got {other:?}"),
    };
    assert!(
        reason.as_str().contains("Model validation failed"),
        "panic reason should preserve model-validation context: {reason}"
    );
    assert!(
        reason.as_str().contains("Assertion 5 violated"),
        "panic reason should preserve assertion detail for diagnostics: {reason}"
    );
}

/// `is_ay_panic` classifies the SAT-model reverse-map consistency assertion.
///
/// This message shows up when ay constructs a term_to_var mapping that points
/// past the returned SAT model length. trust-wp must treat it as a ay panic so
/// the hard-timeout worker can downgrade the failure to Unknown instead of
/// unwinding past the verification boundary.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_classifies_term_to_var_model_size_mismatch() {
    assert!(
        is_ay_panic("term_to_var contains index 56 but model has only 53 vars"),
        "should classify the term_to_var/model-length mismatch as a ay panic"
    );
}

/// `catch_ay_sort_panics` converts the SAT-model reverse-map mismatch to `Unknown`.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_term_to_var_model_size_mismatch() {
    let result = catch_ay_sort_panics(|| {
        panic!("term_to_var contains index 56 but model has only 53 vars");
    });
    let inner = result.expect("catch should return Ok");
    assert!(
        matches!(inner, VerificationResult::Unknown(_)),
        "term_to_var/model-length mismatch must be downgraded to Unknown: {inner:?}"
    );
}

/// `catch_ay_sort_panics` passes through non-ay panics via `resume_unwind`.
///
/// This is the critical safety path: programmer errors (debug_assert, index OOB)
/// must NOT be silently converted to Unknown. Before this test, the
/// `resume_unwind` path was explicitly documented as untested.
#[test]
#[timeout(30000)]
#[should_panic(expected = "programmer error: index out of bounds")]
fn test_catch_ay_sort_panics_propagates_non_ay_panics() {
    let _ = catch_ay_sort_panics(|| {
        panic!("programmer error: index out of bounds");
    });
}

/// Non-string payloads are re-raised (they are not ay sort panics).
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_non_string_payload_propagates() {
    // Non-string payloads should propagate via `resume_unwind`.
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = catch_ay_sort_panics(|| {
            std::panic::panic_any(42i32);
        });
    }));
    let payload = caught.expect_err("non-string payload must be re-raised");
    assert!(
        payload.downcast_ref::<i32>().copied() == Some(42),
        "re-raised payload must preserve the original i32 value"
    );
}

/// `catch_ay_sort_panics` returns Ok for closures that succeed normally.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_passes_through_ok_result() {
    let result = catch_ay_sort_panics(|| Ok(VerificationResult::Verified(None)));
    let inner = result.expect("Ok should pass through");
    assert!(
        matches!(inner, VerificationResult::Verified(_)),
        "expected Verified pass-through, got: {inner:?}"
    );
}

/// `catch_ay_sort_panics` returns Ok for closures that return encoding errors.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_passes_through_encoding_error() {
    let result = catch_ay_sort_panics(|| Err(EncodingError::unsupported("test encoding error")));
    let err = result.expect_err("encoding errors should pass through as Err");
    assert!(
        err.to_string().contains("test encoding error"),
        "returned error should preserve original message: {err}"
    );
}

/// `catch_ay_sort_panics_loop` catches ay sort panics and returns all-Unknown.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_loop_catches_sort_mismatch() {
    let result = catch_ay_sort_panics_loop(|| {
        panic!("Sort mismatch: Int vs Seq");
    });
    let loop_result = result.expect("catch should return Ok");
    // All three sub-results must be Unknown with the panic reason
    assert!(
        matches!(&loop_result.initialization, VerificationResult::Unknown(r) if r.as_str().contains("Sort mismatch")),
        "initialization should be Unknown: got {:?}",
        loop_result.initialization
    );
    assert!(
        matches!(&loop_result.preservation, VerificationResult::Unknown(r) if r.as_str().contains("Sort mismatch")),
        "preservation should be Unknown: got {:?}",
        loop_result.preservation
    );
    assert!(
        matches!(&loop_result.postcondition, VerificationResult::Unknown(r) if r.as_str().contains("Sort mismatch")),
        "postcondition should be Unknown: got {:?}",
        loop_result.postcondition
    );
    // Variant fields should be None (not populated by panic handler)
    assert!(
        loop_result.variant_nonneg.is_none(),
        "variant_nonneg must be None after panic"
    );
    assert!(
        loop_result.variant_decrease.is_none(),
        "variant_decrease must be None after panic"
    );
}

/// `catch_ay_sort_panics_loop` propagates non-ay panics.
#[test]
#[timeout(30000)]
#[should_panic(expected = "assertion failed")]
fn test_catch_ay_sort_panics_loop_propagates_non_ay_panics() {
    let _ = catch_ay_sort_panics_loop(|| {
        panic!("assertion failed: unexpected state");
    });
}

/// `catch_ay_sort_panics` catches lowercase "sort mismatch" from ay's
/// `SolverError::SortMismatch` Display format (#885). Before this fix, only
/// uppercase "Sort mismatch" was caught, letting ay `datatype_selector` and
/// `try_datatype_selector` panics escape as unhandled panics.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_lowercase_sort_mismatch() {
    let result = catch_ay_sort_panics(|| {
        panic!(
            "sort mismatch in datatype_selector: expected expr sort matching selector's argument sort, got Int"
        );
    });
    let inner = result.expect("catch should return Ok, not encoding error");
    match &inner {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("sort mismatch"),
                "Unknown reason must include the panic message, got: {reason}"
            );
        }
        other => panic!("expected Unknown(...), got: {other:?}"),
    }
}

/// `catch_ay_sort_panics_loop` catches lowercase "sort mismatch" (#885).
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_loop_catches_lowercase_sort_mismatch() {
    let result = catch_ay_sort_panics_loop(|| {
        panic!("sort mismatch in datatype_selector: expected result sort, got Int");
    });
    let inner = result.expect("catch should return Ok");
    assert!(
        matches!(inner.initialization, VerificationResult::Unknown(_)),
        "Loop initialization must be Unknown on sort panic: got {:?}",
        inner.initialization
    );
}

/// `catch_ay_sort_panics_loop` catches "BUG: Model validation failed" (#1256).
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_loop_catches_model_validation_panic() {
    let result = catch_ay_sort_panics_loop(|| {
        panic!("BUG: Model validation failed: Err(\"Assertion violated\")");
    });
    let inner = result.expect("catch should return Ok");
    assert!(
        matches!(inner.initialization, VerificationResult::Unknown(_)),
        "Loop initialization must be Unknown on model validation panic: got {:?}",
        inner.initialization
    );
}

/// `is_ay_panic` matches "Sort mismatch" case-insensitively.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_sort_mismatch_uppercase() {
    assert!(
        is_ay_panic("Sort mismatch: expected Int, got Bool"),
        "should classify 'Sort mismatch' as ay panic"
    );
}

#[test]
#[timeout(30000)]
fn test_is_ay_panic_sort_mismatch_lowercase() {
    assert!(
        is_ay_panic("sort mismatch in eq_sort"),
        "should classify lowercase 'sort mismatch' as ay panic"
    );
}

/// `is_ay_panic` matches "expects Bool, got" (case-insensitive).
#[test]
#[timeout(30000)]
fn test_is_ay_panic_expects_bool_got() {
    assert!(
        is_ay_panic("expects Bool, got Int"),
        "should classify 'expects Bool, got Int' as ay panic"
    );
    // Case-insensitive: alternative casing also matches
    assert!(
        is_ay_panic("expects bool, got int"),
        "should classify lowercase 'expects bool, got int' as ay panic"
    );
    assert!(
        is_ay_panic("EXPECTS BOOL, GOT INT"),
        "should classify uppercase 'EXPECTS BOOL, GOT INT' as ay panic"
    );
}

/// `is_ay_panic` matches "BUG: " only at the start of the message (#1977).
///
/// The tightened filter requires "bug:" at position 0 (case-insensitive) to
/// prevent non-ay panics containing incidental "bug:" substrings from being
/// silently swallowed.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_bug_prefix_at_start() {
    assert!(
        is_ay_panic("BUG: mk_eq called with mismatched sorts"),
        "should classify 'BUG:' at start as ay panic"
    );
    assert!(
        is_ay_panic("BUG: Model validation failed: Err(\"Assertion violated\")"),
        "should classify 'BUG: Model validation failed' at start as ay panic"
    );
    // Case-insensitive: alternative casing at start also matches
    assert!(
        is_ay_panic("bug: mk_eq called with mismatched sorts"),
        "should classify lowercase 'bug:' at start as ay panic"
    );
    assert!(
        is_ay_panic("Bug: unexpected state"),
        "should classify mixed-case 'Bug:' at start as ay panic"
    );
}

/// `is_ay_panic` rejects "bug:" when it appears mid-message (#1977).
///
/// This is the core fix: messages like "known bug: ..." or "this is a bug: ..."
/// are NOT ay internal panics and must propagate as programmer errors.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_rejects_bug_mid_message() {
    assert!(
        !is_ay_panic("known bug: sort encoding fails"),
        "should NOT classify 'known bug:' as ay panic — mid-message"
    );
    assert!(
        !is_ay_panic("this is a bug: unexpected None"),
        "should NOT classify 'this is a bug:' as ay panic — mid-message"
    );
    assert!(
        !is_ay_panic("trust-wp hit a bug: missing spec"),
        "should NOT classify 'hit a bug:' as ay panic — mid-message"
    );
    assert!(
        !is_ay_panic("api wrapper panic: BUG: mk_eq called with non-matching sorts"),
        "should NOT classify wrapped 'BUG:' as ay panic — not at position 0"
    );
}

/// `catch_ay_sort_panics` propagates mid-message "bug:" panics (#1977).
#[test]
#[timeout(30000)]
#[should_panic(expected = "known bug: sort encoding")]
fn test_catch_ay_sort_panics_propagates_mid_message_bug() {
    let _ = catch_ay_sort_panics(|| {
        panic!("known bug: sort encoding fails");
    });
}

/// `is_ay_panic` matches ay-dpll theory conflict verification panics (#1272, case-insensitive).
#[test]
#[timeout(30000)]
fn test_is_ay_panic_theory_conflict_verification() {
    assert!(
        is_ay_panic("Theory conflict verification failed in extension.rs"),
        "should classify theory conflict in extension.rs as ay panic"
    );
    assert!(
        is_ay_panic("Theory conflict verification failed in lra.rs"),
        "should classify theory conflict in lra.rs as ay panic"
    );
    assert!(
        is_ay_panic("Theory conflict verification failed in lia.rs"),
        "should classify theory conflict in lia.rs as ay panic"
    );
    // Case-insensitive: alternative casing also matches
    assert!(
        is_ay_panic("theory conflict verification failed in lra.rs"),
        "should classify lowercase theory conflict as ay panic"
    );
}

/// `is_ay_panic` matches ay-dpll Farkas semantic verification panics (#1272, case-insensitive).
#[test]
#[timeout(30000)]
fn test_is_ay_panic_farkas_verification() {
    assert!(
        is_ay_panic("Farkas semantic verification failed in euf.rs"),
        "should classify Farkas verification in euf.rs as ay panic"
    );
    assert!(
        is_ay_panic("Farkas semantic verification failed in lra.rs"),
        "should classify Farkas verification in lra.rs as ay panic"
    );
    // Case-insensitive: alternative casing also matches
    assert!(
        is_ay_panic("farkas semantic verification failed in euf.rs"),
        "should classify lowercase Farkas verification as ay panic"
    );
}

/// `is_ay_panic` rejects unrelated panic messages.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_rejects_non_ay_panics() {
    assert!(
        !is_ay_panic("index out of bounds: the len is 5 but the index is 10"),
        "should NOT classify generic index-out-of-bounds as ay panic"
    );
    assert!(
        !is_ay_panic("called `Option::unwrap()` on a `None` value"),
        "should NOT classify Option::unwrap panic as ay panic"
    );
    assert!(
        !is_ay_panic("assertion failed: x > 0"),
        "should NOT classify generic assertion failure as ay panic"
    );
    assert!(
        !is_ay_panic("unknown panic"),
        "should NOT classify non-string panic payload as ay panic"
    );
}

// ── ay-prefetch panic classification tests (#2687, ay#8414) ────────────

/// `is_ay_panic` classifies ay-prefetch `val_at` panics as ay panics.
/// This is the actual panic observed in `inferred_invariants.rs` baseline:
/// `val_at: index 86 out of bounds for vals of length 22`
#[test]
#[timeout(30000)]
fn test_is_ay_panic_classifies_ay_prefetch_val_at() {
    assert!(
        is_ay_panic("val_at: index 86 out of bounds for vals of length 22"),
        "should classify ay-prefetch val_at panic as ay panic"
    );
}

/// `is_ay_panic` classifies other ay-prefetch function panics.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_classifies_ay_prefetch_variants() {
    assert!(
        is_ay_panic("set_val: index 50 out of bounds for vals of length 10"),
        "should classify ay-prefetch set_val panic"
    );
    assert!(
        is_ay_panic("neg_val_at: index 3 out of bounds for vals of length 2"),
        "should classify ay-prefetch neg_val_at panic"
    );
    assert!(
        is_ay_panic("assign_val: index 7 out of bounds for vals of length 4"),
        "should classify ay-prefetch assign_val panic"
    );
    assert!(
        is_ay_panic("decision_val: index 100 out of bounds for vals of length 50"),
        "should classify ay-prefetch decision_val panic"
    );
    assert!(
        is_ay_panic("word_at: index 5 out of bounds for words of length 3"),
        "should classify ay-prefetch word_at panic"
    );
    assert!(
        is_ay_panic("entry_at: index 12 out of bounds for entries of length 8"),
        "should classify ay-prefetch entry_at panic"
    );
    assert!(
        is_ay_panic("entry_set: index 9 out of bounds for entries of length 6"),
        "should classify ay-prefetch entry_set panic"
    );
}

/// `catch_ay_sort_panics` catches ay-prefetch panics and returns Unknown.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_ay_prefetch_val_at() {
    let result = catch_ay_sort_panics(|| {
        panic!("val_at: index 86 out of bounds for vals of length 22");
    });
    let inner = result.expect("catch should return Ok, not encoding error");
    match &inner {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("val_at"),
                "Unknown reason must include ay-prefetch function name, got: {reason}"
            );
        }
        other => panic!("expected Unknown(...) for ay-prefetch panic, got: {other:?}"),
    }
}

/// Generic "index out of bounds" NOT starting with a ay-prefetch prefix is
/// still rejected — only specific ay-prefetch function names are recognized.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_rejects_generic_out_of_bounds() {
    assert!(
        !is_ay_panic("index out of bounds: the len is 5 but the index is 10"),
        "generic Rust index-out-of-bounds must NOT be classified as ay panic"
    );
    assert!(
        !is_ay_panic("my_function: index 3 out of bounds for items of length 2"),
        "non-ay-prefetch function with out-of-bounds must NOT be ay panic"
    );
}

// ── ay-dpll deprecated datatype API panic classification (#2687) ───────
//
// The ay-dpll `datatype_constructor` / `datatype_selector` APIs are marked
// #[deprecated] in favor of the fallible variants, but trust-wp still calls
// them in several encoding paths. When invoked with a mismatched declared
// return sort (e.g., a constructor 'Cons' declared with return sort
// `Uninterpreted("Adt_Cons_Nil")` rather than a `Datatype` sort), the
// deprecated API formats the error as a panic with the message
// "invalid argument to datatype_constructor: ...". The upstream
// `ay_core::is_ay_panic_reason` classifier does not recognize this phrasing,
// so the panic escapes `catch_unwind` boundaries and aborts rustc. The
// trust-wp-side classifier must recognize it as a ay panic so graceful
// degradation to Unknown occurs at every call site.

/// `is_ay_panic` classifies the deprecated `datatype_constructor` panic.
/// Observed in `rusthorn/inc_some_*.rs` and `binary_search_list.rs` baseline.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_classifies_datatype_constructor_invalid_argument() {
    assert!(
        is_ay_panic(
            "invalid argument to datatype_constructor: constructor 'Cons' does not construct datatype 'List': declared return sort is Uninterpreted(\"Adt_Cons_Nil\")"
        ),
        "should classify ay-dpll deprecated datatype_constructor panic as ay panic"
    );
}

/// `is_ay_panic` classifies the deprecated `datatype_selector` panic.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_classifies_datatype_selector_invalid_argument() {
    assert!(
        is_ay_panic(
            "invalid argument to datatype_selector: selector 'head' does not extract from datatype 'List'"
        ),
        "should classify ay-dpll deprecated datatype_selector panic as ay panic"
    );
}

/// `is_ay_panic` classifies the SeqLIA "conflict semantic verification failed"
/// variant. ay_core recognizes "conflict verification failed" but the SeqLIA
/// theory inserts "semantic" between the tokens, causing the upstream filter
/// to miss it. Observed in `mapping_test.rs` baseline.
#[test]
#[timeout(30000)]
fn test_is_ay_panic_classifies_conflict_semantic_verification_failed() {
    assert!(
        is_ay_panic(
            "BUG(#6853): SeqLIA LIA conflict semantic verification failed: Conflict literals are satisfiable (not a real conflict)"
        ),
        "should classify ay-dpll SeqLIA conflict-semantic panic as ay panic"
    );
}

/// `catch_ay_sort_panics` converts the `datatype_constructor` panic to
/// `Unknown` rather than re-raising it. This is the graceful-degradation
/// path that prevents rustc from aborting on this class of panic.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_datatype_constructor_panic() {
    let result = catch_ay_sort_panics(|| {
        panic!(
            "invalid argument to datatype_constructor: constructor 'Cons' does not construct datatype 'List': declared return sort is Uninterpreted(\"Adt_Cons_Nil\")"
        );
    });
    let inner = result.expect("catch should return Ok, not encoding error");
    match &inner {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason
                    .as_str()
                    .contains("invalid argument to datatype_constructor"),
                "Unknown reason must preserve datatype_constructor panic message, got: {reason}"
            );
        }
        other => panic!("expected Unknown(...) for datatype_constructor panic, got: {other:?}"),
    }
}

/// `catch_ay_sort_panics` converts the SeqLIA semantic-conflict panic to
/// `Unknown` rather than re-raising it.
#[test]
#[timeout(30000)]
fn test_catch_ay_sort_panics_catches_conflict_semantic_panic() {
    let result = catch_ay_sort_panics(|| {
        panic!(
            "BUG(#6853): SeqLIA LIA conflict semantic verification failed: Conflict literals are satisfiable (not a real conflict)"
        );
    });
    let inner = result.expect("catch should return Ok, not encoding error");
    match &inner {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason
                    .as_str()
                    .contains("conflict semantic verification failed"),
                "Unknown reason must preserve SeqLIA conflict-semantic message, got: {reason}"
            );
        }
        other => panic!("expected Unknown(...) for SeqLIA conflict-semantic panic, got: {other:?}"),
    }
}
