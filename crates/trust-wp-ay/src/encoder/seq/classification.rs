// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq method classification — single source of truth.
//!
//! Pure predicates that classify whether a method name indicates Seq sort.
//! No state, no `AYEncoder` dependency. Used across the crate by sort
//! inference, prescan, and encoding dispatch.

/// Returns true if the method always produces a Seq-sorted result.
///
/// This is the authoritative list of methods that return `Seq`. Used by:
/// - `expr_produces_seq` (determines if an expression is Seq-sorted)
/// - `normalize_seq_receiver_for_scan` (determines if a receiver is already Seq)
/// - `infer_expr_sort` (determines sort for sort inference)
/// - `is_definitely_non_bool` (determines non-Bool sort)
///
/// Note: `set` is included here because `set(s, i, v)` always returns a Seq
/// when the receiver is Seq. Callers that need a receiver guard for `set`
/// (e.g., `infer_expr_sort` where `set` could also be an `FSet` method)
/// should check `method_produces_seq_unconditional` instead.
pub(crate) fn method_produces_seq(method: &str) -> bool {
    matches!(
        method,
        "push_back"
            | "push_back_ghost"
            | "push_front"
            | "push_front_ghost"
            | "pop_front"
            | "pop_front_ghost"
            | "pop_back"
            | "pop_back_ghost"
            | "tail"
            | "reverse"
            | "to_owned_seq"
            | "to_utf8"
            | "concat"
            | "subsequence"
            | "set"
    )
}

/// Like `method_produces_seq` but excludes `set`, which is ambiguous between
/// Seq and FSet contexts. Used by `infer_expr_sort` and `is_definitely_non_bool`
/// where `set` requires a separate receiver guard.
pub(crate) fn method_produces_seq_unconditional(method: &str) -> bool {
    method_produces_seq(method) && method != "set"
}

/// Returns true if the method unambiguously indicates a Seq receiver.
///
/// Superset of `method_produces_seq_unconditional`: includes methods like
/// `len_logic` that consume a Seq but don't return one.
/// Excludes `set` (ambiguous with FSet).
///
/// Note: `index_logic` is NOT included here — it is ambiguous between Seq
/// and FMap (the contract parser lowers `map[k]` to `index_logic(k)`).
/// Including it caused the prescan to tag bare Var receivers as Seq,
/// preventing FMap dispatch in `encode_method_call_impl`. (#967)
///
/// Note: `sum` is NOT included here — user-defined ADTs (e.g., List) can
/// define `sum` as a logic function. Including it causes the prescan to
/// unconditionally tag the receiver as Seq, which conflicts with the
/// Datatype domain sort of the registered logic function. (#1965, #2002)
///
/// Used by the sort hint prescan (`collect_all_sort_hints`) to identify
/// variables that should be declared with Seq sort.
pub(crate) fn is_seq_only_method(method: &str) -> bool {
    method_produces_seq_unconditional(method) || matches!(method, "len_logic")
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── method_produces_seq ──

    #[test]
    fn test_method_produces_seq_push_back_returns_true() {
        assert!(method_produces_seq("push_back"));
    }

    #[test]
    fn test_method_produces_seq_push_front_returns_true() {
        assert!(method_produces_seq("push_front"));
    }

    #[test]
    fn test_method_produces_seq_ghost_variants_return_true() {
        assert!(method_produces_seq("push_back_ghost"));
        assert!(method_produces_seq("push_front_ghost"));
        assert!(method_produces_seq("pop_front_ghost"));
        assert!(method_produces_seq("pop_back_ghost"));
    }

    #[test]
    fn test_method_produces_seq_pop_variants_return_true() {
        assert!(method_produces_seq("pop_front"));
        assert!(method_produces_seq("pop_back"));
    }

    #[test]
    fn test_method_produces_seq_tail_returns_true() {
        assert!(method_produces_seq("tail"));
    }

    #[test]
    fn test_method_produces_seq_reverse_returns_true() {
        assert!(method_produces_seq("reverse"));
    }

    #[test]
    fn test_method_produces_seq_to_owned_seq_returns_true() {
        assert!(method_produces_seq("to_owned_seq"));
    }

    #[test]
    fn test_method_produces_seq_concat_returns_true() {
        assert!(method_produces_seq("concat"));
    }

    #[test]
    fn test_method_produces_seq_subsequence_returns_true() {
        assert!(method_produces_seq("subsequence"));
    }

    #[test]
    fn test_method_produces_seq_set_returns_true() {
        // `set` produces Seq when the receiver is Seq
        assert!(method_produces_seq("set"));
    }

    #[test]
    fn test_method_produces_seq_non_seq_methods_return_false() {
        assert!(!method_produces_seq("len"));
        assert!(!method_produces_seq("len_logic"));
        assert!(!method_produces_seq("index_logic"));
        assert!(!method_produces_seq("get"));
        assert!(!method_produces_seq("contains"));
        assert!(!method_produces_seq("sum"));
        assert!(!method_produces_seq("deep_model"));
        assert!(!method_produces_seq(""));
    }

    // ── method_produces_seq_unconditional ──

    #[test]
    fn test_method_produces_seq_unconditional_excludes_set() {
        // `set` is ambiguous between Seq and FSet, so it is excluded
        assert!(!method_produces_seq_unconditional("set"));
    }

    #[test]
    fn test_method_produces_seq_unconditional_includes_non_set_seq_methods() {
        assert!(method_produces_seq_unconditional("push_back"));
        assert!(method_produces_seq_unconditional("tail"));
        assert!(method_produces_seq_unconditional("reverse"));
        assert!(method_produces_seq_unconditional("concat"));
        assert!(method_produces_seq_unconditional("subsequence"));
        assert!(method_produces_seq_unconditional("to_utf8"));
    }

    #[test]
    fn test_method_produces_seq_unconditional_non_seq_returns_false() {
        assert!(!method_produces_seq_unconditional("len"));
        assert!(!method_produces_seq_unconditional("index_logic"));
    }

    #[test]
    fn test_method_produces_seq_into_seq_returns_false() {
        assert!(!method_produces_seq("into_seq"));
    }

    // ── is_seq_only_method ──

    #[test]
    fn test_is_seq_only_method_includes_len_logic() {
        // len_logic consumes a Seq but does not return one
        assert!(is_seq_only_method("len_logic"));
    }

    #[test]
    fn test_is_seq_only_method_includes_unconditional_seq_producers() {
        assert!(is_seq_only_method("push_back"));
        assert!(is_seq_only_method("reverse"));
        assert!(is_seq_only_method("concat"));
    }

    #[test]
    fn test_is_seq_only_method_excludes_set() {
        // `set` is ambiguous between Seq and FSet contexts
        assert!(!is_seq_only_method("set"));
    }

    #[test]
    fn test_is_seq_only_method_excludes_index_logic() {
        // index_logic is ambiguous between Seq and FMap (#967)
        assert!(!is_seq_only_method("index_logic"));
    }

    #[test]
    fn test_is_seq_only_method_excludes_sum() {
        // sum can be a user-defined logic function on ADTs (#1965, #2002)
        assert!(!is_seq_only_method("sum"));
    }

    #[test]
    fn test_is_seq_only_method_excludes_arbitrary_names() {
        assert!(!is_seq_only_method("foo"));
        assert!(!is_seq_only_method("bar_baz"));
        assert!(!is_seq_only_method(""));
    }
}
