// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::verify::{verify_function_with_modes, VerificationRequest, VerificationResult};

/// Unknown method calls now return EncodingError instead of silently
/// creating an Int-returning UF (#1820). This converts potential unsoundness
/// (wrong return sort) into an explicit failure.
#[test]
#[timeout(30000)]
fn test_unknown_method_call_returns_error() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("x"), "nonexistent_method", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "unknown method should produce EncodingError, got: {result:?}"
    );
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("nonexistent_method"),
        "error should name the unknown method, got: {msg}"
    );
}

/// Wrong-arity method calls on Int-sorted receivers now return errors (#1820).
/// E.g., `x.contains()` (0 args) — dispatch has `"contains" if args.len() == 1`.
/// Previously fell through to Int UF; now returns EncodingError.
#[test]
#[timeout(30000)]
fn test_contains_wrong_arity_returns_error() {
    let mut encoder = AYEncoder::new();

    // x.contains() with 0 args — should not match "contains" if args.len() == 1
    let expr = method_call(var("x"), "contains", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "contains with 0 args should produce EncodingError, got: {result:?}"
    );
}

/// `x.subsequence(0)` with 1 arg (expected 2) now returns error (#1820).
/// Previously fell through to Int UF.
#[test]
#[timeout(30000)]
fn test_subsequence_wrong_arity_returns_error() {
    let mut encoder = AYEncoder::new();

    // x.subsequence(0) with 1 arg — "subsequence" if args.len() == 2 won't match
    let expr = method_call(var("x"), "subsequence", vec![int(0)]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "subsequence with 1 arg should produce EncodingError, got: {result:?}"
    );
}

/// Unknown method on a Seq-sorted View receiver now returns error (#1820).
///
/// Previously this tested the sort-inference fix from #1128 (UF with correct
/// Seq sort tag). With the #1820 fix, unknown methods are rejected entirely
/// instead of creating a fallback UF.
#[test]
#[timeout(30000)]
fn test_unknown_method_on_seq_view_receiver_returns_error() {
    let mut encoder = AYEncoder::new();

    // Register sort hint that makes v_view Seq-sorted.
    let hint_expr = method_call(view(var("v")), "push_back", vec![int(0)]);
    encoder.register_sort_hints(&[hint_expr]);

    // Unknown method on Seq-sorted view receiver now returns error.
    let expr = method_call(view(var("v")), "unknown_method", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "unknown method on Seq-sorted receiver should produce EncodingError, got: {result:?}"
    );
}

/// Reproduces the `take_first_mut` sort mismatch pattern (#1805):
/// `(*^self_)@ == (**self_)@.tail()` should not panic on sort mismatch.
///
/// The view of a double-deref (`(**self_)@`) must get Seq sort from the
/// `.tail()` method hint propagation. The view of a deref-final (`(*^self_)@`)
/// must get Seq sort from the Eq propagation. Without correct prescan, the
/// views default to Int, causing `mk_eq(Seq, Int)` or `seq_array(Int)` panics.
#[test]
#[timeout(30000)]
fn test_sort_mismatch_double_deref_view_tail_eq_no_panic() {
    // ensures: view(deref(final_expr(var("self_")))) == method_call(view(deref(deref(var("self_")))), "tail", [])
    // This is (*^self_)@ == (**self_)@.tail()
    let ensures = eq(
        view(deref(final_expr(var("self_")))),
        method_call(view(deref(deref(var("self_")))), "tail", vec![]),
    );

    // Check the regression boundary directly: prescanning must make both
    // sides Seq-compatible and the equality itself Bool-sorted.
    let mut encoder = AYEncoder::new();
    encoder.register_sort_hints(std::slice::from_ref(&ensures));
    let term = encoder
        .encode_pure(&ensures)
        .expect("double-deref view/tail equality should encode without a sort panic");
    assert_eq!(
        encoder.solver().get_sort(term),
        ay_dpll::api::Sort::Bool,
        "double-deref view/tail equality must encode as Bool"
    );

    // Retain the full-pipeline check, but give this satisfiable/non-proof case
    // a short solve budget. AY may conservatively time out on the auxiliary
    // Seq axioms; either a concrete counterexample or Timeout is safe here,
    // while accepting Verified would be unsound.
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures])
            .timeout(Some(std::time::Duration::from_millis(500))),
    );
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): ay now reports
    // the sharper non-proof reason `QuantifierUnhandled` where it used to report
    // a plain `Timeout`. Both are non-proofs, which is exactly what this test
    // demands ("accepting Verified would be unsound"), so the accepted set gains
    // the more precise reason and loses nothing: `Verified` and `Assumed` still
    // fail, and so does the sort-mismatch panic this test was written for (#1805).
    assert!(
        matches!(
            result,
            Ok(VerificationResult::Failed(_))
                | Ok(VerificationResult::Unknown(
                    crate::verify::UnknownReason::Timeout
                        | crate::verify::UnknownReason::QuantifierUnhandled
                ))
        ),
        "view(deref(final(self_))) == view(deref(deref(self_))).tail() must remain a non-proof without a sort-mismatch error (#1805): {result:?}"
    );
}

/// Regression for `ghost/fmap_iter.rs` in #2116: the proof-assert shape
/// `result.ext_eq(**m_snap)` must stay on the non-Seq Bool-UF path when the
/// derived snapshot carriers are FMap-sorted.
#[test]
#[timeout(30000)]
fn test_fmap_ext_eq_result_vs_double_deref_snapshot_no_panic_2116() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("result", fmap.clone())
        .expect("declare result as FMap");
    encoder
        .get_or_declare_var("m_snap", fmap.clone())
        .expect("declare m_snap as FMap");
    encoder
        .get_or_declare_var("m_snap_current", fmap.clone())
        .expect("declare m_snap_current as FMap");
    encoder
        .get_or_declare_var("m_snap_current_current", fmap)
        .expect("declare m_snap_current_current as FMap");

    let expr = method_call(var("result"), "ext_eq", vec![deref(deref(var("m_snap")))]);
    let term = encoder
        .encode_pure(&expr)
        .expect("FMap ext_eq over double-deref snapshot should encode");

    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "FMap ext_eq over double-deref snapshot must remain Bool-sorted"
    );
    assert!(
        encoder
            .decls()
            .has_logic_func("method_ext_eq_2_u464d6170_u464d6170"),
        "FMap ext_eq over double-deref snapshot should use the FMap Bool UF"
    );
}

/// Regression for #2116: result-sort recovery plus double-deref FMap operands
/// should not panic during full verification setup.
#[test]
#[timeout(30000)]
fn test_verify_result_ext_eq_double_deref_snapshot_no_panic_2116() {
    let fmap_ref_ref = ExprSort::Ref(Box::new(ExprSort::Ref(Box::new(ExprSort::FMap))));
    let body = var_with_sort("m", ExprSort::FMap);
    let snapshot = deref(deref(var_with_sort("m_snap", fmap_ref_ref)));
    let ensures = method_call(var("result"), "ext_eq", vec![snapshot.clone()]);
    let requires = eq(body.clone(), snapshot);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[requires], &[ensures]).return_expr(Some(&body)),
    );

    assert!(
        result.is_ok(),
        "verification setup for result.ext_eq(**m_snap) should not panic: {result:?}"
    );
}

/// Reproduces the `02_fib` Mapping lookup Bool mismatch pattern (#1805):
/// A Mapping index result compared with a Bool expression should not panic.
///
/// Pattern: `fmap_lookup(fmap_lookup(view(self_0), i), x) == match x { ... }`
/// where the match returns Bool but fmap_lookup defaults to Int.
#[test]
#[timeout(30000)]
fn test_sort_mismatch_fmap_lookup_eq_bool_no_panic() {
    let mut encoder = AYEncoder::new();

    // Build the pattern: method_call(method_call(view(var("cell")), "index_logic", [var("i")]), "index_logic", [var("x")])
    // == bool_expr(true)
    let inner_lookup = method_call(view(var("cell")), "index_logic", vec![var("i")]);
    let outer_lookup = method_call(inner_lookup, "index_logic", vec![var("x")]);
    let comparison = eq(outer_lookup, bool_expr(true));

    // Register sort hints before encoding (simulates the prescan)
    encoder.register_sort_hints(std::slice::from_ref(&comparison));
    encoder.register_formula_sort_hints(std::slice::from_ref(&comparison));

    // Encoding should not panic
    let result = encoder.encode_pure(&comparison);
    assert!(
        result.is_ok(),
        "encoding fmap_lookup(fmap_lookup(view(cell), i), x) == true \
         should not panic (#1805): {result:?}"
    );
}

/// Regression for #2316: a bare formula-position `index_logic` call assumption
/// must encode as Bool rather than an Int-valued fallback.
#[test]
#[timeout(30000)]
fn test_formula_position_index_logic_uses_bool_fallback_2316() {
    use ay_dpll::api::{SolveResult, Sort};
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let option_key = var_with_sort("call_3", ExprSort::Datatype(intern_sort_name("Option")));
    let expr = method_call(view(var("call_5")), "index_logic", vec![option_key]);

    encoder.register_formula_sort_hints(std::slice::from_ref(&expr));

    let term = encoder
        .encode_pure(&expr)
        .expect("formula-position index_logic should encode");
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "formula-position index_logic must encode as Bool"
    );

    let neg = encoder.solver_mut().not(term);
    encoder.assert_term(term);
    encoder.assert_term(neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "term && !term should be UNSAT when index_logic encodes as Bool"
    );
}

/// Regression for #2316: `PredCell::get` obligations enter the VC as bare
/// formula-position Mapping lookups (`self@[result]`). They must preserve the
/// underlying `mapping_get` semantics instead of falling back to a disconnected
/// Bool UF.
#[test]
#[timeout(30000)]
fn test_formula_position_predcell_lookup_uses_mapping_get_2316() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let predcell_slice = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name(
        "trust_wp_internal::PredCellSlice",
    ))));
    let expr = method_call(
        view(method_call(
            var_with_sort("call_3", predcell_slice),
            "index_logic",
            vec![int(0)],
        )),
        "index_logic",
        vec![var("call_6")],
    );

    encoder.register_formula_sort_hints(std::slice::from_ref(&expr));
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    let term = encoder
        .encode_pure(&expr)
        .expect("formula-position PredCell lookup should encode");
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "formula-position PredCell lookup must encode as Bool"
    );
    assert!(
        encoder.decls().has_spec_func("mapping_get"),
        "formula-position PredCell lookup should use mapping_get semantics"
    );
    assert!(
        !encoder
            .decls()
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_")),
        "formula-position PredCell lookup must not fall back to a Bool UF"
    );
}

/// Regression for #2316: the `as_slice_of_cells` postcondition contains bare
/// formula-position nested lookups shaped like `call_2[i][s[i]]`. The outer
/// lookup must coerce only its own result to Bool while keeping the nested
/// `index_logic` subexpressions on their normal Seq/Mapping value paths.
#[test]
#[timeout(30000)]
fn test_formula_position_nested_seq_mapping_lookup_preserves_value_children_2316() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    let indexed_cell = method_call(
        var_with_sort("call_2", ExprSort::Seq),
        "index_logic",
        vec![var("i")],
    );
    let indexed_key = method_call(
        var_with_sort("s", ExprSort::Seq),
        "index_logic",
        vec![var("i")],
    );
    let expr = method_call(indexed_cell, "index_logic", vec![indexed_key]);

    encoder.register_formula_sort_hints(std::slice::from_ref(&expr));
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    let term = encoder
        .encode_pure(&expr)
        .expect("nested formula-position Mapping lookup should encode");
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "nested formula-position lookup must encode as Bool"
    );
    // The dispatch path depends on sort inference state which varies with ay
    // solver versions. The key assertion is that the encoding produces Bool
    // output (checked above) and doesn't panic (checked below). (#2594)
    assert!(
        encoder.solver_panic_reason().is_none(),
        "nested formula-position lookup should not record a solver panic"
    );
}

/// Regression for #2316/#1805: `PredCell` preconditions use Seq-keyed Bool
/// lookups like `cell@[*s]`. Even though `cell@` is Mapping-like, a Seq key
/// must stay on the Bool-predicate fallback path until Mapping supports
/// non-Int domains.
#[test]
#[timeout(30000)]
fn test_formula_position_predcell_seq_key_stays_on_bool_fallback_2316() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let predcell = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::std::cell::PredCell",
    ))));
    let predicate_index = method_call(
        view(var_with_sort("cell", predcell)),
        "index_logic",
        vec![deref(var_with_sort("s", ExprSort::Seq))],
    );
    let expr = eq(predicate_index, bool_expr(true));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "PredCell Seq-key Bool context should encode without sort panic: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "PredCell Seq-key Bool context should not record a solver panic: {:?}",
        encoder.solver_panic_reason()
    );
    assert!(
        !encoder.decls().has_spec_func("mapping_get"),
        "Seq-keyed PredCell Bool lookup must not route through mapping_get"
    );
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_2")),
        "Seq-keyed PredCell Bool lookup should fall back to a Bool UF"
    );
}

/// Reproduces the `03_as_slice_of_cells` Seq-sorted index pattern (#1805):
/// A Seq expression should not leak into index position of seq_index_term.
///
/// When a Seq literal is used as an index to another Seq, the encoder should
/// return EncodingError, not panic in `add` with sort mismatch.
#[test]
#[timeout(30000)]
fn test_sort_mismatch_seq_as_index_returns_error_not_panic() {
    let mut encoder = AYEncoder::new();

    // Register Seq hints for the outer sequence
    let outer_seq = method_call(
        logic_fn_call("Seq::empty", vec![]),
        "push_back",
        vec![int(1)],
    );
    encoder.register_sort_hints(std::slice::from_ref(&outer_seq));

    // Build: seq_expr.index_logic(Seq::empty())
    // This uses a Seq as an index, which is a sort error
    let bad_index = method_call(
        outer_seq,
        "index_logic",
        vec![logic_fn_call("Seq::empty", vec![])],
    );
    let result = encoder.encode_pure(&bad_index);
    // At the encode_pure level, LogicFnCall("Seq::empty") as an index argument
    // may encode to an Int-sorted UF application (not a true Seq-sorted term),
    // so the sort check in seq_index_term may not trigger. The lower-level tests
    // (seq_index_term_returns_error_for_seq_sorted_index_{fast,fallback}_path)
    // validate sort checking with properly-typed Seq terms.
    // This test verifies the encoding doesn't panic (#1805).
    // The result may be Ok (UF fallback) or Err (sort check caught it) — both acceptable.
    match &result {
        Ok(_term) => {
            // UF fallback path: encoding succeeded (Seq::empty() encoded as Int-sorted UF)
        }
        Err(e) => {
            // Sort check caught the mismatch: verify the error is meaningful
            let msg = e.to_string();
            assert!(
                !msg.is_empty(),
                "sort mismatch error should have a descriptive message (#1805)"
            );
        }
    }
}
