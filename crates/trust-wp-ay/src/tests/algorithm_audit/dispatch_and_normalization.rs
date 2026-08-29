// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Method dispatch wildcard fallback, sort-tag collision, structural equality,
//! duplicate binder handling, mut-ref canonicalization, and `normalize_deref_final`
//! coverage (#901, #1603, #1802, #1820).

use std::sync::Arc;

use ntest::timeout;

use super::super::helpers::{and, int, method_call, var};
use crate::{AYEncoder, ExprSort, PureExpr};

// =============================================================================
// Method dispatch algorithm audit: wildcard fallback rejects unknown methods (#901, #1820)
// =============================================================================
//
// The wildcard `_` arm in `encode_method_call_impl` now returns an
// `EncodingError::Unsupported` for methods that are neither in the dispatch
// table nor registered as logic functions. Previously it silently created an
// Int-returning UF, which was unsound for Bool/struct-returning methods.

/// Unknown method call on receiver returns an encoding error (#1820).
///
/// Previously this fell through to an Int UF. Now it produces
/// `EncodingError::Unsupported` with a diagnostic message.
#[test]
#[timeout(30000)]
fn wildcard_method_fallback_returns_error() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("x"), "my_unknown_method", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "unknown method should produce EncodingError, got: {result:?}"
    );
    let err = result.unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("my_unknown_method"),
        "error message should name the unknown method, got: {msg}"
    );
}

/// Unknown method in a Bool context: `seed_bool_context_hints` (0c84153f)
/// marks the method call with `ExprSort::Bool`, allowing the wildcard UF
/// path to declare a Bool-returning function. The `And` operator then
/// receives Bool operands and encoding succeeds.
///
/// Previously (#1820) this triggered a ay sort panic because the
/// Int-returning UF was passed to `solver.and()` which expects Bool.
/// Before that fix, it returned EncodingError from method dispatch.
#[test]
#[timeout(30000)]
fn wildcard_method_in_bool_context_encodes_with_bool_hint() {
    let mut encoder = AYEncoder::new();
    // user_pred(x) && true — user_pred gets Bool hint from seed_bool_context_hints
    let pred_call = method_call(var("x"), "user_pred", vec![]);
    let expr = and(pred_call, PureExpr::Bool(true));
    let result = encoder.encode_pure(&expr);
    // seed_bool_context_hints (0c84153f) pre-seeds Bool sort for methods in
    // Bool contexts. The wildcard UF path declares a Bool-returning function,
    // so And(user_pred(x), true) encodes successfully.
    assert!(
        result.is_ok(),
        "unknown method in Bool context should encode with Bool hint, got: {result:?}"
    );
}

// =============================================================================
// Method dispatch: `len_logic` missing is_seq_receiver guard (#901)
// =============================================================================
//
// The `len_logic` arm at method_call/mod.rs unconditionally routes to
// encode_seq_operation_impl, unlike `len` which checks is_seq_receiver.
// A non-Seq receiver calling .len_logic() would be misrouted.

/// `len_logic` on an Int-sorted variable routes through Seq encoder.
///
/// Documents the missing is_seq_receiver guard: len_logic(x) for an
/// Int variable x will be treated as seq_len(x) and may incorrectly
/// record a Seq sort hint for x.
#[test]
#[timeout(30000)]
fn len_logic_on_non_seq_receiver_routes_through_seq_encoder() {
    let mut encoder = AYEncoder::new();
    // Predeclare x as Int to make it definitively non-Seq
    encoder
        .get_or_declare_var("x", ay_dpll::api::Sort::Int)
        .expect("declare x:Int");
    let expr = method_call(var("x"), "len_logic", vec![]);
    let result = encoder.encode_pure(&expr);
    // Current behavior: this succeeds but treats x as a Seq receiver
    // via normalize_seq_receiver, which wraps it in View(Var("x")).
    // This is a misrouting bug — len_logic lacks the is_seq_receiver
    // guard that len has. Pinning current Ok behavior so any change
    // (fix or regression) is detected. (#901)
    assert!(
        result.is_ok(),
        "len_logic on non-Seq currently succeeds via misrouting: {result:?}"
    );
}

/// Contrast: `len` correctly dispatches non-Seq to FMap encoder.
///
/// This is the reference behavior that `len_logic` should match.
#[test]
#[timeout(30000)]
fn len_on_non_seq_receiver_dispatches_to_fmap() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("x", ay_dpll::api::Sort::Int)
        .expect("declare x:Int");
    let expr = method_call(var("x"), "len", vec![]);
    let result = encoder.encode_pure(&expr);
    // `len` checks is_seq_receiver(x) → false → encode_fmap_method
    assert!(
        result.is_ok(),
        "len on non-Seq should encode via FMap: {result:?}"
    );
}

// =============================================================================
// Arity-guarded methods: wrong-arity now returns error (#901, #1820)
// =============================================================================
//
// Methods like `contains`, `remove`, `intersection` have arity guards
// (e.g., `if args.len() == 1`). When the guard fails, the call falls
// through to the wildcard `_` arm which now returns EncodingError
// instead of silently creating an Int UF.

/// `contains` with wrong arity (0 args) returns EncodingError (#1820).
///
/// Previously fell through to Int UF. Now the wildcard rejects it.
#[test]
#[timeout(30000)]
fn contains_zero_args_returns_error() {
    let mut encoder = AYEncoder::new();
    // contains() with 0 args — arity guard `args.len() == 1` fails
    let expr = method_call(var("x"), "contains", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "contains with 0 args should produce EncodingError, got: {result:?}"
    );
}

// =============================================================================
// method_sort_tag: uninterpreted sort collision (#901)
// =============================================================================
//
// method_sort_tag maps ALL non-Bool/non-Int sorts to "u". Two methods
// with different uninterpreted-sort receivers get the same SMT symbol.

/// Sort tag produces distinct UF names for Int vs Bool receivers.
///
/// Uses `deep_model` (a known Int-returning method in the dispatch table)
/// to test sort tag differentiation. After #1820, unknown methods return
/// errors, so we use a known method instead.
#[test]
#[timeout(30000)]
fn method_sort_tag_distinguishes_int_and_bool_receivers() {
    let mut encoder = AYEncoder::new();

    // First receiver: Int-sorted variable -> sort tag "i"
    encoder
        .get_or_declare_var("a", ay_dpll::api::Sort::Int)
        .expect("declare a:Int");
    let expr_a = method_call(var("a"), "deep_model", vec![]);
    encoder
        .encode_pure(&expr_a)
        .expect("encode deep_model on Int receiver");

    // Second receiver: Bool-sorted variable -> sort tag "b"
    encoder
        .get_or_declare_var("b", ay_dpll::api::Sort::Bool)
        .expect("declare b:Bool");
    let expr_b = method_call(var("b"), "deep_model", vec![]);
    encoder
        .encode_pure(&expr_b)
        .expect("encode deep_model on Bool receiver");

    // Int and Bool receivers should produce DIFFERENT UF names
    let key_int = "method_deep_model_1_i";
    let key_bool = "method_deep_model_1_b";
    assert!(
        encoder.decls().has_logic_func(key_int),
        "Int receiver should produce '{key_int}'"
    );
    assert!(
        encoder.decls().has_logic_func(key_bool),
        "Bool receiver should produce '{key_bool}'"
    );
}

// =============================================================================
// Algorithm audit: eager_instantiation boundary conditions (#1603)
// =============================================================================
//
// Findings from Prover algorithm_audit phase targeting eager_instantiation,
// mut_borrow, and canonicalize_mut_ref_vars modules.

/// PureExpr PartialEq DOES distinguish sort annotations on Var nodes.
/// This tests the derived PartialEq, NOT `exprs_structurally_equal`.
///
/// Note: `exprs_structurally_equal` IGNORES sort annotations for Var
/// nodes (matching by name only). See `exprs_structurally_equal_ignores_sort`
/// below for the direct function test. (#1267)
#[test]
#[timeout(30000)]
fn pure_expr_partial_eq_sort_annotation_sensitivity() {
    let var_no_sort = var("x");
    let var_int_sort = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let var_bool_sort = PureExpr::Var("x".to_string(), Some(ExprSort::Bool));

    // PartialEq: same name, different sort annotations are NOT equal
    assert_ne!(
        var_no_sort, var_int_sort,
        "PartialEq: Var(x, None) != Var(x, Some(Int))"
    );
    assert_ne!(
        var_no_sort, var_bool_sort,
        "PartialEq: Var(x, None) != Var(x, Some(Bool))"
    );
    assert_ne!(
        var_int_sort, var_bool_sort,
        "PartialEq: Var(x, Some(Int)) != Var(x, Some(Bool))"
    );

    // PartialEq: same name and same sort annotation ARE equal
    assert_eq!(
        var_no_sort,
        var("x"),
        "PartialEq: Var(x, None) == Var(x, None)"
    );
}

/// `exprs_structurally_equal` IGNORES sort annotations on Var nodes,
/// matching by name only. This prevents missed witness bindings when
/// ExprSort enrichment produces richer annotations on one side.
///
/// Directly calls the function (not PartialEq). Addresses #1267 AC1.
#[test]
#[timeout(30000)]
fn exprs_structurally_equal_ignores_sort() {
    use crate::verify::exprs_structurally_equal;

    let var_no_sort = var("x");
    let var_int_sort = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let var_bool_sort = PureExpr::Var("x".to_string(), Some(ExprSort::Bool));

    // exprs_structurally_equal matches Var by name only
    assert!(
        exprs_structurally_equal(&var_no_sort, &var_int_sort),
        "exprs_structurally_equal: Var(x, None) matches Var(x, Some(Int))"
    );
    assert!(
        exprs_structurally_equal(&var_no_sort, &var_bool_sort),
        "exprs_structurally_equal: Var(x, None) matches Var(x, Some(Bool))"
    );
    assert!(
        exprs_structurally_equal(&var_int_sort, &var_bool_sort),
        "exprs_structurally_equal: Var(x, Some(Int)) matches Var(x, Some(Bool))"
    );

    // Different names do NOT match
    assert!(
        !exprs_structurally_equal(&var("x"), &var("y")),
        "exprs_structurally_equal: Var(x) != Var(y)"
    );

    // Non-Var expressions fall through to PartialEq
    assert!(
        exprs_structurally_equal(&int(42), &int(42)),
        "exprs_structurally_equal: Int(42) == Int(42)"
    );
    assert!(
        !exprs_structurally_equal(&int(42), &int(43)),
        "exprs_structurally_equal: Int(42) != Int(43)"
    );
}

/// `try_match_expr` for free variables (line 969-976) compares by name only,
/// ignoring sort annotations. This is correct: `matches!(ground, Var(gn, _) if gn == name)`.
/// Verify that a free variable with sort annotation still matches a ground variable
/// without sort annotation (and vice versa).
#[test]
#[timeout(30000)]
fn eager_instantiation_free_var_match_ignores_sort_annotation() {
    use crate::verify::assert_eager_negated_existential_instantiations;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Requires: postcondition_mut(f, result) where f has no sort annotation
    let requires = vec![method_call(
        var("f"),
        "postcondition_mut",
        vec![var("result")],
    )];
    for req in &requires {
        let t = encoder.encode_pure(req).unwrap();
        encoder.assert_term(t);
    }

    // Ensures: exists<st> postcondition_mut(st, result) — st is bound, f is free in requires
    // The body uses Var("result", None) and the ground term uses Var("result", None) — match.
    let body = method_call(var("st"), "postcondition_mut", vec![var("result")]);
    let ensures = vec![PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(body),
        triggers: vec![],
    }];

    let result =
        assert_eager_negated_existential_instantiations(&mut encoder, &ensures, &requires, &[]);
    assert!(
        result.is_ok(),
        "free variable match should succeed regardless of sort annotation: {result:?}"
    );
}

/// `flatten_nested_existentials` with duplicate bound variable names.
///
/// `exists<x> exists<x> body` produces `bound_vars = ["x", "x"]` with
/// `bound_vars.len() = 2`. The witness binding HashMap can only contain
/// one entry for "x", so `binding.len() < bound_vars.len()` is always true,
/// causing eager instantiation to silently skip (incomplete binding).
///
/// This documents the behavior: duplicate bound variables are not rejected
/// at the flatten stage, and the completeness check at try_eager_instantiate_one
/// line 103 acts as a conservative guard that prevents unsound instantiation.
#[test]
#[timeout(30000)]
fn flatten_nested_existentials_duplicate_bound_vars() {
    use crate::verify::flatten_nested_existentials;

    // exists<x> exists<x> x (shadowing — semantically the inner x)
    let inner = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![],
    };
    let outer = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(inner),
        triggers: vec![],
    };

    let result = flatten_nested_existentials(&outer);
    assert!(result.is_some(), "duplicate vars should still produce Some");
    let (vars, _body) = result.unwrap();
    assert_eq!(vars, vec!["x".to_string(), "x".to_string()]);
    // The HashMap-based binding will have at most 1 entry for "x",
    // but bound_vars.len() is 2, so the completeness check fails.
    // This is conservative (sound) — the instantiation is skipped.
}

/// `flatten_nested_existentials` with duplicate vars causes eager instantiation
/// to skip (binding.len() < bound_vars.len()), so the solver remains SAT.
///
/// This exercises the full pipeline to confirm the conservative guard works.
#[test]
#[timeout(30000)]
fn eager_instantiation_skips_with_duplicate_bound_vars() {
    use ay_dpll::api::SolveResult;

    use crate::verify::assert_eager_negated_existential_instantiations;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Requires: postcondition_mut(f, result)
    let requires = vec![method_call(
        var("f"),
        "postcondition_mut",
        vec![var("result")],
    )];
    for req in &requires {
        let t = encoder.encode_pure(req).unwrap();
        encoder.assert_term(t);
    }

    // Ensures: exists<st> exists<st> postcondition_mut(st, result)
    // Duplicate bound var "st" — binding can only hold 1 entry, but
    // bound_vars.len() is 2, so instantiation is skipped.
    let body = method_call(var("st"), "postcondition_mut", vec![var("result")]);
    let inner = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(body),
        triggers: vec![],
    };
    let ensures = vec![PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(inner),
        triggers: vec![],
    }];

    let result =
        assert_eager_negated_existential_instantiations(&mut encoder, &ensures, &requires, &[]);
    assert!(result.is_ok(), "should not error: {result:?}");

    // Because instantiation was skipped (incomplete binding), the solver
    // remains SAT — no ground contradiction was asserted.
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "duplicate bound vars cause incomplete binding → instantiation skipped → SAT"
    );
}

/// `canonicalize_mut_ref_vars` does NOT recurse into Deref/Final children.
///
/// This is by design (prevents double-wrapping for `Deref(Var("x"))`) but
/// means complex expressions inside Deref are not canonicalized.
/// `Deref(BinOp(Var("x"), Add, Int(1)))` where "x" is a mut-ref param
/// will NOT have the inner `Var("x")` wrapped in Deref.
///
/// This documents the boundary: only bare `Var("x")` at the top level
/// is canonicalized. Variables buried inside Deref/Final are left as-is.
#[test]
#[timeout(30000)]
fn canonicalize_mut_ref_vars_does_not_recurse_into_deref() {
    use std::collections::HashSet;

    use trust_wp_core::formula::BinOp;

    use crate::verify::mut_borrow::helpers::canonicalize_mut_ref_vars;

    let mut params = HashSet::new();
    params.insert("x");

    // Case 1: Deref(Var("x")) — already canonical, no change expected
    let input = PureExpr::Deref(Arc::new(var("x")));
    let output = canonicalize_mut_ref_vars(&input, &params);
    assert_eq!(
        output, input,
        "Deref(Var(x)) should be unchanged (already canonical)"
    );

    // Case 2: Deref(BinOp(Var("x"), Add, Int(1))) — inner Var("x") is NOT wrapped
    let inner_binop = PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(int(1)));
    let input = PureExpr::Deref(Arc::new(inner_binop.clone()));
    let output = canonicalize_mut_ref_vars(&input, &params);
    // The non-recursion means the inner Var("x") stays as Var("x"),
    // NOT as Deref(Var("x")).
    assert_eq!(
        output,
        PureExpr::Deref(Arc::new(inner_binop)),
        "Deref(BinOp(Var(x), +, 1)) should be unchanged — no recursion into Deref children"
    );

    // Case 3: Contrast — bare BinOp(Var("x"), Add, Int(1)) IS canonicalized
    let bare_binop = PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(int(1)));
    let output = canonicalize_mut_ref_vars(&bare_binop, &params);
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Add,
        Arc::new(int(1)),
    );
    assert_eq!(
        output, expected,
        "bare BinOp(Var(x), +, 1) should canonicalize the Var(x) → Deref(Var(x))"
    );
}

/// `canonicalize_mut_ref_vars` correctly handles Final(Var("x")) — no change.
#[test]
#[timeout(30000)]
fn canonicalize_mut_ref_vars_preserves_final_var() {
    use std::collections::HashSet;

    use crate::verify::mut_borrow::helpers::canonicalize_mut_ref_vars;

    let mut params = HashSet::new();
    params.insert("x");

    let input = PureExpr::Final(Arc::new(var("x")));
    let output = canonicalize_mut_ref_vars(&input, &params);
    assert_eq!(
        output, input,
        "Final(Var(x)) should be unchanged — Final encodes x_final correctly"
    );
}

/// `canonicalize_mut_ref_vars` with empty param_names is a no-op identity.
#[test]
#[timeout(30000)]
fn canonicalize_mut_ref_vars_empty_params_is_identity() {
    use std::collections::HashSet;

    use crate::verify::mut_borrow::helpers::canonicalize_mut_ref_vars;

    let params: HashSet<&str> = HashSet::new();

    let exprs = vec![
        var("x"),
        PureExpr::BinOp(
            Arc::new(var("x")),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(int(1)),
        ),
        PureExpr::Deref(Arc::new(var("x"))),
        method_call(var("x"), "len", vec![]),
    ];

    for expr in &exprs {
        let output = canonicalize_mut_ref_vars(expr, &params);
        assert_eq!(
            &output, expr,
            "empty params should produce identity: input={expr:?}"
        );
    }
}

/// `normalize_deref_final` strips sort annotation from `Final(Var("x", Some(Int)))`.
///
/// This is important for the eager instantiation pipeline: normalized ground
/// terms produce `Var("x_final", None)` regardless of the original sort
/// annotation on the inner Var. If the body also uses `Var("x_final", None)`,
/// structural equality succeeds. But if the body retains `Var("x_final", Some(Int))`,
/// the match fails.
#[test]
#[timeout(30000)]
fn normalize_deref_final_preserves_sort_on_final_var() {
    use crate::verify::{exprs_structurally_equal, normalize_deref_final};

    // Final(Var("x", Some(Int))) -> Var("x_final", Some(Int))
    // Sort annotation is preserved through finalization so that
    // ExprSort enrichment (#2036, #2037) information survives.
    let input = PureExpr::Final(Arc::new(PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::Int),
    )));
    let output = normalize_deref_final(&input);
    assert_eq!(
        output,
        PureExpr::Var("x_final".to_string(), Some(ExprSort::Int)),
        "normalize_deref_final should preserve sort: Final(Var(x, Int)) -> Var(x_final, Int)"
    );

    // Final(Var("x", None)) -> Var("x_final", None)
    let input2 = PureExpr::Final(Arc::new(var("x")));
    let output2 = normalize_deref_final(&input2);
    assert_eq!(output2, PureExpr::Var("x_final".to_string(), None));

    // Structural equality (Var nodes matched by name only) ensures that
    // sort-enriched and unannotated _final vars match in eager instantiation.
    assert!(
        exprs_structurally_equal(&output, &output2),
        "exprs_structurally_equal should match Final(Var(x, Int)) and Final(Var(x, None)) by name"
    );

    // But PartialEq distinguishes them (sort metadata differs)
    assert_ne!(
        output, output2,
        "PartialEq should distinguish sort-annotated from unannotated _final vars"
    );
}

/// `normalize_deref_final` strips sort annotation from `Deref(Var("x", Some(Int)))`.
///
/// `Deref(Var("x", Some(Int)))` normalizes to `Var("x", Some(Int))` — the Deref
/// is stripped but the sort annotation on the inner Var is PRESERVED (unlike Final).
/// This is because Deref just recurses into the inner expression, and plain
/// Var is a leaf that passes through unchanged.
#[test]
#[timeout(30000)]
fn normalize_deref_final_preserves_sort_on_deref_var() {
    use crate::verify::normalize_deref_final;

    // Deref(Var("x", Some(Int))) -> Var("x", Some(Int))
    let input = PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::Int),
    )));
    let output = normalize_deref_final(&input);
    assert_eq!(
        output,
        PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
        "Deref strips the wrapper but preserves inner Var's sort annotation"
    );

    // Deref(Var("x", None)) -> Var("x", None)
    let input2 = PureExpr::Deref(Arc::new(var("x")));
    let output2 = normalize_deref_final(&input2);
    assert_eq!(output2, var("x"));

    // These are NOT equal — sort annotation mismatch
    assert_ne!(
        output, output2,
        "Deref(Var(x, Int)) and Deref(Var(x, None)) normalize to DIFFERENT forms \
         because the inner Var sort is preserved"
    );
}

/// Documents that sort-annotated and unannotated vars differ under `PartialEq`
/// but match under `exprs_structurally_equal` (sort-insensitive).
///
/// Both Deref and Final paths now preserve sort annotations, which is correct
/// for ExprSort enrichment (#2036, #2037). Eager instantiation matching uses
/// `exprs_structurally_equal` and `try_match_expr` (which ignore sort on Var
/// nodes), so sort-enriched ground calls still match unannotated body vars.
#[test]
#[timeout(30000)]
fn normalize_deref_final_sort_enrichment_matching() {
    use crate::verify::{exprs_structurally_equal, normalize_deref_final};

    // Ground call has sort-annotated Deref — sort is preserved
    let ground = PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::Int),
    )));
    let ground_normalized = normalize_deref_final(&ground);

    // Body uses unannotated var
    let body_var = var("x");

    // PartialEq distinguishes them (sort metadata differs)
    assert_ne!(
        ground_normalized, body_var,
        "PartialEq: sort-annotated Deref and unannotated Var differ"
    );

    // But exprs_structurally_equal matches by name only
    assert!(
        exprs_structurally_equal(&ground_normalized, &body_var),
        "exprs_structurally_equal: sort-annotated and unannotated vars match by name"
    );

    // Final path also preserves sort now
    let ground_final = PureExpr::Final(Arc::new(PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::Int),
    )));
    let final_normalized = normalize_deref_final(&ground_final);
    let body_final_var = PureExpr::Var("x_final".to_string(), None);

    // PartialEq distinguishes them
    assert_ne!(
        final_normalized, body_final_var,
        "PartialEq: sort-annotated _final and unannotated _final differ"
    );

    // But exprs_structurally_equal matches by name
    assert!(
        exprs_structurally_equal(&final_normalized, &body_final_var),
        "exprs_structurally_equal: _final vars match by name regardless of sort"
    );
}

// --- normalize_deref_final Float variant panic (#1802 regression) ---
//
// `normalize_deref_final` must handle `PureExpr::Float` as a leaf — returning
// it unchanged. Before the fix, Float fell through to the binder match arm
// and hit `unreachable!`, causing a panic on any postcondition containing
// a float literal.

/// `normalize_deref_final` returns `PureExpr::Float` unchanged (leaf pass-through).
#[test]
#[timeout(30000)]
fn normalize_deref_final_handles_float_leaf() {
    use trust_wp_core::formula::FloatBits;

    use crate::verify::normalize_deref_final;

    #[allow(clippy::approx_constant)] // intentional: testing float encoding, not using PI
    let float_expr = PureExpr::Float(FloatBits::from_f64(3.14));
    let result = normalize_deref_final(&float_expr);
    assert_eq!(
        result, float_expr,
        "Float literal should pass through unchanged"
    );
}

/// `normalize_deref_final` recurses into expressions containing Float children.
#[test]
#[timeout(30000)]
fn normalize_deref_final_recurses_through_float_in_binop() {
    use trust_wp_core::formula::FloatBits;

    use crate::{verify::normalize_deref_final, BinOp};

    // Deref(Var("x")) + Float(2.5) — the Deref should be stripped, Float preserved.
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(var("x")))),
        BinOp::Add,
        Arc::new(PureExpr::Float(FloatBits::from_f64(2.5))),
    );
    let result = normalize_deref_final(&expr);
    let expected = PureExpr::BinOp(
        Arc::new(var("x")),
        BinOp::Add,
        Arc::new(PureExpr::Float(FloatBits::from_f64(2.5))),
    );
    assert_eq!(
        result, expected,
        "Deref stripped, Float leaf preserved in BinOp"
    );
}

/// `normalize_deref_final` handles Float inside Final-wrapped method calls.
#[test]
#[timeout(30000)]
fn normalize_deref_final_float_in_method_call_args() {
    use trust_wp_core::formula::FloatBits;

    use crate::verify::normalize_deref_final;

    // receiver.method(Final(Var("x")), Float(1.0))
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(var("self")),
        method: "check".to_string(),
        args: vec![
            PureExpr::Final(Arc::new(var("x"))),
            PureExpr::Float(FloatBits::from_f64(1.0)),
        ],
    };
    let result = normalize_deref_final(&expr);
    let expected = PureExpr::MethodCall {
        receiver: Arc::new(var("self")),
        method: "check".to_string(),
        args: vec![
            PureExpr::Var("x_final".to_string(), None),
            PureExpr::Float(FloatBits::from_f64(1.0)),
        ],
    };
    assert_eq!(
        result, expected,
        "Final renamed, Float preserved in method args"
    );
}

// --- push_pending_disjoint_constraint eager HashSet insertion invariant ---
//
// `push_pending_disjoint_constraint` must eagerly insert terms into
// `quantified_disjoint_terms` so that `mentions_quantified_term` can use
// O(1) HashSet lookup instead of O(C*T) Vec::contains scanning.

/// Verify that push_pending_disjoint_constraint inserts terms into the
/// HashSet immediately, so mentions_quantified_term works via O(1) lookup.
#[test]
#[timeout(30000)]
fn push_pending_disjoint_constraint_eagerly_populates_hashset() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let left = encoder
        .get_or_declare_var("__eager_left", ay_dpll::api::Sort::Int)
        .expect("left should declare");
    let right = encoder
        .get_or_declare_var("__eager_right", ay_dpll::api::Sort::Int)
        .expect("right should declare");
    let unrelated = encoder
        .get_or_declare_var("__eager_unrelated", ay_dpll::api::Sort::Int)
        .expect("unrelated should declare");

    // Before push: nothing in HashSet
    assert!(
        !encoder
            .assertion_pipeline_for_test()
            .contains_disjoint_term(left),
        "left should not be in HashSet before push"
    );

    encoder
        .assertion_pipeline_mut_for_test()
        .push_pending_disjoint_constraint(vec![left], vec![right]);

    // After push: both terms in HashSet immediately
    assert!(
        encoder
            .assertion_pipeline_for_test()
            .contains_disjoint_term(left),
        "left must be in HashSet immediately after push_pending_disjoint_constraint"
    );
    assert!(
        encoder
            .assertion_pipeline_for_test()
            .contains_disjoint_term(right),
        "right must be in HashSet immediately after push_pending_disjoint_constraint"
    );
    assert!(
        !encoder
            .assertion_pipeline_for_test()
            .contains_disjoint_term(unrelated),
        "unrelated terms must not be in HashSet"
    );

    // Constraint also in pending vec
    assert_eq!(
        encoder
            .assertion_pipeline_for_test()
            .pending_disjoint_constraints()
            .len(),
        1
    );
}
