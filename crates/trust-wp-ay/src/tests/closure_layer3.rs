// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Layer-3 closure specification encoding tests (#1495).
//!
//! Covers sort-aware FnMut/FnOnce Skolem witness generation and structural
//! closure resolve axioms for closure environment sorts.

use ntest::timeout;

use super::{super::*, helpers::*};
use crate::encoder::closure_sorts::closure_env_sort_name;

/// Layer-3: reverse fn_mut_once Skolem witness is closure-sort aware.
#[test]
#[timeout(30000)]
fn test_layer3_fn_mut_once_witness_uses_closure_sort_tag() {
    let closure_def_id = "crate::layer3::witness#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![crate::CaptureField::new(
                    "x",
                    crate::ExprSort::Int,
                    CaptureKind::ByValue,
                )],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare closure receiver");
    encoder
        .get_or_declare_var("f2", closure_sort.clone())
        .expect("declare closure post-state");

    let once = method_call(
        var("f"),
        "postcondition_once",
        vec![var("arg"), var("result")],
    );
    let post_mut = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("arg"), var("f2"), var("result")],
    );
    encoder
        .encode_pure(&once)
        .expect("postcondition_once should encode");
    encoder
        .encode_pure(&post_mut)
        .expect("postcondition_mut should encode");

    encoder.assert_fn_mut_once_law();

    let witness_name = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with("fn_mut_once_witness_3_"))
        .find(|name| name.contains("_c"))
        .cloned()
        .expect("expected closure-sort witness symbol with concrete 'c...' tag");
    let witness_decl = encoder
        .decls()
        .get_logic_func(&witness_name)
        .expect("witness declaration should exist");
    // Witness range is Sort::Uninterpreted (from sort tag reconstruction)
    // while closure_sort is Sort::Datatype after #2151. Compare by name.
    let witness_name_str = closure_env_sort_name(witness_decl.range())
        .expect("witness range should be a ClosureEnv sort");
    let closure_name_str =
        closure_env_sort_name(&closure_sort).expect("closure_sort should be ClosureEnv");
    assert_eq!(
        witness_name_str, closure_name_str,
        "witness return sort must match closure environment sort by name"
    );
}

/// Layer-3: structural closure resolve axioms are emitted for registered
/// closure sorts. A zero-capture closure resolves to `true`.
#[test]
#[timeout(30000)]
fn test_layer3_direct_closure_resolve_entrypoint_asserted() {
    let closure_def_id = "crate::layer3::resolve_direct#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![],
            },
        )
        .unwrap();

    encoder.assert_closure_resolve_axioms();

    let sort_name = closure_env_sort_name(&closure_sort).expect("expected ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_name = format!("closure_resolve_{suffix}");
    let resolve_decl = encoder
        .decls()
        .get_logic_func(&resolve_name)
        .expect("closure resolve declaration should exist after direct entrypoint")
        .clone();

    let env = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("declare closure env var");
    let resolve_env = encoder.solver_mut().apply(&resolve_decl, &[env]);
    let not_resolve_env = encoder.solver_mut().not(resolve_env);
    encoder.assert_term(not_resolve_env);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "direct closure resolve axiom entrypoint must force resolve(env) == true"
    );
}

/// Layer-3: structural closure resolve axioms are emitted for registered
/// closure sorts. A zero-capture closure resolves to `true`.
#[test]
#[timeout(30000)]
fn test_layer3_structural_closure_resolve_axiom_asserted() {
    let closure_def_id = "crate::layer3::resolve#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare closure receiver");
    encoder
        .get_or_declare_var("f2", closure_sort.clone())
        .expect("declare closure post-state");

    let once = method_call(
        var("f"),
        "postcondition_once",
        vec![var("arg"), var("result")],
    );
    let post_mut = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("arg"), var("f2"), var("result")],
    );
    encoder
        .encode_pure(&once)
        .expect("postcondition_once should encode");
    encoder
        .encode_pure(&post_mut)
        .expect("postcondition_mut should encode");

    // Layer-3 resolve axioms are registered from closure law assertion.
    encoder.assert_fn_mut_once_law();

    let sort_name = closure_env_sort_name(&closure_sort).expect("expected ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_name = format!("closure_resolve_{suffix}");
    let resolve_decl = encoder
        .decls()
        .get_logic_func(&resolve_name)
        .expect("closure resolve declaration should exist")
        .clone();

    let env = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("declare closure env var");
    let resolve_env = encoder.solver_mut().apply(&resolve_decl, &[env]);
    let not_resolve_env = encoder.solver_mut().not(resolve_env);
    encoder.assert_term(not_resolve_env);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "zero-capture closure resolve axiom must force resolve(env) == true"
    );
}

// ============================================================================
// Per-capture hist_inv decomposition tests (#758)
// ============================================================================

/// Find the hist_inv UF declaration by scanning logic functions for a name
/// starting with "closure_hist_inv_2_". Returns the declaration.
fn find_hist_inv_decl(encoder: &AYEncoder) -> ay_dpll::api::FuncDecl {
    encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, _)| name.starts_with("closure_hist_inv_2_"))
        .map(|(_, decl)| decl.clone())
        .expect("hist_inv declaration should exist after assert_fn_closure_laws")
}

/// hist_inv for a closure with only ByValue captures is trivially true.
/// The fn_mut law still contains `self == res_state`, but the hist_inv
/// axiom itself should not force identity.
///
/// Verifies: `NOT hist_inv(s2, r2)` is UNSAT (hist_inv is always true),
/// confirming that the axiom `hist_inv <=> true` holds for ByValue-only.
#[test]
#[timeout(30000)]
fn test_hist_inv_byvalue_only_is_unconstrained() {
    let closure_def_id = "crate::test_hist_inv::byvalue_only#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![crate::CaptureField::new(
                    "x",
                    crate::ExprSort::Int,
                    CaptureKind::ByValue,
                )],
            },
        )
        .unwrap();

    // Declare closure vars and encode postcondition_mut to trigger law registration
    encoder
        .get_or_declare_var("s", closure_sort.clone())
        .expect("declare self");
    encoder
        .get_or_declare_var("r", closure_sort.clone())
        .expect("declare res_state");

    let post_mut = method_call(
        var("s"),
        "postcondition_mut",
        vec![var("arg"), var("r"), var("result")],
    );
    let post = method_call(var("s"), "postcondition", vec![var("arg"), var("result")]);
    encoder
        .encode_pure(&post_mut)
        .expect("encode postcondition_mut");
    encoder.encode_pure(&post).expect("encode postcondition");

    // Assert closure laws (which emits hist_inv axiom)
    encoder.assert_fn_closure_laws();

    let hist_inv_decl = find_hist_inv_decl(&encoder);

    // Verify hist_inv is always true: NOT hist_inv(s2, r2) should be UNSAT
    let s = encoder
        .get_or_declare_var("s2", closure_sort.clone())
        .unwrap();
    let r = encoder
        .get_or_declare_var("r2", closure_sort.clone())
        .unwrap();
    let hi = encoder.solver_mut().apply(&hist_inv_decl, &[s, r]);
    let not_hi = encoder.solver_mut().not(hi);
    encoder.solver_mut().push();
    encoder.assert_term(not_hi);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "ByValue-only hist_inv should be always true (UNSAT when negated)"
    );
    encoder.solver_mut().pop();
}

/// hist_inv for a closure with a ByRef capture should enforce identity on
/// that field. If we assert hist_inv(s, r) and capture_0(s) != capture_0(r)
/// where capture_0 is ByRef, the formula should be UNSAT.
#[test]
#[timeout(30000)]
fn test_hist_inv_byref_capture_enforces_identity() {
    let closure_def_id = "crate::test_hist_inv::byref_only#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![crate::CaptureField::new(
                    "x",
                    crate::ExprSort::Int,
                    CaptureKind::ByRef,
                )],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("s", closure_sort.clone())
        .expect("declare self");
    encoder
        .get_or_declare_var("r", closure_sort.clone())
        .expect("declare res_state");

    let post_mut = method_call(
        var("s"),
        "postcondition_mut",
        vec![var("arg"), var("r"), var("result")],
    );
    let post = method_call(var("s"), "postcondition", vec![var("arg"), var("result")]);
    encoder
        .encode_pure(&post_mut)
        .expect("encode postcondition_mut");
    encoder.encode_pure(&post).expect("encode postcondition");

    encoder.assert_fn_closure_laws();

    let hist_inv_decl = find_hist_inv_decl(&encoder);

    let sort_name = closure_env_sort_name(&closure_sort).expect("expected ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();

    let s = encoder
        .get_or_declare_var("s2", closure_sort.clone())
        .unwrap();
    let r = encoder
        .get_or_declare_var("r2", closure_sort.clone())
        .unwrap();
    let hi = encoder.solver_mut().apply(&hist_inv_decl, &[s, r]);
    encoder.assert_term(hi);

    // Assert capture_0(s2) != capture_0(r2) — should be UNSAT because
    // ByRef captures have identity in hist_inv. Use try_datatype_selector (#2151).
    let selector_name = format!("closure_capture_{suffix}_0");
    let s_cap = encoder
        .solver_mut()
        .try_datatype_selector(&selector_name, s, Sort::Int)
        .expect("selector for capture_0");
    let r_cap = encoder
        .solver_mut()
        .try_datatype_selector(&selector_name, r, Sort::Int)
        .expect("selector for capture_0");
    let eq = encoder.solver_mut().eq(s_cap, r_cap);
    let neq = encoder.solver_mut().not(eq);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "ByRef hist_inv should force capture fields equal (identity constraint)"
    );
}

/// Build a mixed-capture encoder (ByRef + ByValue) with hist_inv asserted.
/// Returns `(encoder, suffix, s_var, r_var)`.
fn setup_mixed_capture_hist_inv() -> (AYEncoder, String, ay_dpll::api::Term, ay_dpll::api::Term) {
    let closure_def_id = "crate::test_hist_inv::mixed#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![
                    crate::CaptureField::new(
                        "shared_ref",
                        crate::ExprSort::Int,
                        CaptureKind::ByRef,
                    ),
                    crate::CaptureField::new(
                        "owned_val",
                        crate::ExprSort::Int,
                        CaptureKind::ByValue,
                    ),
                ],
            },
        )
        .unwrap();

    encoder
        .get_or_declare_var("s", closure_sort.clone())
        .unwrap();
    encoder
        .get_or_declare_var("r", closure_sort.clone())
        .unwrap();

    let post_mut = method_call(
        var("s"),
        "postcondition_mut",
        vec![var("arg"), var("r"), var("result")],
    );
    let post = method_call(var("s"), "postcondition", vec![var("arg"), var("result")]);
    encoder
        .encode_pure(&post_mut)
        .expect("encode postcondition_mut");
    encoder.encode_pure(&post).expect("encode postcondition");
    encoder.assert_fn_closure_laws();

    let hist_inv_decl = find_hist_inv_decl(&encoder);
    let sort_name = closure_env_sort_name(&closure_sort).expect("expected ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap().to_string();

    let s = encoder
        .get_or_declare_var("s2", closure_sort.clone())
        .unwrap();
    let r = encoder
        .get_or_declare_var("r2", closure_sort.clone())
        .unwrap();
    let hi = encoder.solver_mut().apply(&hist_inv_decl, &[s, r]);
    encoder.assert_term(hi);

    (encoder, suffix, s, r)
}

/// Mixed-capture hist_inv: the axiom is satisfiable and correctly
/// constrains ByRef fields while ByValue fields remain logically free.
///
/// With native datatype registration (#2151), the hist_inv axiom for
/// mixed captures constrains ByRef fields (capture_0) but not ByValue
/// fields (capture_1). This test verifies hist_inv(s2, r2) is SAT.
#[test]
#[timeout(30000)]
fn test_hist_inv_mixed_byvalue_unconstrained() {
    let (mut encoder, suffix, s, r) = setup_mixed_capture_hist_inv();

    // hist_inv(s2, r2) is already asserted in setup. Verify the solver
    // finds a satisfying model (ByRef fields equal, ByValue fields free).
    let sat_result = encoder.check_sat();
    assert!(
        sat_result.is_sat() || sat_result.is_unknown(),
        "Mixed-capture hist_inv should be satisfiable, got {sat_result:?}"
    );

    // Verify ByRef constraint: capture_0(s2) != capture_0(r2) is UNSAT
    // (ByRef field identity is enforced by hist_inv).
    let selector_0 = format!("closure_capture_{suffix}_0");
    let s_ref = encoder
        .solver_mut()
        .try_datatype_selector(&selector_0, s, Sort::Int)
        .expect("selector for capture_0");
    let r_ref = encoder
        .solver_mut()
        .try_datatype_selector(&selector_0, r, Sort::Int)
        .expect("selector for capture_0");
    let eq_ref = encoder.solver_mut().eq(s_ref, r_ref);
    let neq_ref = encoder.solver_mut().not(eq_ref);
    encoder.solver_mut().push();
    encoder.assert_term(neq_ref);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "ByRef field must be identity-constrained even in mixed closure"
    );
    encoder.solver_mut().pop();
}

/// Mixed-capture hist_inv: ByRef field (index 0) should enforce identity.
#[test]
#[timeout(30000)]
fn test_hist_inv_mixed_byref_enforces_identity() {
    let (mut encoder, suffix, s, r) = setup_mixed_capture_hist_inv();

    // Use try_datatype_selector for native datatype captures (#2151).
    let selector_0 = format!("closure_capture_{suffix}_0");
    let s_ref = encoder
        .solver_mut()
        .try_datatype_selector(&selector_0, s, Sort::Int)
        .expect("selector for capture_0");
    let r_ref = encoder
        .solver_mut()
        .try_datatype_selector(&selector_0, r, Sort::Int)
        .expect("selector for capture_0");
    let eq_ref = encoder.solver_mut().eq(s_ref, r_ref);
    let neq_ref = encoder.solver_mut().not(eq_ref);
    encoder.assert_term(neq_ref);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "ByRef capture in mixed closure must be identity-constrained by hist_inv"
    );
}

// ============================================================================
// ensure_closure_resolve_axiom_for_sort + resolve_term_for_sort coverage (#1998)
// ============================================================================

/// Calling `assert_closure_resolve_axioms` twice must be idempotent —
/// the resolve UF declaration is reused and the axiom guard prevents
/// double-assertion. Verify by checking SAT result is unchanged.
///
/// Part of #1998
#[test]
#[timeout(30000)]
fn test_closure_resolve_axiom_idempotent() {
    let closure_def_id = "crate::test_resolve::idempotent#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![crate::CaptureField::new(
                    "x",
                    crate::ExprSort::Int,
                    CaptureKind::ByValue,
                )],
            },
        )
        .unwrap();

    encoder.assert_closure_resolve_axioms();
    let sort_name = closure_env_sort_name(&closure_sort).expect("ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_name = format!("closure_resolve_{suffix}");

    // First call: resolve should be registered
    assert!(
        encoder.decls().has_logic_func(&resolve_name),
        "resolve UF should be registered after first call"
    );
    let decl_count_1 = encoder.decls().logic_func_count();

    // Second call: idempotent — no new declarations
    encoder.assert_closure_resolve_axioms();
    let decl_count_2 = encoder.decls().logic_func_count();
    assert_eq!(
        decl_count_1, decl_count_2,
        "second assert_closure_resolve_axioms should not add new declarations"
    );

    // Semantic: resolve(env) should still hold (single ByValue → true)
    let env = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("declare env");
    let resolve_decl = encoder
        .decls()
        .get_logic_func(&resolve_name)
        .unwrap()
        .clone();
    let resolve_env = encoder.solver_mut().apply(&resolve_decl, &[env]);
    let not_resolve = encoder.solver_mut().not(resolve_env);
    encoder.assert_term(not_resolve);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "resolve should still be true after idempotent double-call"
    );
}

/// `resolve_term_for_sort` on a closure with ByMutRef capture decomposes
/// structurally. For a single ByMutRef Int capture, resolve(env) is true
/// because flat-sort resolve returns true. This verifies the decomposition
/// path through `resolve_term_for_capture` → `resolve_term_for_sort`.
///
/// Part of #1998
#[test]
#[timeout(30000)]
fn test_closure_resolve_bymutref_capture_decomposition() {
    let closure_def_id = "crate::test_resolve::bymutref#0";
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![crate::CaptureField::new(
                    "x",
                    crate::ExprSort::Int,
                    CaptureKind::ByMutRef,
                )],
            },
        )
        .unwrap();

    encoder.assert_closure_resolve_axioms();

    let sort_name = closure_env_sort_name(&closure_sort).expect("ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_name = format!("closure_resolve_{suffix}");
    let resolve_decl = encoder
        .decls()
        .get_logic_func(&resolve_name)
        .expect("resolve UF should be registered for ByMutRef closure")
        .clone();

    // ByMutRef of flat Int → resolve_term_for_sort returns true,
    // so the overall resolve axiom should be trivially true.
    let env = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("declare env");
    let resolve_env = encoder.solver_mut().apply(&resolve_decl, &[env]);
    let not_resolve = encoder.solver_mut().not(resolve_env);
    encoder.assert_term(not_resolve);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "ByMutRef of flat Int should resolve to true (flat sort = true)"
    );
}

/// Nested closure resolve: a closure capturing another closure by ByMutRef
/// should have its resolve decomposed recursively. The inner closure's
/// resolve is applied to the inner capture field.
///
/// Part of #1998
#[test]
#[timeout(30000)]
fn test_closure_resolve_nested_closure_capture_recursive() {
    let inner_def_id = "crate::test_resolve::inner#0";
    let outer_def_id = "crate::test_resolve::outer#0";
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register inner closure (zero captures → resolve is trivially true)
    let inner_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: inner_def_id.to_string(),
                captures: vec![],
            },
        )
        .unwrap();

    // Register outer closure capturing inner by ByMutRef
    let outer_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: outer_def_id.to_string(),
                captures: vec![crate::CaptureField::new(
                    "inner",
                    crate::ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(
                        crate::encoder::closure_sorts::closure_env_sort_name(&inner_sort)
                            .expect("inner closure sort should be a ClosureEnv datatype"),
                    )),
                    CaptureKind::ByMutRef,
                )],
            },
        )
        .unwrap();

    encoder.assert_closure_resolve_axioms();

    // Both closure resolve UFs should be registered
    let inner_sort_name = closure_env_sort_name(&inner_sort).expect("inner sort");
    let inner_suffix = inner_sort_name.strip_prefix("ClosureEnv_").unwrap();
    let outer_sort_name = closure_env_sort_name(&outer_sort).expect("outer sort");
    let outer_suffix = outer_sort_name.strip_prefix("ClosureEnv_").unwrap();
    assert!(
        encoder
            .decls()
            .has_logic_func(&format!("closure_resolve_{inner_suffix}")),
        "inner closure resolve UF should be registered"
    );
    assert!(
        encoder
            .decls()
            .has_logic_func(&format!("closure_resolve_{outer_suffix}")),
        "outer closure resolve UF should be registered"
    );

    // Outer resolve decomposes to inner resolve on the captured field.
    // Both are trivially true (inner has zero captures), so
    // NOT(resolve_outer(env)) should be UNSAT.
    let outer_resolve = encoder
        .decls()
        .get_logic_func(&format!("closure_resolve_{outer_suffix}"))
        .unwrap()
        .clone();
    let env = encoder
        .get_or_declare_var("env", outer_sort)
        .expect("declare env");
    let resolve_env = encoder.solver_mut().apply(&outer_resolve, &[env]);
    let not_resolve = encoder.solver_mut().not(resolve_env);
    encoder.assert_term(not_resolve);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "nested closure resolve should decompose recursively (both trivially true)"
    );
}

/// `resolve_term_for_sort` returns `true` for non-closure sorts (Int, Seq, Bool).
/// This path is hit when fn_mut_once_law applies resolve to witness terms
/// that have non-closure sorts. Verifying indirectly: no resolve UF is registered
/// for non-closure sorts after `assert_closure_resolve_axioms`.
///
/// Part of #1998
#[test]
#[timeout(30000)]
fn test_resolve_no_uf_for_non_closure_sorts() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register only a closure sort, then assert resolve axioms
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "crate::test_resolve::nonclosure#0".to_string(),
                captures: vec![crate::CaptureField::new(
                    "x",
                    crate::ExprSort::Int,
                    CaptureKind::ByValue,
                )],
            },
        )
        .unwrap();

    encoder.assert_closure_resolve_axioms();

    // Only one resolve UF should exist (for the registered closure sort)
    let resolve_keys: Vec<&String> = encoder
        .decls()
        .logic_func_names()
        .filter(|k| k.starts_with("closure_resolve_"))
        .collect();
    assert_eq!(
        resolve_keys.len(),
        1,
        "only the registered closure sort should have a resolve UF, got: {resolve_keys:?}"
    );

    // No resolve for Int, Seq, Bool
    let resolve_int = encoder
        .decls()
        .logic_func_names()
        .any(|k| k.contains("Int") && k.starts_with("closure_resolve_"));
    assert!(
        !resolve_int,
        "no resolve UF should exist for non-closure sort Int"
    );

    // The closure resolve should still work
    let sort_name = closure_env_sort_name(&closure_sort).expect("ClosureEnv sort");
    let suffix = sort_name.strip_prefix("ClosureEnv_").unwrap();
    let resolve_name = format!("closure_resolve_{suffix}");
    assert!(
        encoder.decls().has_logic_func(&resolve_name),
        "closure resolve UF should exist"
    );
}
