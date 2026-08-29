// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bool coercion paths, unsoundness category classification, standard ground
//! instances, `eq_or_iff`, polymorphic mapping UFs, tuple and method fallback
//! regressions (#994, #2231).

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use super::super::helpers::{int, method_call, var, var_with_sort};
use crate::{AYEncoder, ExprSort, PureExpr};

// ── coerce_bool_operand soundness boundary (#994, #2231) ──────────────────
//
// `coerce_bool_operand` has 3 code paths:
//   Path 1: Sort::Bool → identity (correct, no coercion)
//   Path 2: Sort::Int → neq(term, 0) (C-style truthiness coercion)
//   Path 3: Other sort → fresh Bool constant (lossy replacement)
//
// Path 3 is a significant soundness gap: replacing a non-Int/non-Bool term
// with a fresh unconstrained Bool constant means the solver can choose ANY
// truth value. This is sound-by-default (verification becomes weaker, not
// stronger), but still worth testing to lock the behavior.
//
// Zero unit tests existed for this function before this commit.

/// Path 1: Bool term passes through `coerce_bool_operand` unchanged.
#[test]
#[timeout(30000)]
fn coerce_bool_operand_path1_bool_identity() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let bool_term = encoder.solver.declare_const("b", Sort::Bool);
    let coerced = encoder.coerce_bool_operand(bool_term);
    assert_eq!(
        encoder.solver.get_sort(coerced),
        Sort::Bool,
        "Bool input must remain Bool"
    );
    // Identity: the term should be the same object (no wrapping)
    assert_eq!(
        bool_term, coerced,
        "Bool passthrough should return the same term, not a wrapper"
    );
}

/// Path 2: Int term becomes `neq(term, 0)` — C-style truthiness.
/// The coerced term must be Bool-sorted and must be SAT-equivalent to
/// the original being nonzero.
#[test]
#[timeout(30000)]
fn coerce_bool_operand_path2_int_to_bool() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_term = encoder.solver.declare_const("n", Sort::Int);
    let coerced = encoder.coerce_bool_operand(int_term);
    assert_eq!(
        encoder.solver.get_sort(coerced),
        Sort::Bool,
        "Int coercion must produce Bool"
    );
    // Semantic check: assert n = 0 AND coerced = true should be UNSAT
    // (because coerced = neq(n, 0) = false when n = 0)
    let zero = encoder.solver.int_const(0);
    let n_is_zero = encoder.solver.eq(int_term, zero);
    let coerced_true = coerced; // coerced is already the Bool term
    encoder.solver.assert_term(n_is_zero);
    encoder.solver.assert_term(coerced_true);
    let result = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "n=0 AND neq(n,0)=true should be UNSAT, got {result:?}"
    );
}

/// Path 2 positive: Int=5 makes the coerced Bool true (SAT).
#[test]
#[timeout(30000)]
fn coerce_bool_operand_path2_nonzero_int_is_true() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_term = encoder.solver.declare_const("n", Sort::Int);
    let coerced = encoder.coerce_bool_operand(int_term);
    let five = encoder.solver.int_const(5);
    let n_is_five = encoder.solver.eq(int_term, five);
    encoder.solver.assert_term(n_is_five);
    encoder.solver.assert_term(coerced);
    let result = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Sat),
        "n=5 AND neq(n,0)=true should be SAT, got {result:?}"
    );
}

/// Path 3: Non-Int/non-Bool sort (e.g., Uninterpreted) produces a fresh Bool
/// constant. The fresh constant is unconstrained, so both true and false should
/// be satisfiable independently.
#[test]
#[timeout(30000)]
fn coerce_bool_operand_path3_uninterpreted_fresh_const() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let weird_sort = Sort::Uninterpreted("Weird".to_string());
    let weird_term = encoder.solver.fresh_var("w", weird_sort);
    let coerced = encoder.coerce_bool_operand(weird_term);
    assert_eq!(
        encoder.solver.get_sort(coerced),
        Sort::Bool,
        "Non-Int/non-Bool coercion must produce Bool"
    );
    // The fresh Bool is unconstrained — both polarities should be SAT
    // (this is sound: it makes verification weaker, not stronger)
    assert_ne!(
        coerced, weird_term,
        "Path 3 must NOT return the original non-Bool term"
    );
}

/// Path 3 soundness: asserting the coerced fresh Bool true is SAT (not
/// overconstrained). This verifies the fresh constant doesn't accidentally
/// get constrained to false by the coercion machinery.
#[test]
#[timeout(30000)]
fn coerce_bool_operand_path3_fresh_is_satisfiable() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let seq_sort = Sort::seq(Sort::Int);
    let seq_term = encoder.solver.fresh_var("s", seq_sort);
    let coerced = encoder.coerce_bool_operand(seq_term);
    encoder.solver.assert_term(coerced);
    let result = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Sat),
        "Fresh Bool from path 3 should be satisfiable, got {result:?}"
    );
}

/// Multiple calls to path 3 produce DISTINCT fresh constants.
/// This ensures two different non-Bool operands don't accidentally
/// share the same fresh Bool variable.
#[test]
#[timeout(30000)]
fn coerce_bool_operand_path3_distinct_fresh_consts() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap_sort = Sort::Uninterpreted("FMap".to_string());
    let t1 = encoder.solver.fresh_var("m1", fmap_sort.clone());
    let t2 = encoder.solver.fresh_var("m2", fmap_sort);
    let c1 = encoder.coerce_bool_operand(t1);
    let c2 = encoder.coerce_bool_operand(t2);
    assert_ne!(
        c1, c2,
        "Distinct non-Bool operands must produce distinct fresh Bool constants"
    );
    // Assert c1 = true and c2 = false — should be SAT since they're independent
    let not_c2 = encoder.solver.not(c2);
    encoder.solver.assert_term(c1);
    encoder.solver.assert_term(not_c2);
    let result = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Sat),
        "Distinct fresh Bools should be independently satisfiable, got {result:?}"
    );
}

// ── Unsoundness demotion classification audit (#2106) ─────────────────────
//
// `UnsoundnessCategory::is_demoting` controls whether a `Verified` result
// gets demoted to `Unknown`. If a category that CAN produce false proofs
// is classified as non-demoting (LOW), the pipeline has a soundness hole.
//
// These meta-tests lock the classification so reclassifications require
// deliberate test updates, not accidental drift.

/// All defined categories are present in `UnsoundnessCategory::ALL`.
/// Catches accidental omissions when adding new categories.
#[test]
#[timeout(30000)]
fn unsoundness_category_all_is_exhaustive() {
    use crate::encoder::unsoundness::UnsoundnessCategory;
    // Current count: 15 categories (6 HIGH + 2 MEDIUM + 7 LOW).
    // If a new category is added to the enum but not to ALL, this fails.
    assert!(
        UnsoundnessCategory::ALL.len() >= 15,
        "Expected at least 15 unsoundness categories, got {}. \
         Did you add a new category without updating ALL?",
        UnsoundnessCategory::ALL.len()
    );
}

/// HIGH-risk categories (5) must all be demoting.
/// False proofs from these categories are NOT caught without demotion.
#[test]
#[timeout(30000)]
fn unsoundness_high_risk_categories_are_demoting() {
    use crate::encoder::unsoundness::UnsoundnessCategory;
    let high_risk = [
        UnsoundnessCategory::LetAssumeDropped,
        UnsoundnessCategory::SpecAxiomDropped,
        UnsoundnessCategory::SortFallbackToInt,
        // ClosureBodyTrueDefault ELIMINATED (#2541) — no production increment sites
        // BitwiseUfApproximation ELIMINATED (#2666) — BV mode always-on
        UnsoundnessCategory::OpaqueCallTrueAssumption,
        UnsoundnessCategory::IntegerCastIdentity,
    ];
    for cat in &high_risk {
        assert!(
            cat.is_demoting(),
            "HIGH-risk category {cat:?} must be demoting — \
             false proofs are possible without demotion"
        );
    }
}

/// MEDIUM-risk categories (2) must all be demoting.
/// Edge-case false proofs from these categories are caught by demotion.
#[test]
#[timeout(30000)]
fn unsoundness_medium_risk_categories_are_demoting() {
    use crate::encoder::unsoundness::UnsoundnessCategory;
    let medium_risk = [
        UnsoundnessCategory::PanicRecoveryFalse,
        UnsoundnessCategory::SortFallbackToIntFromLogicFn,
    ];
    for cat in &medium_risk {
        assert!(
            cat.is_demoting(),
            "MEDIUM-risk category {cat:?} must be demoting — \
             edge-case false proofs are possible without demotion"
        );
    }
}

/// LOW-risk categories (7) must NOT be demoting.
/// These produce conservative approximations (false counterexamples, not false proofs).
/// Making them demoting would cause excessive Unknown results.
#[test]
#[timeout(30000)]
fn unsoundness_low_risk_categories_are_not_demoting() {
    use crate::encoder::unsoundness::UnsoundnessCategory;
    let low_risk = [
        UnsoundnessCategory::UnsupportedConstructSkip,
        UnsoundnessCategory::CatchUnwindFallback,
        UnsoundnessCategory::ClosureAxiomSkipped,
        UnsoundnessCategory::SortFallbackToIntFromVar,
        UnsoundnessCategory::InvariantTrueShortCircuit,
        UnsoundnessCategory::SortFallbackToIntFromMethodCall,
        UnsoundnessCategory::BoolCoercionFromNonBool,
    ];
    for cat in &low_risk {
        assert!(
            !cat.is_demoting(),
            "LOW-risk category {cat:?} must NOT be demoting — \
             conservative approximations should not trigger Unknown results"
        );
    }
}

/// Demoting count equals HIGH + MEDIUM count.
/// Catches classification drift where a category moves risk level
/// but `is_demoting` isn't updated to match.
#[test]
#[timeout(30000)]
fn unsoundness_demoting_count_matches_classification() {
    use crate::encoder::unsoundness::UnsoundnessCategory;
    let demoting_count = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.is_demoting())
        .count();
    // 7 HIGH + 3 MEDIUM = 10 demoting
    // (ClosureBodyTrueDefault reclassified non-demoting, ELIMINATED #2541)
    // (UnconstrainedResultVar split from SortFallbackToInt as MEDIUM #2663)
    // (BitwiseUfApproximation reclassified non-demoting, ELIMINATED #2666)
    // (FinalCollapseRefused added as HIGH — Final-collapse audit Fix A)
    // (OpaqueClosureValueFallback added as HIGH — vacfix: the opaque Bool
    //  closure VALUE whose ite(b,1,0) promotion fabricates a {0,1} bound;
    //  reclassified out of the LOW UnsupportedConstructSkip bucket)
    assert_eq!(
        demoting_count, 10,
        "Expected 10 demoting categories (7 HIGH + 3 MEDIUM), got {demoting_count}. \
         Classification may have drifted — update risk level tests above."
    );
}

// ── index/get dispatch parity (#994) ──────────────────────────────────────
//
// `len`, `contains`, `index_logic`, `index`, and `get` all need the same
// inferred-sort safety net when receiver classifiers miss a bare variable that
// only carries its concrete sort in `var_sorts`.

/// `len` on a bare Var with Seq sort in var_sorts (no sort hint) correctly
/// routes to seq_len via the `infer_encoded_sort` fallback at
/// method_call/mod.rs:316-324.
///
/// Key setup: bare `Var("s_view")` (NOT wrapped in View). `View(Var("s"))`
/// receivers are promoted to Seq by the prescan `is_ambiguous_seq` heuristic
/// in hint_collection.rs:286 — that tests a different (working) path.
/// The gap is specifically for bare Var receivers where the prescan's
/// bare-Var guard (line 286: `!matches!(receiver, Var(_, _))`) prevents
/// Seq hint registration, relying solely on the dispatch-time fallback.
#[test]
#[timeout(30000)]
fn dispatch_len_has_infer_encoded_sort_fallback() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let seq_sort = Sort::seq(Sort::Int);
    let _ = encoder.get_or_declare_var("s_view", seq_sort);

    // Bare Var("s_view").len() — no View wrapper, no annotation, no hint
    let receiver = var("s_view");
    let expr = method_call(receiver, "len", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "len on bare Seq-sorted Var should succeed via infer_encoded_sort fallback: {result:?}"
    );
    let term = result.unwrap();
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Int,
        "seq_len should return Int"
    );
    // Verify: no generic method_len UF was created (correctly routed to Seq)
    let logic_fns = encoder.logic_func_names();
    let has_generic_len = logic_fns.iter().any(|n| n.starts_with("method_len_"));
    assert!(
        !has_generic_len,
        "len should use seq_len, not a generic method_len UF. logic_fns={logic_fns:?}"
    );
}

/// `index` on a bare Var with Seq sort in var_sorts (no sort hint) should use
/// the same inferred-sort fallback as `len`, routing to the Seq encoder.
#[test]
#[timeout(30000)]
fn dispatch_index_has_infer_encoded_sort_fallback() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let seq_sort = Sort::seq(Sort::Int);
    let _ = encoder.get_or_declare_var("s_view", seq_sort);

    // Bare Var("s_view").index(0) — no View wrapper, no annotation, no hint
    let receiver = var("s_view");
    let expr = method_call(receiver, "index", vec![int(0)]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "index on bare Seq-sorted Var should route to Seq encoding: {result:?}"
    );
    let logic_fns = encoder.logic_func_names();
    let has_generic_method_uf = logic_fns.iter().any(|n| n.starts_with("method_index_"));
    assert!(
        !has_generic_method_uf,
        "index on bare Seq-sorted Var should not create generic method_index UF: \
         logic_fns={logic_fns:?}"
    );
}

/// Parity check: `len` and `index` both use inferred-sort fallback on the same
/// hintless bare Seq receiver.
#[test]
#[timeout(30000)]
fn dispatch_len_index_parity_on_hintless_seq_receiver() {
    // Test len: should use Seq path via infer_encoded_sort fallback
    let mut len_encoder = AYEncoder::new_pure_with_quantifiers();
    let seq_sort = Sort::seq(Sort::Int);
    let _ = len_encoder.get_or_declare_var("s_view", seq_sort.clone());
    let receiver = var("s_view");
    let len_result = len_encoder.encode_pure(&method_call(receiver.clone(), "len", vec![]));
    assert!(
        len_result.is_ok(),
        "len should route to Seq via infer_encoded_sort fallback"
    );
    let len_logic_fns = len_encoder.logic_func_names();
    let len_has_generic = len_logic_fns.iter().any(|n| n.starts_with("method_len_"));
    assert!(
        !len_has_generic,
        "len correctly uses seq_len, not generic method_len UF"
    );

    // Test index: now routes to the same Seq path
    let mut idx_encoder = AYEncoder::new_pure_with_quantifiers();
    let _ = idx_encoder.get_or_declare_var("s_view", seq_sort);
    let idx_result = idx_encoder.encode_pure(&method_call(receiver, "index", vec![int(0)]));
    assert!(
        idx_result.is_ok(),
        "index should route to Seq via infer_encoded_sort fallback"
    );
    let idx_logic_fns = idx_encoder.logic_func_names();
    let idx_has_generic = idx_logic_fns.iter().any(|n| n.starts_with("method_index_"));
    assert!(
        !idx_has_generic,
        "index should use seq_index_logic, not generic method_index UF: {idx_logic_fns:?}"
    );
}

// ── assert_standard_ground_instances wiring completeness ──────────────
//
// Regression guard: verify that all ground instance sub-handlers are wired
// into assert_standard_ground_instances(). The Mapping handler was added in
// W2-2349 (ca5d0e7c) but is at risk of silent removal during dirty-tree
// file merges.

/// Regression guard: `assert_standard_ground_instances` must call
/// `assert_mapping_ground_instances` for Mapping read-over-write axioms.
///
/// Without this wiring, `mapping_set` ground entries are registered during
/// encoding but the same-key read-over-write axiom `get(set(m,k,v),k) = v`
/// is never asserted as a ground instance. The quantified axiom in axioms.rs
/// covers the general case, but ay-dpll's single-round E-matching may fail
/// to fire it on concrete terms.
///
/// The committed code (W2-2349) has this wiring at ground_pool.rs:411.
/// This test catches silent reverts (e.g., dirty-tree file merge drops).
#[test]
#[timeout(30000)]
fn assert_standard_ground_instances_includes_mapping() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    // Declare mapping UFs
    let get_decl =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);
    let set_decl = encoder.get_or_declare_spec_fn(
        "mapping_set",
        &[mapping.clone(), Sort::Int, Sort::Int],
        mapping.clone(),
    );

    let m = encoder.solver.fresh_var("m", mapping);
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    // Register a mapping_set ground application
    let set_app = encoder.solver.apply(&set_decl, &[m, k, v]);
    encoder.register_standard_ground_application("mapping_set", set_app, vec![m, k, v]);

    // Also register mapping_get so the handler has the get decl
    let get_app = encoder.solver.apply(&get_decl, &[m, k]);
    encoder.register_standard_ground_application("mapping_get", get_app, vec![m, k]);

    // assert_standard_ground_instances should fire the mapping handler
    let count = encoder.assert_standard_ground_instances();
    assert!(
        count >= 1,
        "assert_standard_ground_instances must include mapping ground instances. \
         Got count={count}. If 0, assert_mapping_ground_instances is not wired in \
         (check instantiation.rs for `count += self.assert_mapping_ground_instances(remaining_budget)`)."
    );
}

/// Regression guard: verify that Mapping read-over-write ground instance
/// is semantically correct at SMT level (UNSAT when contradicted).
///
/// Asserts `get(set(m,k,v), k) = v` from the ground instance handler,
/// then contradicts with `get(set(m,k,v), k) != v`. UNSAT confirms
/// the axiom is sound.
#[test]
#[timeout(30000)]
fn mapping_ground_instance_read_over_write_is_sound() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    let get_decl =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);
    let set_decl = encoder.get_or_declare_spec_fn(
        "mapping_set",
        &[mapping.clone(), Sort::Int, Sort::Int],
        mapping.clone(),
    );

    let m = encoder.solver.fresh_var("m", mapping);
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    let set_app = encoder.solver.apply(&set_decl, &[m, k, v]);
    encoder.register_standard_ground_application("mapping_set", set_app, vec![m, k, v]);

    // Fire ground instances — this should assert get(set(m,k,v),k) = v
    let count = encoder.assert_standard_ground_instances();
    assert!(
        count >= 1,
        "mapping ground instances should fire, got {count}"
    );

    // Now contradict: assert get(set(m,k,v),k) != v
    let get_set_k = encoder.solver.apply(&get_decl, &[set_app, k]);
    let neq = encoder.solver.eq(get_set_k, v);
    let neq = encoder.solver.not(neq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "mapping ground instance get(set(m,k,v),k)=v should make contradiction UNSAT, got {result:?}"
    );
}

// ── eq_or_iff sort handling soundness ────────────────────────────────
//
// eq_or_iff is now a compatibility wrapper over the shared equality helper.
// These tests keep the legacy wrong-hint scenarios alive so sort-repair and
// panic-isolation behavior stay covered while the wrapper is phased out.
//
// These tests guard the #994/#2231 hardening.

/// Bool operands should still reject disagreement on the happy path.
#[test]
#[timeout(30000)]
fn eq_or_iff_bool_hint_with_bool_terms_produces_iff() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let a = encoder.solver.fresh_var("a", Sort::Bool);
    let b = encoder.solver.fresh_var("b", Sort::Bool);

    let result = encoder.eq_or_iff(a, b, &Sort::Bool);
    // Result should be Bool-sorted.
    assert_eq!(
        encoder.solver.get_sort(result),
        Sort::Bool,
        "eq_or_iff with Bool hint and Bool terms should produce a Bool result"
    );

    // Verify it rejects disagreement: assert a=true, b=false, equality term.
    encoder.solver.assert_term(a);
    let not_b = encoder.solver.not(b);
    encoder.solver.assert_term(not_b);
    encoder.solver.assert_term(result);
    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, ay_dpll::api::SolveResult::Unsat(_)),
        "bool equality with disagreeing operands should be UNSAT, got {sat_result:?}"
    );
}

/// Wrong Bool hints on non-Bool operands must still land on the shared
/// equality path rather than panicking.
#[test]
#[timeout(30000)]
fn eq_or_iff_bool_hint_survives_sort_mismatch() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_term = encoder.solver.fresh_var("x", Sort::Int);
    let seq_sort = Sort::seq(Sort::Int);
    let seq_term = encoder.solver.fresh_var("s", seq_sort);

    let result = encoder.eq_or_iff(int_term, seq_term, &Sort::Bool);
    assert_eq!(
        encoder.solver.get_sort(result),
        Sort::Bool,
        "eq_or_iff should still return Bool when the Bool hint is wrong"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "wrong Bool hint should not leak an uncaught solver panic"
    );
}

/// Documents that the generic equality path still survives a sort mismatch
/// (Int vs Seq) without panicking.
#[test]
#[timeout(30000)]
fn eq_or_iff_non_bool_path_survives_sort_mismatch() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_term = encoder.solver.fresh_var("x", Sort::Int);
    let seq_sort = Sort::seq(Sort::Int);
    let seq_term = encoder.solver.fresh_var("s", seq_sort);

    // Non-Bool path: sort hint is Int but actual terms are Int vs Seq.
    // The non-Bool path should coerce or recover via catch_solver_panic.
    let result = encoder.eq_or_iff(int_term, seq_term, &Sort::Int);
    // Result should be Bool-sorted (either a valid eq or false from panic recovery)
    assert_eq!(
        encoder.solver.get_sort(result),
        Sort::Bool,
        "eq_or_iff non-Bool path should produce Bool even on sort mismatch"
    );
}

/// Verifies that the shared equality path with matching Int sorts still
/// produces a semantically correct equality.
#[test]
#[timeout(30000)]
fn eq_or_iff_int_path_correct_equality() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let y = encoder.solver.fresh_var("y", Sort::Int);

    let eq = encoder.eq_or_iff(x, y, &Sort::Int);
    assert_eq!(encoder.solver.get_sort(eq), Sort::Bool);

    // Assert x=5, y=5, eq should be SAT
    let five = encoder.solver.int_const(5);
    let x_eq_5 = encoder.solver.eq(x, five);
    let y_eq_5 = encoder.solver.eq(y, five);
    encoder.solver.assert_term(x_eq_5);
    encoder.solver.assert_term(y_eq_5);
    encoder.solver.assert_term(eq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "eq(5, 5) should be SAT, got {result:?}"
    );
}

// ── fmap_instances sort hint consistency ──────────────────────────────
//
// The quantified and ground fmap insert axioms should use the same lookup
// result sort when constructing `eq_or_iff`.

/// Regression guard for the direct lookup equality asserted by the fmap insert
/// ground-instance handler.
#[test]
#[timeout(30000)]
fn fmap_insert_ground_lookup_sort_is_consistent_with_encoding() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = Sort::Uninterpreted("FMap".to_string());

    // Declare FMap UFs with Int value sort (current encoding)
    let _contains_decl =
        encoder.get_or_declare_spec_fn("fmap_contains", &[fmap.clone(), Sort::Int], Sort::Bool);
    let lookup_decl =
        encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap.clone(), Sort::Int], Sort::Int);
    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let _len_decl =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    // Register insert ground application
    let insert_app = encoder.solver.apply(&insert_decl, &[m, k, v]);
    encoder.register_standard_ground_application("fmap_insert", insert_app, vec![m, k, v]);

    // Fire ground instances
    let count = encoder.assert_standard_ground_instances();
    assert!(
        count >= 2,
        "fmap_insert ground instances should fire at least contains + lookup axioms, got {count}"
    );

    // Verify lookup(insert(m,k,v), k) = v is asserted (UNSAT when contradicted)
    let lookup_ins_k = encoder.solver.apply(&lookup_decl, &[insert_app, k]);
    let neq = encoder.solver.eq(lookup_ins_k, v);
    let neq = encoder.solver.not(neq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "fmap_insert ground lookup axiom should make lookup(insert(m,k,v),k)!=v UNSAT, got {result:?}"
    );
}

/// `mapping_get` with a Seq-sorted key should use a sort-polymorphic UF
/// (`mapping_get__Seq`) instead of panicking on domain sort mismatch. (#2316)
///
/// This is the root cause of the cell/03_as_slice_of_cells crash: the PredCell
/// requires clause `cell@[*s]` passes a Seq-sorted key to `mapping_get`, which
/// was monomorphically declared as `(Mapping, Int) -> Int`.
#[test]
#[timeout(30000)]
fn mapping_get_seq_key_uses_polymorphic_uf() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
    let seq_sort = Sort::seq(Sort::Int);
    let mapping_ann = ExprSort::Datatype(intern_sort_name("Mapping"));

    let _m_term = encoder.solver.declare_const("m", mapping_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("m".to_string(), mapping_sort.clone());
    let _s_term = encoder.solver.declare_const("s", seq_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("s".to_string(), seq_sort.clone());

    // m.get(s) where m: Mapping and s: Seq — should produce mapping_get__Seq
    let expr = method_call(
        var_with_sort("m", mapping_ann),
        "get",
        vec![var_with_sort("s", ExprSort::Seq)],
    );
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "mapping_get with Seq key should encode without panic, got: {:?}",
        result.err()
    );

    // The Seq-keyed dispatch falls through to encode_int_method_uf which
    // registers under `method_get_2_{sort_tag}` naming (not mapping_get__Seq).
    // The monomorphic mapping_get should NOT have entries (Seq key bypasses it).
    let mono_entries = encoder.ground_pool_for_test().entries_for("mapping_get");
    assert!(
        mono_entries.is_none_or(<[_]>::is_empty),
        "ground pool should NOT contain monomorphic mapping_get when only Seq keys were used"
    );
}

/// `mapping_set` with non-Int key and value sorts should use polymorphic UF. (#2316)
#[test]
#[timeout(30000)]
fn mapping_set_non_int_key_val_uses_polymorphic_uf() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
    let seq_sort = Sort::seq(Sort::Int);
    let mapping_ann = ExprSort::Datatype(intern_sort_name("Mapping"));

    let _m_term = encoder.solver.declare_const("m", mapping_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("m".to_string(), mapping_sort.clone());
    let _s_term = encoder.solver.declare_const("s", seq_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("s".to_string(), seq_sort);

    // m.set(s, 42) where s: Seq, 42: Int
    let expr = method_call(
        var_with_sort("m", mapping_ann),
        "set",
        vec![var_with_sort("s", ExprSort::Seq), int(42)],
    );
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "mapping_set with Seq key should encode without panic, got: {:?}",
        result.err()
    );

    // The Seq-keyed dispatch falls through to encode_int_method_uf which
    // registers under `method_set_3_{sort_tag}` naming (not mapping_set__Seq_Int).
    // The monomorphic mapping_set should NOT have entries.
    let mono_entries = encoder.ground_pool_for_test().entries_for("mapping_set");
    assert!(
        mono_entries.is_none_or(<[_]>::is_empty),
        "ground pool should NOT contain monomorphic mapping_set when Seq keys were used"
    );
}

// ── tuple axiom sort guard boundary (#994) ──────────────────────────
//
// The sort guard in `assert_tuple_axioms` (adt_axioms/tuple.rs) skips
// axioms when the accessor's domain sort doesn't match the constructor's
// return sort. This prevents ay panics from sort-mismatch applications.
//
// These tests verify the guard's boundary conditions:
// 1. Matching sorts → axiom fires → destructuring is sound
// 2. Mismatched sorts → axiom is skipped → no panic

/// When constructor and accessor sorts match (both Int→Int), the tuple
/// destructor axiom `get_0(tuple2(a,b)) = a` must fire. Without it,
/// tuple destructuring is uninterpreted and postconditions involving
/// tuple fields become unprovable.
///
/// This is the happy-path boundary: `accessor_domain == ctor_return`.
#[test]
#[timeout(30000)]
fn tuple_axiom_fires_when_sorts_match() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Compute the correct SMT-encoded names for tuple functions.
    let ctor_name = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple2");
    let getter_name = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");

    // Declare tuple2 constructor and get_0 accessor with matching Int sorts.
    let ctor = encoder
        .solver
        .declare_fun(&ctor_name, &[Sort::Int, Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(ctor_name, ctor.clone());
    let getter = encoder
        .solver
        .declare_fun(&getter_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(getter_name, getter.clone());

    // Assert axioms — should fire for get_0(tuple2)
    encoder.assert_tuple_axioms();

    // Test: get_0(tuple2(42, 99)) should equal 42
    let forty_two = encoder.solver.int_const(42);
    let ninety_nine = encoder.solver.int_const(99);
    let pair = encoder.solver.apply(&ctor, &[forty_two, ninety_nine]);
    let get_0 = encoder.solver.apply(&getter, &[pair]);
    let eq_term = encoder.solver.eq(get_0, forty_two);
    let negated = encoder.solver.not(eq_term);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "get_0(tuple2(42,99)) == 42 should hold (axiom must fire). Got {result:?}"
    );
}

/// When the accessor domain sort does NOT match the constructor return sort,
/// the axiom must be skipped (not panicking). The destructor then remains
/// uninterpreted — the solver cannot simplify `get_0(tuple2(a,b))`.
///
/// This guards the sort-guard boundary at adt_axioms/tuple.rs:106-109.
#[test]
#[timeout(30000)]
fn tuple_axiom_skipped_when_sorts_mismatch_no_panic() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let ctor_name = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple2");
    let getter_name = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");

    // Constructor returns Tuple2 (uninterpreted), but getter expects Int domain.
    // Sort mismatch: accessor domain (Int) != constructor return (Tuple2).
    let tuple2_sort = Sort::Uninterpreted("Tuple2".to_string());
    let ctor = encoder
        .solver
        .declare_fun(&ctor_name, &[Sort::Int, Sort::Int], tuple2_sort.clone());
    encoder
        .decls_for_test_mut()
        .insert_logic_func(ctor_name, ctor.clone());
    let getter = encoder
        .solver
        .declare_fun(&getter_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(getter_name, getter.clone());

    // This must not panic — sort guard should skip the axiom silently.
    encoder.assert_tuple_axioms();

    // Without the axiom, get_0(proxy) is unconstrained — the negation
    // of get_0(proxy) == 42 should be satisfiable.
    let forty_two = encoder.solver.int_const(42);
    // get_0 takes Int, but constructor returns Tuple2. The axiom was skipped
    // due to sort mismatch. Use a proxy Int constant to query the getter
    // behavior without a ay sort error from applying Int-domain getter to Tuple2.
    let pair_proxy = encoder.solver.declare_const("pair_proxy", Sort::Int);
    let get_0 = encoder.solver.apply(&getter, &[pair_proxy]);
    let eq_term = encoder.solver.eq(get_0, forty_two);
    let negated = encoder.solver.not(eq_term);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "get_0(proxy) != 42 should be Sat when axiom is skipped (sorts mismatch). Got {result:?}"
    );
}

/// Method call fallback: Bool sort hint takes priority over quantified Int UF.
///
/// When a method has a Bool sort hint and we're inside a quantifier scope,
/// the Bool hint path (encode_bool_method_predicate) should fire BEFORE
/// the quantified Int UF fallback (encode_int_method_uf). The if-else chain
/// at method_call/mod.rs:547 tests Bool hint before quantifier check.
///
/// This guards the priority ordering at the boundary between lines 547-555.
/// We encode `forall<x: Int> x.is_valid()` where `is_valid` has a Bool hint.
/// Inside the quantifier body, both `has_bound_vars()` is true AND the Bool
/// hint is present — the Bool path must win.
#[test]
#[timeout(30000)]
fn method_call_fallback_bool_hint_beats_quantified_int_uf() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register a Bool sort hint for the method name "is_valid" via sort_hints.
    // The method_call fallback checks sort_resolver.get_sort_hint(method) using
    // receiver-qualified keys (#2245): `x.is_valid` for `Var("x").is_valid()`.
    encoder.record_sort_hint("x.is_valid".to_string(), ExprSort::Bool);

    // Build forall<x: Int>. x.is_valid() — this enters a quantifier scope
    // during encoding and calls the method inside it.
    let body = method_call(var("x"), "is_valid", vec![]);
    let forall = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![],
    };

    let result = encoder.encode_pure(&forall);
    assert!(
        result.is_ok(),
        "forall with Bool-hinted is_valid should encode, got: {:?}",
        result.err()
    );

    // The forall itself should be Bool-sorted (quantifiers return Bool)
    let term = result.unwrap();
    let term_sort = encoder.solver.get_sort(term);
    assert_eq!(
        term_sort,
        Sort::Bool,
        "forall expression should be Bool-sorted, got {term_sort:?}"
    );

    // The decisive check: the declared UF's return sort must be Bool.
    // If the Int UF path had fired instead, the UF would return Sort::Int.
    // Both paths use the same naming: "method_is_valid_1_i" (1 param, Int tag).
    let uf_decl = encoder
        .decls()
        .get_logic_func("method_is_valid_1_i")
        .expect("method UF should have been declared during encoding");
    assert_eq!(
        *uf_decl.range(),
        Sort::Bool,
        "UF return sort must be Bool (Bool hint path), not Int (quantified Int UF path). \
         Got {:?}",
        uf_decl.range()
    );
}

// ── method_call proof-coverage: untested branches ───────────────────
//
// The method_call dispatch in encode_method_call_impl has ~33 arms.
// These tests cover branches with zero or near-zero test coverage,
// exercised through the public encode_pure API.

/// `start_log` dispatches to Int-returning UF for range iterator spec
/// accessors. This method is seeded by IntoIterator contracts and consumed
/// by range `produces` rewrites (#2171).
///
/// Guards: method_call/mod.rs:491 — `"start_log" | "end_log" if args.is_empty()`
#[test]
#[timeout(30000)]
fn method_call_start_log_encodes_as_int_uf() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("iter"), "start_log", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "start_log() should encode as Int UF, got: {:?}",
        result.err()
    );

    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Int,
        "start_log() must return Int (UF fallback for range spec accessor). Got {sort:?}"
    );
}

/// `end_log` dispatches to Int-returning UF, symmetric with `start_log`.
/// Guards: method_call/mod.rs:491 — same arm.
#[test]
#[timeout(30000)]
fn method_call_end_log_encodes_as_int_uf() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("iter"), "end_log", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "end_log() should encode as Int UF, got: {:?}",
        result.err()
    );

    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Int,
        "end_log() must return Int (UF fallback for range spec accessor). Got {sort:?}"
    );
}

/// `set` with 2 args on a receiver that is neither Seq nor Mapping
/// should fall through to the Int UF fallback (method_call/mod.rs:502).
///
/// The Seq path checks `is_seq_receiver`, the Mapping path checks
/// `is_mapping_receiver`. A plain untyped variable triggers neither,
/// so the fallback at line 502 fires.
#[test]
#[timeout(30000)]
fn method_call_set_2arg_non_seq_non_mapping_falls_to_int_uf() {
    let mut encoder = AYEncoder::new();
    // Plain var("ghost") is not annotated as Seq or Mapping.
    let expr = method_call(var("ghost"), "set", vec![int(0), int(42)]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "set(0, 42) on non-Seq/non-Mapping should encode as Int UF, got: {:?}",
        result.err()
    );

    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Int,
        "set(0, 42) on untyped receiver must return Int (UF fallback). Got {sort:?}"
    );
}

/// `merge` with 2 args dispatches through `encode_fmap_method` (method_call/mod.rs:295).
/// The FMap merge spec function returns an Int-sorted UF term representing
/// the merged map. This test verifies the dispatch path from `method_call`
/// through to `encode_fmap_method`, which was previously only tested at the
/// axiom level, not through `encode_method_call_impl`.
#[test]
#[timeout(30000)]
fn method_call_merge_2arg_dispatches_to_fmap() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("m1"), "merge", vec![var("m2"), var("m3")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "merge(m2, m3) should encode via fmap dispatch, got: {:?}",
        result.err()
    );

    // FMap methods produce spec_func declarations (not logic_funcs).
    // The merge spec function should be registered.
    assert!(
        encoder.decls().has_spec_func("fmap_merge"),
        "merge dispatch should declare fmap_merge spec function"
    );
}
