// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit pins for the CE-census fixes: counterexamples the census traced to
//! encoder seams rather than to the program under verification.
//!
//! One pin per seam, each with verified teeth (fails unfixed):
//! 1. Ground-then-drop coherence: grounding-exempt negative-contains standard
//!    foralls must be ASSERTED, not dropped (ghost_set proof_assert lib.rs:8).
//! 2. Std iterator-carrier `len` UF carries the FMap LEN law's cardinality
//!    non-negativity (fmap_iter merge_fmaps loop_variant_nonneg) — with a
//!    user-sort CONTROL proving no law is fabricated for non-std receivers.
//! 3. SeqIter⇄Seq harmonization bridges through `__vec_to_seq_*` instead of
//!    minting a value-discarding fresh constant (seq_iter reverse_ghost
//!    loop_initialization).
//! 4. FMap ext_eq fallback carries the EXT_EQ law's equal-args ground
//!    instance (cc/collections roundtrip_hashmap_into_iter proof_assert#4) —
//!    with a non-FMap CONTROL.

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort, TermKind};
use ntest::timeout;
use trust_wp_core::formula::{PureExpr, UnOp};

use super::helpers::{method_call, not, var};
use crate::{
    encoder::AYEncoder,
    verify::{verify_function_with_modes, VerificationRequest, VerificationResult},
};

fn negative_contains_forall(receiver: &str, bound: &str) -> PureExpr {
    PureExpr::Forall {
        var: bound.to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::UnOp(
            UnOp::Not,
            Arc::new(method_call(
                var(receiver),
                "contains",
                vec![PureExpr::Var(bound.to_string(), None)],
            )),
        )),
        triggers: vec![],
    }
}

// ── Pin 1: setup.rs ground-then-drop coherence ──────────────────────

/// A grounding-EXEMPT standard forall (negative-contains body, the FSet
/// EMPTY `forall<k> !result.contains(k)` shape) produces no ground
/// instances, so the post-grounding skip in `encode_and_assert_requires`
/// must not drop it — it must be asserted so ground goals can use it.
/// Unfixed: the premise is neither grounded nor asserted and the goal
/// `!set.contains(7)` gets a fabricated counterexample.
#[test]
#[timeout(60000)]
fn grounding_exempt_negative_contains_forall_is_asserted_not_dropped() {
    let requires = vec![negative_contains_forall("set", "k")];
    let ensures = vec![not(method_call(
        var("set"),
        "contains",
        vec![PureExpr::Int(7)],
    ))];
    let result = verify_function_with_modes(VerificationRequest::new(&requires, &ensures));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "the exempted negative-contains forall premise must reach the solver \
         and discharge the ground goal, got: {result:?}"
    );
}

// ── Pin 2: std iterator-carrier len non-negativity ──────────────────
// (lives in `encoder/method_call/int_uf_tests.rs` — the pinned entry point
// `encode_int_method_uf` is `pub(in crate::encoder)`:
// `std_iterator_len_uf_carries_cardinality_nonnegativity` +
// `user_receiver_len_uf_gets_no_fabricated_nonnegativity` control.)

// ── Pin 3: SeqIter⇄Seq harmonization ────────────────────────────────

/// Harmonizing an Uninterpreted("SeqIter") term against the canonical
/// (uninterpreted-carrier) Seq sort must route through the injective
/// `__vec_to_seq_SeqIter` bridge, not the value-discarding
/// `coerce_ite_sorts` fresh-constant fallback. Unfixed: the returned term
/// is a fresh unconstrained constant with no connection to the iterator.
#[test]
#[timeout(30000)]
fn seq_iterator_carrier_harmonizes_via_vec_to_seq_bridge() {
    let mut encoder = AYEncoder::new();
    encoder.force_uninterpreted_seq_sort_for_mixed_datatype();
    let seq_sort = encoder.get_seq_sort();
    let it = encoder
        .solver
        .declare_const("it", Sort::Uninterpreted("SeqIter".to_string()));
    let s = encoder.solver.declare_const("s", seq_sort.clone());

    let (ha, hb) = encoder.harmonize_eq_or_ite_terms(it, s);

    assert_eq!(hb, s, "the Seq side must pass through unchanged");
    assert_eq!(
        encoder.solver.get_sort(ha),
        seq_sort,
        "the SeqIter side must be bridged to the Seq sort"
    );
    let is_bridge_app = matches!(
        encoder.solver.term_kind(ha),
        TermKind::App { ref name, .. } if name == "__vec_to_seq_SeqIter"
    );
    assert!(
        is_bridge_app,
        "the SeqIter side must be the __vec_to_seq_SeqIter bridge application \
         (value-preserving), not a fresh constant: {:?}",
        encoder.solver.term_kind(ha)
    );
}

// ── Pin 4: FMap ext_eq equal-args ground law ────────────────────────

/// The non-Seq ext_eq fallback on FMap-sorted operands must carry the
/// EXT_EQ law's equal-args ground instance (`a == b ==> ext_eq(a, b)`,
/// entailed by trust-wp-std/src/logic/fmap.rs `FMap::ext_eq` plus
/// congruence). Unfixed: even the reflexive equal-view goal is
/// unprovable because the fallback UF has no defining law in scope.
#[test]
#[timeout(30000)]
fn fmap_ext_eq_fallback_carries_equal_args_law() {
    let mut encoder = AYEncoder::new();
    // Canonical FMap carrier sort (sort_mapping::fmap_sort, not visible here)
    let fmap = Sort::Uninterpreted("FMap".to_string());
    let a_term = encoder
        .get_or_declare_var("m1", fmap.clone())
        .expect("declare FMap operand");
    let b_term = encoder
        .get_or_declare_var("m2", fmap)
        .expect("declare FMap operand");

    let ext_eq_expr = method_call(var("m1"), "ext_eq", vec![var("m2")]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq_expr)
        .expect("FMap ext_eq should encode via the bool-UF fallback");

    let args_eq = encoder.eq_term(a_term, b_term);
    encoder.solver.assert_term(args_eq);
    let goal_negated = encoder.solver.not(ext_eq_term);
    encoder.solver.assert_term(goal_negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "equal FMap operands must entail ext_eq via the EXT_EQ law instance"
    );
}

/// CONTROL (cardinal rule): non-FMap operands get NO equal-args law —
/// an unknown user `ext_eq` need not be reflexive.
#[test]
#[timeout(30000)]
fn non_fmap_ext_eq_fallback_gets_no_equal_args_law() {
    let mut encoder = AYEncoder::new();
    let widget = Sort::Uninterpreted("Widget".to_string());
    let a_term = encoder
        .get_or_declare_var("w1", widget.clone())
        .expect("declare user operand");
    let b_term = encoder
        .get_or_declare_var("w2", widget)
        .expect("declare user operand");

    let ext_eq_expr = method_call(var("w1"), "ext_eq", vec![var("w2")]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq_expr)
        .expect("user ext_eq should encode via the bool-UF fallback");

    let args_eq = encoder.eq_term(a_term, b_term);
    encoder.solver.assert_term(args_eq);
    let goal_negated = encoder.solver.not(ext_eq_term);
    encoder.solver.assert_term(goal_negated);
    assert!(
        !matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "no reflexivity law may be fabricated for user-defined ext_eq"
    );
}
