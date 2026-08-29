// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for quantified equality handling in solver — extracted from inline tests (#1669).

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn mentions_quantified_term_detects_active_and_pending_terms() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let active = encoder
        .get_or_declare_var("__qt_active", Sort::Int)
        .expect("active term should declare");
    let pending_left = encoder
        .get_or_declare_var("__qt_pending_left", Sort::Int)
        .expect("pending-left term should declare");
    let pending_right = encoder
        .get_or_declare_var("__qt_pending_right", Sort::Int)
        .expect("pending-right term should declare");
    let unrelated = encoder
        .get_or_declare_var("__qt_unrelated", Sort::Int)
        .expect("unrelated term should declare");

    assert!(
        !encoder.mentions_quantified_term(unrelated),
        "unrelated terms should not be reported as quantified"
    );

    encoder
        .assertion_pipeline
        .insert_disjoint_term_for_test(active);
    assert!(
        encoder.mentions_quantified_term(active),
        "active quantified terms must be detected"
    );

    encoder
        .assertion_pipeline
        .push_pending_disjoint_constraint(vec![pending_left], vec![pending_right]);
    assert!(
        encoder.mentions_quantified_term(pending_left),
        "pending-left quantified term must be detected"
    );
    assert!(
        encoder.mentions_quantified_term(pending_right),
        "pending-right quantified term must be detected"
    );
    assert!(
        !encoder.mentions_quantified_term(unrelated),
        "pending constraints must not mark unrelated terms"
    );
}

#[test]
#[timeout(30000)]
fn has_relevant_quantified_equality_requires_quantified_reference() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let lhs = encoder
        .get_or_declare_var("__qeq_lhs", Sort::Int)
        .expect("lhs should declare");
    let rhs = encoder
        .get_or_declare_var("__qeq_rhs", Sort::Int)
        .expect("rhs should declare");

    encoder
        .assertion_pipeline
        .push_pending_pure_equality((lhs, rhs));
    assert!(
        !encoder.has_relevant_quantified_equality(),
        "plain equalities without quantified terms must not trigger recheck"
    );

    encoder
        .assertion_pipeline
        .insert_disjoint_term_for_test(lhs);
    assert!(
        encoder.has_relevant_quantified_equality(),
        "equalities touching quantified terms must trigger recheck"
    );
}

#[test]
#[timeout(30000)]
fn has_relevant_quantified_equality_detects_pending_constraint_terms() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let pending_left = encoder
        .get_or_declare_var("__qeq_pending_left", Sort::Int)
        .expect("pending-left should declare");
    let pending_right = encoder
        .get_or_declare_var("__qeq_pending_right", Sort::Int)
        .expect("pending-right should declare");
    let plain = encoder
        .get_or_declare_var("__qeq_plain", Sort::Int)
        .expect("plain should declare");

    encoder
        .assertion_pipeline
        .push_pending_disjoint_constraint(vec![pending_left], vec![pending_right]);
    encoder
        .assertion_pipeline
        .push_pending_pure_equality((plain, pending_right));

    assert!(
        encoder.has_relevant_quantified_equality(),
        "pending quantified constraints should count for relevant equality detection"
    );
}

#[cfg(debug_assertions)]
#[test]
#[timeout(30000)]
fn check_sat_with_pending_assertions_returns_unknown() {
    let mut encoder = AYEncoder::new();
    encoder
        .assertion_pipeline
        .push_pending_assertion(encoder.solver.bool_const(true));

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "check_sat must fail closed when pending assertions are not flushed"
    );
    let reason = encoder
        .solver_panic_reason()
        .expect("debug assert should set solver panic reason");
    assert!(
        reason.contains("unflushed pending assertions"),
        "panic reason should mention the pending-assertion invariant, got: {reason}"
    );
}

#[cfg(debug_assertions)]
#[test]
#[timeout(30000)]
fn check_sat_with_pending_quantified_constraints_returns_unknown() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let left = encoder
        .get_or_declare_var("__pending_qdc_left", Sort::Int)
        .expect("left should declare");
    let right = encoder
        .get_or_declare_var("__pending_qdc_right", Sort::Int)
        .expect("right should declare");
    encoder
        .assertion_pipeline
        .push_pending_disjoint_constraint(vec![left], vec![right]);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "check_sat must fail closed when quantified constraints are not activated"
    );
    let reason = encoder
        .solver_panic_reason()
        .expect("debug assert should set solver panic reason");
    assert!(
        reason.contains("unflushed pending assertions"),
        "panic reason should mention the pending-assertion invariant, got: {reason}"
    );
}

#[test]
#[timeout(30000)]
fn get_model_panic_records_reason_and_forces_unknown() {
    let mut encoder = AYEncoder::new();
    let model = encoder.get_model_with_fetch(|_| {
        panic!("BUG: Model validation failed: synthetic get_model panic")
    });
    assert!(
        model.is_none(),
        "get_model panic path must return None fallback"
    );

    let reason = encoder
        .solver_panic_reason()
        .expect("get_model panic path must store reason");
    assert!(
        reason.contains("synthetic get_model panic"),
        "stored reason should include panic payload, got: {reason}"
    );
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "recorded get_model panic reason must force Unknown in later SAT checks"
    );
}

#[test]
#[timeout(30000)]
fn quantified_disjoint_recheck_turns_spurious_sat_into_unsat() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let left = encoder
        .get_or_declare_var("__qeq_recheck_left", Sort::Int)
        .expect("left term should declare");
    let right = encoder
        .get_or_declare_var("__qeq_recheck_right", Sort::Int)
        .expect("right term should declare");

    // Seed one active quantified disjoint constraint set directly so this
    // test targets the recheck loop itself.
    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![left], vec![right]);
    encoder
        .assertion_pipeline
        .insert_disjoint_term_for_test(left);
    encoder
        .assertion_pipeline
        .insert_disjoint_term_for_test(right);

    // Force the "assertions changed" gate so recheck runs.
    encoder.assertion_pipeline.prime_recheck_for_test();

    // Initial model is SAT under left == right; the recheck must
    // materialize left != right and flip the result to UNSAT.
    let forced_alias = encoder.solver.eq(left, right);
    encoder.solver.assert_term(forced_alias);

    let result = encoder.check_sat_with_quantified_disjoint_recheck();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "recheck should convert forced aliasing into UNSAT, got {result:?}"
    );
    assert!(
        encoder
            .assertion_pipeline
            .has_asserted_neq_pair((left, right)),
        "recheck should materialize an explicit left != right pair"
    );
    assert_eq!(
        encoder.assertion_pipeline.quantified_pairs_revision(),
        encoder.assertion_pipeline.assertion_revision(),
        "recheck should sync quantified_pairs_revision after completion"
    );
}

#[test]
#[timeout(30000)]
fn assert_term_non_bool_does_not_panic_and_forces_unknown() {
    let mut encoder = AYEncoder::new();
    let non_bool = encoder.solver.int_const(1);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(non_bool);
    }));
    assert!(
        result.is_ok(),
        "assert_term should not panic when ay rejects non-Bool terms: {result:?}"
    );
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "solver assertion panic must force Unknown SAT results"
    );
}

#[test]
#[timeout(30000)]
fn assert_term_pending_non_bool_is_panic_isolated() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let quantified = encoder
        .get_or_declare_var("__panic_guard", Sort::Int)
        .expect("quantified term should declare");
    encoder
        .assertion_pipeline
        .insert_disjoint_term_for_test(quantified);
    encoder
        .assertion_pipeline
        .push_pending_pure_equality((quantified, quantified));
    encoder
        .assertion_pipeline
        .push_pending_assertion(encoder.solver.int_const(7));
    let guard = encoder.solver.bool_const(true);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(guard);
    }));
    assert!(
        result.is_ok(),
        "pending assertion panic should be isolated by catch_solver_panic: {result:?}"
    );
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "panic-isolated pending assertions must force Unknown SAT results"
    );
}

/// Regression test for #1098: when the primary assertion panics,
/// pending assertions must be drained but not asserted to the solver.
#[test]
#[timeout(30000)]
fn primary_assertion_failure_drains_without_asserting_pending() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let quantified = encoder
        .get_or_declare_var("__drain_pending", Sort::Int)
        .expect("quantified term should declare");
    encoder
        .assertion_pipeline
        .insert_disjoint_term_for_test(quantified);
    encoder
        .assertion_pipeline
        .push_pending_pure_equality((quantified, quantified));

    // Add a valid pending assertion that would succeed if attempted.
    let valid_pending = encoder.solver.bool_const(true);
    encoder
        .assertion_pipeline
        .push_pending_assertion(valid_pending);

    // Primary term is non-Bool — will panic inside assert_solver_term,
    // returning false. Before the fix, the pending assertion would still
    // be sent to the solver.
    let non_bool_primary = encoder.solver.int_const(42);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(non_bool_primary);
    }));
    assert!(
        result.is_ok(),
        "primary assertion failure must not propagate panic: {result:?}"
    );
    assert!(
        encoder.assertion_pipeline.pending_assertions_is_empty(),
        "pending assertions must be drained even after primary failure"
    );
    assert!(
        encoder.solver_panic_reason().is_some(),
        "solver_panic_reason must be set after primary assertion failure"
    );
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "check_sat must return Unknown after primary assertion failure"
    );
}

#[test]
#[timeout(30000)]
fn primary_assertion_failure_leaves_quantified_constraints_pending() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let left = encoder
        .get_or_declare_var("__panic_pending_left", Sort::Int)
        .expect("left term should declare");
    let right = encoder
        .get_or_declare_var("__panic_pending_right", Sort::Int)
        .expect("right term should declare");
    encoder
        .assertion_pipeline
        .push_pending_disjoint_constraint(vec![left], vec![right]);
    encoder
        .assertion_pipeline
        .push_pending_pure_equality((left, right));

    let non_bool_primary = encoder.solver.int_const(99);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(non_bool_primary);
    }));
    assert!(
        result.is_ok(),
        "primary assertion failure must not propagate panic: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_some(),
        "solver_panic_reason must be set after primary assertion failure"
    );
    assert_eq!(
        encoder
            .assertion_pipeline
            .pending_disjoint_constraints()
            .len(),
        1,
        "poisoned assert_term must leave quantified constraints pending"
    );
    assert!(
        encoder
            .assertion_pipeline
            .active_disjoint_constraints_is_empty(),
        "poisoned assert_term must not activate quantified constraints"
    );
    assert_eq!(
        encoder.assertion_pipeline.pending_pure_equalities_len(),
        1,
        "poisoned assert_term must not clear pending equality terms"
    );
    assert_eq!(
        encoder.assertion_pipeline.quantified_pairs_revision(),
        0,
        "poisoned assert_term must not advance quantified recheck revisions"
    );
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "check_sat must still fail closed after the poisoned assertion"
    );
}

#[test]
#[timeout(30000)]
fn assert_term_pending_non_bool_is_panic_isolated_individually() {
    let mut encoder = AYEncoder::new();
    encoder
        .assertion_pipeline
        .push_pending_assertion(encoder.solver.int_const(11));
    let guard = encoder.solver.bool_const(true);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(guard);
    }));
    assert!(
        result.is_ok(),
        "pending assertion path should isolate solver panics: {result:?}"
    );
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "panic in pending assertion must force Unknown"
    );
}

/// Recheck loop converges with multiple disjoint constraint sets.
/// When multiple (left, right) pairs collide in the initial model,
/// the recheck loop must materialize neq for all of them. (#1208)
#[test]
#[timeout(30000)]
fn recheck_loop_converges_with_multiple_constraint_sets() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = encoder
        .get_or_declare_var("__recheck_a", Sort::Int)
        .expect("a");
    let b = encoder
        .get_or_declare_var("__recheck_b", Sort::Int)
        .expect("b");
    let c = encoder
        .get_or_declare_var("__recheck_c", Sort::Int)
        .expect("c");

    // Two separate disjoint constraint sets: (a != b) and (a != c)
    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![a], vec![b]);
    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![a], vec![c]);
    for &term in &[a, b, c] {
        encoder
            .assertion_pipeline
            .insert_disjoint_term_for_test(term);
    }

    encoder.assertion_pipeline.prime_recheck_for_test();

    // Force all three to equal the same value — the recheck loop must
    // materialize a != b and a != c, making the system UNSAT.
    let ab = encoder.solver.eq(a, b);
    encoder.solver.assert_term(ab);
    let ac = encoder.solver.eq(a, c);
    encoder.solver.assert_term(ac);

    let result = encoder.check_sat_with_quantified_disjoint_recheck();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "multiple collision sets should all be resolved, got {result:?}"
    );
    assert!(
        encoder.assertion_pipeline.has_asserted_neq_pair((a, b)),
        "a != b should be materialized"
    );
    assert!(
        encoder.assertion_pipeline.has_asserted_neq_pair((a, c)),
        "a != c should be materialized"
    );
}

/// Bool pigeonhole: 3 Bool vars with pairwise disjoint constraints
/// converges to Unsat. Verifies the recheck loop handles
/// unsatisfiable systems correctly even with a low pass bound. (#1208)
///
/// NOTE: The `exhausted_bound` code path (returning Unknown on bound
/// exhaustion) is defense-in-depth for pathological solver behavior.
/// In practice, the recheck loop discovers all collisions in one pass
/// (since it iterates all constraint sets per pass), so the bound
/// is never reached. This test verifies the pigeonhole resolves
/// correctly; the bound-return-Unknown logic is verified by code
/// review and the `debug_assert!` guard.
#[test]
#[timeout(30000)]
fn recheck_pigeonhole_bool_resolves_to_unsat() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = encoder
        .get_or_declare_var("__bound_a", Sort::Bool)
        .expect("a");
    let b = encoder
        .get_or_declare_var("__bound_b", Sort::Bool)
        .expect("b");
    let c = encoder
        .get_or_declare_var("__bound_c", Sort::Bool)
        .expect("c");

    // Pairwise disjoint constraints: a != b, b != c, a != c.
    // With Bool (2 values), this is unsatisfiable (pigeonhole).
    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![a], vec![b]);
    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![b], vec![c]);
    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![a], vec![c]);
    for &term in &[a, b, c] {
        encoder
            .assertion_pipeline
            .insert_disjoint_term_for_test(term);
    }

    encoder.assertion_pipeline.prime_recheck_for_test();

    // Even with max_passes = 1, the loop discovers all collisions in
    // pass 0, asserts neq for all, and rechecks → Unsat.
    let result = encoder.check_sat_with_quantified_disjoint_recheck_bounded(1);
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Bool pigeonhole must resolve to Unsat, got {result:?}"
    );

    // Full bound also resolves to Unsat.
    let mut encoder2 = AYEncoder::new_with_quantifiers();
    let a2 = encoder2
        .get_or_declare_var("__bound2_a", Sort::Bool)
        .expect("a");
    let b2 = encoder2
        .get_or_declare_var("__bound2_b", Sort::Bool)
        .expect("b");
    let c2 = encoder2
        .get_or_declare_var("__bound2_c", Sort::Bool)
        .expect("c");

    encoder2
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![a2], vec![b2]);
    encoder2
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![b2], vec![c2]);
    encoder2
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![a2], vec![c2]);
    for &term in &[a2, b2, c2] {
        encoder2
            .assertion_pipeline
            .insert_disjoint_term_for_test(term);
    }
    encoder2.assertion_pipeline.prime_recheck_for_test();

    let full_result = encoder2.check_sat_with_quantified_disjoint_recheck();
    assert!(
        matches!(full_result, SolveResult::Unsat(_)),
        "pigeonhole must be Unsat with full bound, got {full_result:?}"
    );
}

/// Recheck loop syncs revision even when initial SAT has no collisions.
#[test]
#[timeout(30000)]
fn recheck_loop_syncs_revision_without_collisions() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = encoder
        .get_or_declare_var("__recheck_nocol_a", Sort::Int)
        .expect("a");
    let b = encoder
        .get_or_declare_var("__recheck_nocol_b", Sort::Int)
        .expect("b");

    // Add a constraint set but don't force a collision — the terms
    // may or may not collide in the model, but we constrain them apart.
    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![a], vec![b]);
    encoder.assertion_pipeline.insert_disjoint_term_for_test(a);
    encoder.assertion_pipeline.insert_disjoint_term_for_test(b);

    encoder.assertion_pipeline.prime_recheck_for_test();

    // Constrain a and b to different values so no collision occurs.
    let a_val = encoder.solver.int_const(0);
    let b_val = encoder.solver.int_const(1);
    let eq_a = encoder.solver.eq(a, a_val);
    let eq_b = encoder.solver.eq(b, b_val);
    encoder.solver.assert_term(eq_a);
    encoder.solver.assert_term(eq_b);

    let result = encoder.check_sat_with_quantified_disjoint_recheck();
    assert_eq!(result, SolveResult::Sat, "no collision should remain SAT");
    assert_eq!(
        encoder.assertion_pipeline.quantified_pairs_revision(),
        encoder.assertion_pipeline.assertion_revision(),
        "revision must be synced even when no neq was materialized"
    );
}

/// Recheck loop detects collisions for UF application terms.
///
/// Exercises the recheck loop with uninterpreted function application
/// terms f(x) and f(y) rather than bare variables. When x == y is
/// asserted, f(x) == f(y) by functional consistency, so the recheck
/// loop must detect the collision and the result must not be Sat.
///
/// This also serves as a regression guard for #1780: the
/// `recheck_one_constraint_set` helper now returns `Abort` (→ Unknown)
/// if `get_value` returns `None`, rather than silently skipping terms.
#[test]
#[timeout(30000)]
fn recheck_loop_detects_uf_application_collision() {
    // UF application terms exercise a more complex model evaluation
    // path than bare variables.
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare an uninterpreted function f: Int -> Int
    let f_decl = encoder
        .solver
        .declare_fun("__recheck_uf_f", &[Sort::Int], Sort::Int);

    let x = encoder
        .get_or_declare_var("__recheck_uf_x", Sort::Int)
        .expect("x");
    let y = encoder
        .get_or_declare_var("__recheck_uf_y", Sort::Int)
        .expect("y");

    // Create application terms f(x) and f(y)
    let fx = encoder.solver.apply(&f_decl, &[x]);
    let fy = encoder.solver.apply(&f_decl, &[y]);

    // Force x == y so f(x) == f(y) — this should create a collision
    // that the recheck loop detects and resolves.
    let xy_eq = encoder.solver.eq(x, y);
    encoder.solver.assert_term(xy_eq);

    // Add a quantified disjoint constraint between f(x) and f(y).
    // Since x == y, f(x) == f(y) in the model, so the recheck loop
    // should detect the collision, assert neq(f(x), f(y)), and on
    // recheck produce Unsat (since functional consistency requires
    // f(x) == f(y) when x == y).
    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![fx], vec![fy]);
    encoder.assertion_pipeline.insert_disjoint_term_for_test(fx);
    encoder.assertion_pipeline.insert_disjoint_term_for_test(fy);

    encoder.assertion_pipeline.prime_recheck_for_test();

    let result = encoder.check_sat_with_quantified_disjoint_recheck();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "recheck loop must return Unsat when UF terms collide in model, got {result:?}"
    );
}

/// Build an encoder with `n` Bool variables and all-pairs disjoint
/// constraints (pigeonhole setup). Revisions are set so the recheck fires.
///
/// Used by the full-bound pigeonhole test below.
fn build_bool_pigeonhole_encoder(n: usize, prefix: &str) -> AYEncoder {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let vars: Vec<Term> = (0..n)
        .map(|i| {
            encoder
                .get_or_declare_var(&format!("{prefix}_b{i}"), Sort::Bool)
                .expect("bool var")
        })
        .collect();
    for i in 0..n {
        for j in (i + 1)..n {
            encoder
                .assertion_pipeline
                .push_active_disjoint_constraint_for_test(vec![vars[i]], vec![vars[j]]);
            encoder
                .assertion_pipeline
                .insert_disjoint_term_for_test(vars[i]);
            encoder
                .assertion_pipeline
                .insert_disjoint_term_for_test(vars[j]);
        }
    }
    encoder.assertion_pipeline.prime_recheck_for_test();
    encoder
}

/// Build a 4-Bool recheck fixture that deterministically needs two passes.
///
/// The direct solver constraints `a != b` and `c != d` force the initial
/// model into a 2+2 partition. The first recheck pass can only discover one
/// of the two possible cross-partition matchings, which leaves a satisfiable
/// 4-cycle. A second pass is then required to discover the alternate matching
/// and close the graph to the full Bool pigeonhole contradiction.
fn build_two_pass_bool_recheck_encoder(prefix: &str) -> AYEncoder {
    let mut encoder = build_bool_pigeonhole_encoder(4, prefix);
    let a = encoder
        .get_or_declare_var(&format!("{prefix}_b0"), Sort::Bool)
        .expect("a");
    let b = encoder
        .get_or_declare_var(&format!("{prefix}_b1"), Sort::Bool)
        .expect("b");
    let c = encoder
        .get_or_declare_var(&format!("{prefix}_b2"), Sort::Bool)
        .expect("c");
    let d = encoder
        .get_or_declare_var(&format!("{prefix}_b3"), Sort::Bool)
        .expect("d");

    let ab_neq = encoder.solver.neq(a, b);
    let cd_neq = encoder.solver.neq(c, d);
    encoder.solver.assert_term(ab_neq);
    encoder.solver.assert_term(cd_neq);
    encoder
}

/// With a bounded pass count of 1, the deterministic two-pass Bool fixture
/// must return `Unknown` because the first pass adds new neq constraints but
/// cannot reach fixpoint before the safety bound is exhausted.
///
/// Re: #901 — exhausted_bound recheck path coverage
#[test]
#[timeout(30000)]
fn recheck_exhausted_bound_returns_unknown() {
    let mut encoder = build_two_pass_bool_recheck_encoder("__exh2");
    let result = encoder.check_sat_with_quantified_disjoint_recheck_bounded(1);
    assert!(
        matches!(result, SolveResult::Unknown),
        "one-pass recheck must exhaust the safety bound and return Unknown, got {result:?}"
    );
}

/// With the full bound (10 passes), the same deterministic two-pass fixture
/// must converge to `Unsat`.
///
/// Re: #901 — full-bound convergence
#[test]
#[timeout(30000)]
fn recheck_full_bound_pigeonhole_unsat() {
    let mut encoder = build_two_pass_bool_recheck_encoder("__exh3");
    let full_result = encoder.check_sat_with_quantified_disjoint_recheck();
    assert!(
        matches!(full_result, SolveResult::Unsat(_)),
        "two-pass Bool recheck fixture must be Unsat with full bound, got {full_result:?}"
    );
}

/// Revision sync after successful recheck: when the recheck loop completes
/// with a non-Unknown result (Unsat from collision detection), the revision
/// must be synchronized so subsequent check_sat calls skip the recheck.
///
/// Re: #2354 — guard sync_pairs_revision on result != Unknown
#[test]
#[timeout(30000)]
fn recheck_unsat_syncs_revision() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let left = encoder
        .get_or_declare_var("__sync_unsat_left", Sort::Int)
        .expect("left term should declare");
    let right = encoder
        .get_or_declare_var("__sync_unsat_right", Sort::Int)
        .expect("right term should declare");

    encoder
        .assertion_pipeline
        .push_active_disjoint_constraint_for_test(vec![left], vec![right]);
    encoder
        .assertion_pipeline
        .insert_disjoint_term_for_test(left);
    encoder
        .assertion_pipeline
        .insert_disjoint_term_for_test(right);
    encoder.assertion_pipeline.prime_recheck_for_test();

    // Force collision: left == right makes the disjointness check fail.
    let forced_alias = encoder.solver.eq(left, right);
    encoder.solver.assert_term(forced_alias);

    let pre_revision = encoder.assertion_pipeline.quantified_pairs_revision();
    let result = encoder.check_sat_with_quantified_disjoint_recheck();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "forced alias must yield Unsat after recheck, got {result:?}"
    );
    assert!(
        encoder.assertion_pipeline.quantified_pairs_revision() > pre_revision,
        "Unsat recheck must sync revision (pre={pre_revision}, post={})",
        encoder.assertion_pipeline.quantified_pairs_revision()
    );
    assert!(
        !encoder.assertion_pipeline.needs_disjoint_recheck(),
        "after Unsat recheck, needs_disjoint_recheck should be false"
    );
}
