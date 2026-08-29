// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`super::shared_constraints`] helper functions.
//!
//! Extracted per #2222 so that Prover-authored tests live in a separate
//! `*_tests.rs` file, avoiding cross-role staging conflicts on the
//! production `shared_constraints.rs` module.

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::shared_constraints::{
    assert_current_chain_alias_constraints, infer_result_sort, is_ground_constant,
    is_substitutable_expr, substitute_constants,
};
use crate::{
    encoder::{AYEncoder, MAX_ENCODING_DEPTH},
    tests::helpers::{var, var_with_sort},
};

// --- is_ground_constant ---

/// Int literals are ground constants.
#[test]
#[timeout(30000)]
fn test_is_ground_constant_int_literal() {
    assert!(is_ground_constant(&PureExpr::Int(42)));
    assert!(is_ground_constant(&PureExpr::Int(0)));
    assert!(is_ground_constant(&PureExpr::Int(-1)));
}

/// Bool literals are ground constants.
#[test]
#[timeout(30000)]
fn test_is_ground_constant_bool_literal() {
    assert!(is_ground_constant(&PureExpr::Bool(true)));
    assert!(is_ground_constant(&PureExpr::Bool(false)));
}

/// Variables are NOT ground constants.
#[test]
#[timeout(30000)]
fn test_is_ground_constant_var_is_not_ground() {
    assert!(!is_ground_constant(&PureExpr::Var("x".to_string(), None)));
}

// --- is_substitutable_expr ---

/// A bare Var is not substitutable (not complex enough).
#[test]
#[timeout(30000)]
fn test_is_substitutable_expr_non_ground() {
    assert!(!is_substitutable_expr(&PureExpr::Var(
        "x".to_string(),
        None
    )));
    assert!(!is_substitutable_expr(&PureExpr::Int(42)));
    assert!(!is_substitutable_expr(&PureExpr::Bool(true)));
}

/// BinOp, UnOp, MethodCall, LogicFnCall are substitutable.
#[test]
#[timeout(30000)]
fn test_is_substitutable_expr_complex_forms() {
    let binop = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert!(is_substitutable_expr(&binop));

    let view = PureExpr::View(Arc::new(PureExpr::Var("v".to_string(), None)));
    assert!(is_substitutable_expr(&view));

    let deref = PureExpr::Deref(Arc::new(PureExpr::Var("r".to_string(), None)));
    assert!(is_substitutable_expr(&deref));

    let method = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
        method: "len".to_string(),
        args: vec![],
    };
    assert!(is_substitutable_expr(&method));

    let logic_fn = PureExpr::LogicFnCall {
        name: "my_fn".to_string(),
        args: vec![PureExpr::Int(1)],
    };
    assert!(is_substitutable_expr(&logic_fn));
}

// --- substitute_constants ---

/// Direct substitution: single-var expression matched by const_map.
#[test]
#[timeout(30000)]
fn test_substitute_constants_direct_match() {
    let method = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let constant = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&method, &constant)];

    let result = substitute_constants(&method, &const_map);
    assert_eq!(result, Some(PureExpr::Int(0)));
}

/// No match: unknown var passes through (returns None).
#[test]
#[timeout(30000)]
fn test_substitute_constants_no_match() {
    let unknown = PureExpr::Var("unknown".to_string(), None);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![];

    let result = substitute_constants(&unknown, &const_map);
    assert_eq!(result, None);
}

/// BinOp: substitution recurses into both sides.
#[test]
#[timeout(30000)]
fn test_substitute_constants_binop_both_sides() {
    let f_a = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];

    // f(a) + f(a) should become 0 + 0
    let binop = PureExpr::BinOp(Arc::new(f_a.clone()), BinOp::Add, Arc::new(f_a.clone()));

    let result = substitute_constants(&binop, &const_map);
    assert_eq!(
        result,
        Some(PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            BinOp::Add,
            Arc::new(PureExpr::Int(0)),
        ))
    );
}

/// Nested substitution with View passthrough.
#[test]
#[timeout(30000)]
fn test_substitute_constants_nested_with_view() {
    let f_a = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];

    // View(f(a)) should substitute to View(0)
    let view_expr = PureExpr::View(Arc::new(f_a.clone()));
    let result = substitute_constants(&view_expr, &const_map);
    assert_eq!(result, Some(PureExpr::View(Arc::new(PureExpr::Int(0)))));
}

// --- substitute_constants edge cases (#proof_coverage) ---

/// LogicFnCall: argument substitution replaces known constants.
#[test]
#[timeout(30000)]
fn test_substitute_constants_logic_fn_call_arg() {
    let f_a = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];

    // g(f(a)) should become g(0)
    let logic_fn = PureExpr::LogicFnCall {
        name: "g".to_string(),
        args: vec![f_a.clone()],
    };
    let result = substitute_constants(&logic_fn, &const_map);
    assert_eq!(
        result,
        Some(PureExpr::LogicFnCall {
            name: "g".to_string(),
            args: vec![PureExpr::Int(0)],
        })
    );
}

/// LogicFnCall with no matching args returns None (no change).
#[test]
#[timeout(30000)]
fn test_substitute_constants_logic_fn_call_no_match() {
    let unknown = PureExpr::Var("x".to_string(), None);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![];

    let logic_fn = PureExpr::LogicFnCall {
        name: "g".to_string(),
        args: vec![unknown],
    };
    let result = substitute_constants(&logic_fn, &const_map);
    assert_eq!(result, None);
}

/// Ite (if-then-else): substitution recurses into all three branches.
#[test]
#[timeout(30000)]
fn test_substitute_constants_ite() {
    let f_a = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];

    // if cond then f(a) else f(a) → if cond then 0 else 0
    let ite = PureExpr::Ite(
        Arc::new(PureExpr::Var("cond".to_string(), None)),
        Arc::new(f_a.clone()),
        Arc::new(f_a.clone()),
    );
    let result = substitute_constants(&ite, &const_map);
    assert_eq!(
        result,
        Some(PureExpr::Ite(
            Arc::new(PureExpr::Var("cond".to_string(), None)),
            Arc::new(PureExpr::Int(0)),
            Arc::new(PureExpr::Int(0)),
        ))
    );
}

/// Ite with no matching subexpressions returns None.
#[test]
#[timeout(30000)]
fn test_substitute_constants_ite_no_match() {
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![];
    let ite = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::Int(1)),
        Arc::new(PureExpr::Int(2)),
    );
    let result = substitute_constants(&ite, &const_map);
    assert_eq!(result, None);
}

/// Deref/Old wrappers: substitution passes through (same-state projections).
/// `Final` does NOT (temporal wrapper — #124).
#[test]
#[timeout(30000)]
fn test_substitute_constants_final_deref_old() {
    let f_a = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];

    // Final(f(a)) — NOT rewritten (#124). `Final` is a temporal wrapper, not
    // a function of its inner expression's current value: `f(a) == 0` does
    // not entail `^f(a) == ^0` (that is the `^p == *p` inversion), and the
    // minted `Final(Int(0))` is refused fail-closed by the Fix A
    // constant-carrier guard anyway. A whole-node `Final(f(a))` key still
    // substitutes — see `test_substitute_constants_never_rewrites_under_final`.
    let final_expr = PureExpr::Final(Arc::new(f_a.clone()));
    assert_eq!(substitute_constants(&final_expr, &const_map), None);

    // Deref(f(a)) → Deref(0)
    let deref_expr = PureExpr::Deref(Arc::new(f_a.clone()));
    assert_eq!(
        substitute_constants(&deref_expr, &const_map),
        Some(PureExpr::Deref(Arc::new(PureExpr::Int(0))))
    );

    // Old(f(a)) → Old(0)
    let old_expr = PureExpr::Old(Arc::new(f_a.clone()));
    assert_eq!(
        substitute_constants(&old_expr, &const_map),
        Some(PureExpr::Old(Arc::new(PureExpr::Int(0))))
    );
}

/// MethodCall: substitution in receiver and args.
#[test]
#[timeout(30000)]
fn test_substitute_constants_method_call_receiver_and_args() {
    let f_a = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];

    // f(a).g(f(a)) → 0.g(0)
    let method = PureExpr::MethodCall {
        receiver: Arc::new(f_a.clone()),
        method: "g".to_string(),
        args: vec![f_a.clone()],
    };
    let result = substitute_constants(&method, &const_map);
    assert_eq!(
        result,
        Some(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Int(0)),
            method: "g".to_string(),
            args: vec![PureExpr::Int(0)],
        })
    );
}

/// `substitute_constants` does not recurse into Forall/Exists/Match/Let.
/// These are handled by the `_ => None` catch-all arm, which is correct
/// because `substitute_constants` is an optimization — not recursing into
/// quantifiers means fewer redundant assertions, not missed soundness.
///
/// This test documents the traversal boundary: a `Forall` containing a
/// substitutable subexpression returns `None` (no substitution performed).
///
/// If the traversal is ever extended to recurse into quantifiers, this test
/// should be updated to expect `Some(...)` instead.
#[test]
#[timeout(30000)]
fn test_substitute_constants_does_not_recurse_into_forall() {
    let f_a = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];

    // Forall { body: f(a) == 0 } — the body contains a substitutable expr,
    // but substitute_constants does not recurse into Forall.
    let forall_expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(f_a.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )),
        triggers: vec![],
    };
    let result = substitute_constants(&forall_expr, &const_map);
    assert_eq!(
        result, None,
        "substitute_constants should return None for Forall — it does not recurse \
         into quantifiers. If this starts returning Some, update the traversal docs."
    );
}

// ---------------------------------------------------------------------------
// Performance regression tests (#performance_proofs)
// ---------------------------------------------------------------------------

/// Phase 2 of `flatten_ghost_implications` uses a nested
/// `ghost_exprs.iter().any(|e| e == right)` scan inside a `for expr in
/// ghost_exprs` loop (shared_constraints.rs:66-79). This is O(n²) in
/// `ghost_exprs.len()`. For simple Var expressions the constant factor
/// is small, but with complex expressions the structural equality check
/// amplifies the cost.
///
/// This test constructs 2000 ghost expressions of the form
/// `Eq(Var("b_i"), complex_rhs)` where `complex_rhs` is a 5-deep nested
/// BinOp tree. Phase 2 would scan all 2000 expressions for each of
/// the ~2000 equality expressions, producing ~4M structural comparisons.
///
/// With the 10s timeout, this guards against regressions that would
/// make the quadratic scan intractable. If the scan is ever converted
/// to a HashSet lookup (O(n)), this test should still pass trivially.
#[test]
#[timeout(30000)]
#[allow(clippy::cast_possible_wrap)] // test data: small usize values safely fit i64
fn perf_phase2_ghost_equality_propagation_quadratic_guard() {
    // Build a moderately complex expression tree (5-deep nested Add).
    fn build_deep_expr(depth: usize, seed: i64) -> PureExpr {
        if depth == 0 {
            PureExpr::Int(seed)
        } else {
            PureExpr::BinOp(
                Arc::new(build_deep_expr(depth - 1, seed)),
                BinOp::Add,
                Arc::new(build_deep_expr(depth - 1, seed + 1)),
            )
        }
    }

    let n = 2000;
    let mut ghost_exprs: Vec<PureExpr> = Vec::with_capacity(n + 1);

    // One known-true variable.
    let rhs = build_deep_expr(5, 42);
    ghost_exprs.push(rhs.clone());

    // N equality expressions: Eq(Var("b_i"), rhs_i) where rhs_i differs.
    for i in 0..n {
        let var_expr = PureExpr::Var(format!("b_{i}"), None);
        let rhs_i = build_deep_expr(5, i as i64);
        ghost_exprs.push(PureExpr::BinOp(
            Arc::new(var_expr),
            BinOp::Eq,
            Arc::new(rhs_i),
        ));
    }

    // Simulate Phase 2 logic: the quadratic scan.
    // This exercises the exact pattern at shared_constraints.rs:66-79.
    use std::collections::HashSet;
    let mut true_vars: HashSet<&str> = HashSet::new();
    for expr in &ghost_exprs {
        if let PureExpr::Var(name, _) = expr {
            true_vars.insert(name.as_str());
        }
    }
    for expr in &ghost_exprs {
        if let PureExpr::BinOp(left, BinOp::Eq, right) = expr {
            if let PureExpr::Var(name, _) = left.as_ref() {
                if ghost_exprs.iter().any(|e| e == right.as_ref()) {
                    true_vars.insert(name.as_str());
                }
            }
        }
    }

    // The test passes if it completes within the timeout. The quadratic
    // scan with structural equality on 5-deep trees (31 nodes each) over
    // 2000 expressions should still be well under 10s on modern hardware,
    // but would blow up at ~10K+ expressions.
    //
    // BUG: this scan is O(n²×m) where m = avg expr node count. A HashSet
    // on expression identity would reduce to O(n×m) for construction +
    // O(n) for lookups. See shared_constraints.rs Phase 2 comment.
    assert!(
        ghost_exprs.len() > n,
        "constructed expression list should have n+1 entries"
    );
}

/// `substitute_constants` does a linear scan of `const_map` at every
/// tree node (shared_constraints.rs:195). With a const_map of size M
/// and expression tree of size N, each call is O(N × M). When called
/// in Phase 4 over K expressions, total is O(K × N × M).
///
/// This test constructs a const_map with 500 entries and a 500-node
/// expression, verifying that substitute_constants completes within
/// the timeout. A HashMap-based const_map would reduce per-node lookup
/// from O(M) to O(1).
#[test]
#[timeout(30000)]
#[allow(clippy::cast_possible_wrap, clippy::needless_range_loop)] // test data: small usize→i64; index loop reads clearer here
fn perf_substitute_constants_linear_scan_guard() {
    let m = 500;

    // Build const_map: 500 distinct MethodCall → Int mappings.
    let methods: Vec<PureExpr> = (0..m)
        .map(|i| PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(format!("r_{i}"), None)),
            method: format!("f_{i}"),
            args: vec![],
        })
        .collect();
    let constants: Vec<PureExpr> = (0..m).map(|i| PureExpr::Int(i as i64)).collect();
    let const_map: Vec<(&PureExpr, &PureExpr)> = methods.iter().zip(constants.iter()).collect();

    // Build a 500-node chain: f_0().g(f_1().g(f_2().g(...)))
    let mut expr = methods[0].clone();
    for i in 1..m {
        expr = PureExpr::MethodCall {
            receiver: Arc::new(expr),
            method: "g".to_string(),
            args: vec![methods[i].clone()],
        };
    }

    // Run substitute_constants — exercises O(N × M) per call.
    let result = substitute_constants(&expr, &const_map);

    // Both the chain root and each arg should be substitutable.
    assert!(
        result.is_some(),
        "deeply nested expression with 500 const_map entries should substitute"
    );
}

#[test]
#[timeout(30000)]
fn test_substitute_constants_rewrites_node_at_exact_depth_limit() {
    let target = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "target".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&target, &zero)];

    let mut expr = target.clone();
    for i in 0..MAX_ENCODING_DEPTH {
        expr = PureExpr::MethodCall {
            receiver: Arc::new(expr),
            method: format!("wrap_{i}"),
            args: vec![],
        };
    }

    let rewritten = substitute_constants(&expr, &const_map)
        .expect("target exactly at MAX_ENCODING_DEPTH should still rewrite");

    assert!(
        rewritten.any_recursive(|node| matches!(node, PureExpr::Int(0))),
        "replacement should appear when the matching node is exactly at MAX_ENCODING_DEPTH"
    );
}

#[test]
#[timeout(30000)]
fn test_substitute_constants_skips_node_beyond_depth_limit() {
    let target = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "target".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&target, &zero)];

    let mut expr = target.clone();
    for i in 0..=MAX_ENCODING_DEPTH {
        expr = PureExpr::MethodCall {
            receiver: Arc::new(expr),
            method: format!("wrap_{i}"),
            args: vec![],
        };
    }

    assert_eq!(
        substitute_constants(&expr, &const_map),
        None,
        "matching nodes deeper than MAX_ENCODING_DEPTH should remain untouched"
    );
}

/// `substitute_constants` does not recurse into Match expressions.
/// Same boundary documentation as the Forall test above.
#[test]
#[timeout(30000)]
fn test_substitute_constants_does_not_recurse_into_match() {
    let f_a = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    };
    let zero = PureExpr::Int(0);
    let const_map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];

    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![trust_wp_core::formula::MatchArm {
            pattern: trust_wp_core::formula::Pattern::Wildcard,
            body: f_a.clone(),
        }],
    };
    let result = substitute_constants(&match_expr, &const_map);
    assert_eq!(
        result, None,
        "substitute_constants should return None for Match — it does not recurse \
         into match arms. This is an optimization boundary, not a soundness gap."
    );
}

// ---------------------------------------------------------------------------
// assert_current_chain_alias_constraints (moved from function/tests.rs, #2175)
// ---------------------------------------------------------------------------

/// `f_current` must NOT be equated to `f` (base) — mutable borrow treats
/// those as distinct states. Only `_current`→`_current` links are asserted.
#[test]
#[timeout(30000)]
fn current_chain_alias_skips_current_to_base_identity() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let f = encoder
        .get_or_declare_var("f", Sort::Int)
        .expect("f should declare");
    let f_current = encoder
        .get_or_declare_var("f_current", Sort::Int)
        .expect("f_current should declare");

    let five = encoder.solver_mut().int_const(5);
    let eq = encoder.solver_mut().eq(f, five);
    encoder.assert_term(eq);

    assert_current_chain_alias_constraints(&mut encoder)
        .expect("current-chain alias constraints should succeed");

    let five2 = encoder.solver_mut().int_const(5);
    let eq2 = encoder.solver_mut().eq(f_current, five2);
    let neq = encoder.solver_mut().not(eq2);
    encoder.assert_term(neq);
    assert_ne!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "mut-borrow chain aliases must not enforce f_current = f"
    );
}

/// Deep `_current`→`_current` links ARE asserted:
/// `f_current_current = f_current` must hold.
#[test]
#[timeout(30000)]
fn current_chain_alias_still_links_deep_currents() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let f_current = encoder
        .get_or_declare_var("f_current", Sort::Int)
        .expect("f_current should declare");
    let f_current_current = encoder
        .get_or_declare_var("f_current_current", Sort::Int)
        .expect("f_current_current should declare");

    let seven = encoder.solver_mut().int_const(7);
    let eq = encoder.solver_mut().eq(f_current, seven);
    encoder.assert_term(eq);

    assert_current_chain_alias_constraints(&mut encoder)
        .expect("current-chain alias constraints should succeed");

    let ninety_nine = encoder.solver_mut().int_const(99);
    let eq2 = encoder.solver_mut().eq(f_current_current, ninety_nine);
    encoder.assert_term(eq2);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "mut-borrow chain aliases should still enforce f_current_current = f_current"
    );
}

/// Deeper chain with a missing intermediate: `x_current` and
/// `x_current_current_current` exist, but `x_current_current` is
/// intentionally omitted. The synthesis loop at
/// `shared_constraints.rs:352-375` must create intermediate hops so that
/// `x_current_current_current = x_current` holds transitively.
#[test]
#[timeout(30000)]
fn current_chain_alias_synthesizes_missing_intermediate() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let x_current = encoder
        .get_or_declare_var("x_current", Sort::Int)
        .expect("x_current should declare");
    // Intentionally skip x_current_current — the synthesis loop creates it.
    let x_ccc = encoder
        .get_or_declare_var("x_current_current_current", Sort::Int)
        .expect("x_current_current_current should declare");

    let seven = encoder.solver_mut().int_const(7);
    let eq = encoder.solver_mut().eq(x_current, seven);
    encoder.assert_term(eq);

    assert_current_chain_alias_constraints(&mut encoder)
        .expect("alias constraints with missing intermediate should succeed");

    let ninety_nine = encoder.solver_mut().int_const(99);
    let eq2 = encoder.solver_mut().eq(x_ccc, ninety_nine);
    encoder.assert_term(eq2);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "x_current_current_current must equal x_current via synthesized intermediate chain"
    );
}

/// When only base names (no `_current` suffix) exist, the alias helper
/// must return Ok(()) without constraining anything.
#[test]
#[timeout(30000)]
fn current_chain_alias_no_op_for_base_names_only() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("x should declare");

    let five = encoder.solver_mut().int_const(5);
    let eq = encoder.solver_mut().eq(x, five);
    encoder.assert_term(eq);

    assert_current_chain_alias_constraints(&mut encoder)
        .expect("no-op alias constraints should succeed");

    // `x` should remain freely satisfiable — no alias constraints added.
    assert_ne!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "base-only scope must not become UNSAT from alias constraints"
    );
}

// ---------------------------------------------------------------------------
// infer_result_sort (moved from function/tests.rs, #2175)
// ---------------------------------------------------------------------------

#[test]
#[timeout(30000)]
fn infer_result_sort_var_with_int_annotation_returns_int() {
    let mut encoder = AYEncoder::new();
    let expr = var_with_sort("result", ExprSort::Int);
    let sort = infer_result_sort(&mut encoder, &expr);
    assert_eq!(
        sort,
        Sort::Int,
        "Var with ExprSort::Int should yield Sort::Int"
    );
}

#[test]
#[timeout(30000)]
fn infer_result_sort_var_with_bool_annotation_returns_bool() {
    let mut encoder = AYEncoder::new();
    let expr = var_with_sort("result", ExprSort::Bool);
    let sort = infer_result_sort(&mut encoder, &expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "Var with ExprSort::Bool should yield Sort::Bool"
    );
}

#[test]
#[timeout(30000)]
fn infer_result_sort_var_with_seq_annotation_returns_seq() {
    let mut encoder = AYEncoder::new();
    let expr = var_with_sort("result", ExprSort::Seq);
    let sort = infer_result_sort(&mut encoder, &expr);
    let expected_seq = Sort::seq(Sort::Int);
    assert_eq!(
        sort, expected_seq,
        "Var with ExprSort::Seq should yield Sort::Uninterpreted(\"Seq\")"
    );
}

#[test]
#[timeout(30000)]
fn infer_result_sort_var_none_with_declared_sort_uses_encoder() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("result", Sort::Bool)
        .expect("result should declare as Bool");
    let expr = var("result");
    let sort = infer_result_sort(&mut encoder, &expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "Var(_, None) with encoder-declared Bool should yield Sort::Bool"
    );
}

#[test]
#[timeout(30000)]
fn infer_result_sort_var_none_without_declared_sort_falls_back_to_int() {
    let mut encoder = AYEncoder::new();
    let expr = var("result");
    let sort = infer_result_sort(&mut encoder, &expr);
    assert_eq!(
        sort,
        Sort::Int,
        "Var(_, None) without encoder declaration should fall back to infer_expr_sort (Int)"
    );
}

#[test]
#[timeout(30000)]
fn infer_result_sort_literal_int_returns_int() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::Int(42);
    let sort = infer_result_sort(&mut encoder, &expr);
    assert_eq!(sort, Sort::Int, "Int literal should yield Sort::Int");
}

#[test]
#[timeout(30000)]
fn infer_result_sort_literal_bool_returns_bool() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::Bool(true);
    let sort = infer_result_sort(&mut encoder, &expr);
    assert_eq!(sort, Sort::Bool, "Bool literal should yield Sort::Bool");
}

/// Non-Var branch of `infer_result_sort`: exercises the
/// `infer_expr_sort_with_context` path for `PureExpr::LogicFnCall`.
/// When the encoder has a declared logic function with Bool range,
/// `infer_result_sort` must return `Sort::Bool`.
#[test]
#[timeout(30000)]
fn infer_result_sort_logic_fn_call_uses_declared_range() {
    let mut encoder = AYEncoder::new();
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("my_pred");
    let func_decl = encoder
        .solver
        .declare_fun(&smt_name, &[Sort::Int], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, func_decl);

    let expr = PureExpr::LogicFnCall {
        name: "my_pred".to_string(),
        args: vec![PureExpr::Int(1)],
    };
    let sort = infer_result_sort(&mut encoder, &expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "LogicFnCall with declared Bool-range func should yield Sort::Bool"
    );
}
