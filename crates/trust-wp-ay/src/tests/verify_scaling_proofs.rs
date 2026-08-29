// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(clippy::cast_possible_wrap)] // Test-only: loop counters safely fit in i64

//! Performance scaling proofs for verify-side algorithmic hotspots (#901).
//!
//! These tests exercise quadratic-risk code paths in the verification pipeline
//! that are NOT covered by the encoder-side scaling tests in
//! `performance_proofs.rs`, `performance_hotspot_proofs.rs`, or
//! `solver_axiom_scaling.rs`.
//!
//! ## Hotspots tested:
//!
//! 1. **`collect_constructor_datatype_candidates` O(T²)** — calls
//!    `expr_contains_result_var` (O(T) tree walk) at each BinOp(Eq/Ne) node
//!    during another O(T) tree walk. Deep equality chains could cause
//!    quadratic blowup in postcondition analysis.
//!
//! 2. **`flatten_ghost_implications` O(G²×T)** — Phase 2 equality propagation
//!    scans `ghost_exprs` inside a loop over `ghost_exprs`. Phase 4 const_map
//!    building does a linear scan of `const_map` per expression. Both are
//!    quadratic in ghost expression count. Phase 4 `substitute_constants`
//!    traversal is O(T×K) per expression (T = tree depth, K = const_map size).
//!    Both dimensions are tested independently: tree-depth (3b) and
//!    const_map size (3c).
//!
//! 3. **`result_is_bool_by_postcondition` / `expr_requires_result_bool`** —
//!    called per postcondition with `expr_contains_result_var` sub-calls.
//!    Scaling with postcondition count and expression depth.
//!
//! 4. **`substitute_vars_in_expr` co-growing depth/map bound** — the wrapper
//!    now delegates to the shared overlay-based substitution engine, but when
//!    depth d and map size s grow together (d ≈ s ≈ n), total work should
//!    still stay within an O(n²) bound. Tests prove that quadratic ceiling.
//!
//! 5. **`try_match_expr` O(T×b)** — `bound_vars.contains()` does O(b) linear
//!    scan at each Var node during recursive tree walk. Tests prove the bound.

use std::{collections::HashMap, sync::Arc, time::Instant};

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::helpers::{eq, int, logic_fn_call, var};
use crate::{
    encoder::AYEncoder,
    verify::{
        expr_contains_result_var, flatten_ghost_implications,
        result_match_datatype_from_postcondition, substitute_vars_in_expr, try_match_expr,
    },
};
mod result_inference;

fn run_with_large_stack(f: impl FnOnce() + Send + 'static) {
    let handle = std::thread::Builder::new()
        .name("verify_scaling_large_stack".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("large-stack scaling test worker should spawn");
    if let Err(payload) = handle.join() {
        std::panic::resume_unwind(payload);
    }
}

// ---------------------------------------------------------------------------
// Helpers: build deeply nested PureExpr trees
// ---------------------------------------------------------------------------

/// Build a left-recursive chain of `Eq(... Eq(Eq(result, Some(0)), Some(1)), Some(n-1))`.
///
/// Each level adds one BinOp(Eq) node with `result` on one side and a
/// `LogicFnCall("Some", [Int(i)])` constructor on the other. This creates
/// an AST with O(n) Eq nodes where `collect_constructor_datatype_candidates`
/// must call `expr_contains_result_var` at each level.
fn build_nested_eq_chain(n: usize) -> PureExpr {
    let mut expr = eq(var("result"), logic_fn_call("Some", vec![int(0)]));
    for i in 1..n {
        expr = eq(expr, logic_fn_call("Some", vec![int(i as i64)]));
    }
    expr
}

/// Build a right-recursive chain: `Eq(Some(0), Eq(Some(1), ... Eq(Some(n-1), result)))`.
fn build_nested_eq_chain_right(n: usize) -> PureExpr {
    let mut expr = eq(
        logic_fn_call("Some", vec![int((n - 1) as i64)]),
        var("result"),
    );
    for i in (0..n - 1).rev() {
        expr = eq(logic_fn_call("Some", vec![int(i as i64)]), expr);
    }
    expr
}

/// Build a flat conjunction of independent `result == Some(i)` equalities
/// connected by And: `(result == Some(0)) && (result == Some(1)) && ...`.
///
/// This tests the non-nested case where `expr_contains_result_var` is called
/// for each equality but doesn't need deep tree traversal.
fn build_flat_eq_conjunction(n: usize) -> PureExpr {
    let mut expr = eq(var("result"), logic_fn_call("Some", vec![int(0)]));
    for i in 1..n {
        let next_eq = eq(var("result"), logic_fn_call("Some", vec![int(i as i64)]));
        expr = PureExpr::BinOp(Arc::new(expr), BinOp::And, Arc::new(next_eq));
    }
    expr
}

// ---------------------------------------------------------------------------
// 2. expr_contains_result_var scaling (pure tree walk)
// ---------------------------------------------------------------------------

/// Build a balanced binary tree with NO `result` variable (worst case for
/// `expr_contains_result_var` which must traverse the entire tree).
fn build_deep_tree_without_result(depth: usize) -> PureExpr {
    if depth == 0 {
        var("x")
    } else {
        PureExpr::BinOp(
            Arc::new(build_deep_tree_without_result(depth - 1)),
            BinOp::Add,
            Arc::new(int(depth as i64)),
        )
    }
}

fn measure_expr_contains_result_time(expr: &PureExpr, iters: usize) -> std::time::Duration {
    let start = Instant::now();
    for _ in 0..iters {
        let _ = expr_contains_result_var(expr);
    }
    start.elapsed()
}

/// Proves that `expr_contains_result_var` scales linearly in tree size
/// (worst case: `result` absent, must visit every node).
///
/// This is the O(T) building block used by `collect_constructor_datatype_candidates`.
/// If the base walk is superlinear, the quadratic compound would be even worse.
///
/// Re: #901 — verify/result_inference.rs tree walk baseline
#[test]
#[timeout(30000)]
fn test_expr_contains_result_var_scales_linearly() {
    // depth 8 => 2^8 = 256 nodes, depth 11 => 2^11 = 2048 nodes
    // Ratio ~8x for linear scaling.
    let small_depth = 8;
    let large_depth = 11;
    let rounds = 5;
    let iters = 5000;

    let small_expr = build_deep_tree_without_result(small_depth);
    let large_expr = build_deep_tree_without_result(large_depth);

    // Correctness gate (#2130): negative + positive cases
    assert!(
        !expr_contains_result_var(&small_expr),
        "tree without result var should be false"
    );
    let expr_with_result = PureExpr::BinOp(
        Arc::new(small_expr.clone()),
        BinOp::Add,
        Arc::new(var("result")),
    );
    assert!(
        expr_contains_result_var(&expr_with_result),
        "tree with result var should be true"
    );

    // Warm up.
    let _ = measure_expr_contains_result_time(&small_expr, iters);
    let _ = measure_expr_contains_result_time(&large_expr, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_expr_contains_result_time(&small_expr, iters);
        let large_time = measure_expr_contains_result_time(&large_expr, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(T): 2048/256 = 8x nodes. Allow up to 20x for cache effects.
    assert!(
        min_ratio < 20.0,
        "expr_contains_result_var scaling (depth {large_depth}/{small_depth}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). Expected ~8x (O(T)). \
         If > 20x, tree walk has superlinear regression."
    );

    eprintln!(
        "expr_contains_result: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(T) expect ~8x for depth={small_depth}->{large_depth})"
    );
}

// ---------------------------------------------------------------------------
// 3. flatten_ghost_implications Phase 2 + Phase 4 scaling
// ---------------------------------------------------------------------------

/// Build a ghost expression list with N equalities for Phase 2 propagation.
///
/// Structure: [Var("flag"), Eq(Var("b0"), Var("flag")), Eq(Var("b1"), Var("flag")), ...]
/// Phase 2 scans ghost_exprs for each Eq to check if the RHS is in the list.
fn build_ghost_equality_chain(n: usize) -> Vec<PureExpr> {
    let mut exprs = Vec::with_capacity(n + 1);
    exprs.push(var("flag"));
    for i in 0..n {
        exprs.push(eq(var(&format!("b{i}")), var("flag")));
    }
    exprs
}

/// Build a ghost expression list with N UF equalities for Phase 4 const_map.
///
/// Structure: [f0(a) == 0, f1(a) == 1, ..., f(n-1)(a) == n-1]
/// Phase 4 builds a const_map with linear dedup scan per entry.
fn build_ghost_const_map_chain(n: usize) -> Vec<PureExpr> {
    (0..n)
        .map(|i| {
            eq(
                logic_fn_call(&format!("uf_{i}"), vec![var("a")]),
                int(i as i64),
            )
        })
        .collect()
}

fn measure_flatten_time(ghost_exprs: &[PureExpr], iters: usize) -> std::time::Duration {
    let start = Instant::now();
    for _ in 0..iters {
        let mut encoder = AYEncoder::new_with_quantifiers();
        // Pre-declare UFs so encode_pure doesn't fail on unknown logic fns.
        for expr in ghost_exprs {
            if let PureExpr::BinOp(left, BinOp::Eq, _) = expr {
                if let PureExpr::LogicFnCall { name, .. } = left.as_ref() {
                    if !encoder.decls().has_logic_func(name) {
                        let decl = encoder.solver.declare_fun(name, &[Sort::Int], Sort::Int);
                        encoder
                            .decls_for_test_mut()
                            .insert_logic_func(name.clone(), decl);
                    }
                }
            }
            // Also declare variables
            match expr {
                PureExpr::Var(name, _) => {
                    let _ = encoder.get_or_declare_var(name, Sort::Bool);
                }
                PureExpr::BinOp(left, BinOp::Eq, _) => {
                    if let PureExpr::Var(name, _) = left.as_ref() {
                        let _ = encoder.get_or_declare_var(name, Sort::Bool);
                    }
                }
                _ => {}
            }
        }
        // Pre-declare 'a' for UF args
        let _ = encoder.get_or_declare_var("a", Sort::Int);

        let _ = flatten_ghost_implications(&mut encoder, ghost_exprs);
    }
    start.elapsed()
}

/// Proves that `flatten_ghost_implications` Phase 2 equality propagation
/// scales at most quadratically in ghost expression count.
///
/// Phase 2 iterates ghost_exprs (G) and for each Eq, scans ghost_exprs
/// again with structural equality: O(G² × T). For simple Var expressions
/// (T=1), this should be O(G²). Doubling G from 25 to 100 (4x) should
/// give at most 16x (quadratic).
///
/// Re: #901 — verify/function.rs Phase 2 equality propagation quadratic risk
#[test]
#[timeout(30000)]
fn test_flatten_phase2_equality_propagation_scaling() {
    let small_n = 25;
    let large_n = 100;
    let rounds = 5;
    let iters = 200;

    let small_exprs = build_ghost_equality_chain(small_n);
    let large_exprs = build_ghost_equality_chain(large_n);

    // Correctness gate (#2130): Phase 2 propagation + implication flattening
    {
        let mut gate_exprs = build_ghost_equality_chain(2);
        // b0 => (x > 0) — Phase 2 proves b0 true, so consequent should be asserted
        let implication = PureExpr::BinOp(
            Arc::new(var("b0")),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(var("x")),
                BinOp::Gt,
                Arc::new(int(0)),
            )),
        );
        gate_exprs.push(implication);
        let mut encoder = AYEncoder::new();
        for (n, s) in [
            ("flag", Sort::Bool),
            ("b0", Sort::Bool),
            ("b1", Sort::Bool),
            ("x", Sort::Int),
        ] {
            let _ = encoder.get_or_declare_var(n, s);
        }
        let rev_before = encoder.assertion_pipeline_for_test().assertion_revision();
        let result = flatten_ghost_implications(&mut encoder, &gate_exprs);
        assert!(result.is_ok(), "flatten should succeed: {result:?}");
        assert!(
            encoder.assertion_pipeline_for_test().assertion_revision() > rev_before,
            "Phase 2 should assert consequent when b0 is proven true"
        );
    }

    // Warm up.
    let _ = measure_flatten_time(&small_exprs, iters);
    let _ = measure_flatten_time(&large_exprs, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_flatten_time(&small_exprs, iters);
        let large_time = measure_flatten_time(&large_exprs, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(G²): 4x input → 16x. Allow up to 25x for solver/encoder overhead.
    // Cubic: 4³ = 64x — well above threshold.
    assert!(
        min_ratio < 25.0,
        "flatten Phase 2 scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ≤16x (O(G²) for 4x input). \
         If > 25x, Phase 2 has cubic or worse regression."
    );

    eprintln!(
        "flatten_phase2_eq: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(G²) expect ≤16x for G={small_n}->{large_n})"
    );
}

/// Proves that `flatten_ghost_implications` Phase 4 const_map building
/// scales at most quadratically in ghost expression count.
///
/// Phase 4 iterates ghost_exprs and for each equality, scans the
/// accumulated const_map: O(G²). Doubling G should give at most 4x for
/// the linear part and 16x for the quadratic dedup scan.
///
/// Re: #901 — verify/function.rs Phase 4 const_map quadratic risk
#[test]
#[timeout(30000)]
fn test_flatten_phase4_const_map_scaling() {
    let small_n = 25;
    let large_n = 100;
    let rounds = 3;
    let iters = 20;

    let small_exprs = build_ghost_const_map_chain(small_n);
    let large_exprs = build_ghost_const_map_chain(large_n);

    // Correctness gate (#2130): Phase 4 const propagation via transitive UF chain
    {
        // uf_0(a)==0, uf_1(a)==uf_0(a)+1 → Phase 4 substitutes to assert uf_1(a)==0+1
        let fa = logic_fn_call("uf_0", vec![var("a")]);
        let fb = logic_fn_call("uf_1", vec![var("a")]);
        let chain_exprs = vec![
            eq(fa.clone(), int(0)),
            eq(
                fb,
                PureExpr::BinOp(Arc::new(fa), BinOp::Add, Arc::new(int(1))),
            ),
        ];
        let mut encoder = AYEncoder::new_with_quantifiers();
        for name in ["uf_0", "uf_1"] {
            let decl = encoder
                .solver
                .try_declare_fun(name, &[Sort::Int], Sort::Int)
                .expect(name);
            encoder
                .decls_for_test_mut()
                .insert_logic_func(name.to_string(), decl);
        }
        let _ = encoder.get_or_declare_var("a", Sort::Int);
        let rev_before = encoder.assertion_pipeline_for_test().assertion_revision();
        let result = flatten_ghost_implications(&mut encoder, &chain_exprs);
        assert!(result.is_ok(), "Phase 4 chain should succeed: {result:?}");
        assert!(
            encoder.assertion_pipeline_for_test().assertion_revision() > rev_before,
            "Phase 4 should assert simplified form via constant substitution"
        );
    }

    // Warm up.
    let _ = measure_flatten_time(&small_exprs, iters);
    let _ = measure_flatten_time(&large_exprs, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_flatten_time(&small_exprs, iters);
        let large_time = measure_flatten_time(&large_exprs, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(G²): 4x input → 16x. Allow up to 25x for solver overhead.
    assert!(
        min_ratio < 25.0,
        "flatten Phase 4 const_map scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ≤16x (O(G²) for 4x input). \
         If > 25x, Phase 4 const_map has cubic or worse regression."
    );

    eprintln!(
        "flatten_phase4_const_map: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(G²) expect ≤16x for G={small_n}->{large_n})"
    );
}

/// Combined test: Phase 2 equalities plus Phase 4 UF const_map entries
/// in the same ghost_exprs. Validates no superlinear interaction between
/// the two quadratic passes.
///
/// Re: #901 — verify/function.rs Phase 2+4 combined scaling
#[test]
#[timeout(30000)]
fn test_flatten_combined_phase2_phase4_scaling() {
    let small_n = 20;
    let large_n = 80;
    let rounds = 3;
    let iters = 20;

    // Build: [Var("flag"), Eq(Var("b0"), Var("flag")), ..., uf_0(a) == 0, ...]
    let build_combined = |n: usize| -> Vec<PureExpr> {
        let mut exprs = build_ghost_equality_chain(n);
        exprs.extend(build_ghost_const_map_chain(n));
        exprs
    };

    let small_exprs = build_combined(small_n);
    let large_exprs = build_combined(large_n);

    // Correctness gate (#2130): combined Phase 2+4 succeeds
    {
        let gate_exprs = build_combined(3);
        let mut encoder = AYEncoder::new_with_quantifiers();
        let _ = encoder.get_or_declare_var("flag", Sort::Bool);
        for i in 0..3 {
            let _ = encoder.get_or_declare_var(&format!("b{i}"), Sort::Bool);
        }
        let _ = encoder.get_or_declare_var("a", Sort::Int);
        for i in 0..3 {
            let decl = encoder
                .solver
                .try_declare_fun(&format!("uf_{i}"), &[Sort::Int], Sort::Int)
                .expect("declare UF");
            encoder
                .decls_for_test_mut()
                .insert_logic_func(format!("uf_{i}"), decl);
        }
        let rev_before = encoder.assertion_pipeline_for_test().assertion_revision();
        let result = flatten_ghost_implications(&mut encoder, &gate_exprs);
        assert!(
            result.is_ok(),
            "combined Phase 2+4 should succeed: {result:?}"
        );
        assert!(
            encoder.assertion_pipeline_for_test().assertion_revision() > rev_before,
            "combined Phase 2+4 should assert from equality propagation and/or const substitution"
        );
    }

    // Warm up.
    let _ = measure_flatten_time(&small_exprs, iters);
    let _ = measure_flatten_time(&large_exprs, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_flatten_time(&small_exprs, iters);
        let large_time = measure_flatten_time(&large_exprs, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // Combined: 2G expressions, each pass is O(G²). Total O(G²).
    // 4x input → 16x. Allow 30x for two-pass + solver overhead.
    assert!(
        min_ratio < 30.0,
        "flatten combined Phase 2+4 scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ≤16x (O(G²) for 4x input). \
         If > 30x, combined phases have superquadratic interaction."
    );

    eprintln!(
        "flatten_combined: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(G²) expect ≤16x for G={small_n}->{large_n})"
    );
}

// ---------------------------------------------------------------------------
// 3b. flatten_ghost_implications Phase 4: substitute_constants tree-depth scaling
// ---------------------------------------------------------------------------

/// Build a ghost expression list with a fixed const_map (K entries) and
/// one deeply nested expression of depth T.
///
/// Structure:
///   [uf_0(a) == 0, uf_1(a) == 1, ..., uf_{K-1}(a) == K-1,   // K const_map entries
///    (uf_0(a) + (uf_1(a) + (... + uf_0(a) + ...))) > 0]       // nested tree of depth T
///
/// Phase 4 collects the K equalities into const_map, then substitute_constants
/// recursively walks the depth-T expression. At each node, it scans const_map
/// (O(K) linear scan). Total cost: O(T × K). With K fixed, this should be O(T).
fn build_ghost_deep_tree_chain(const_map_size: usize, tree_depth: usize) -> Vec<PureExpr> {
    let mut exprs = Vec::with_capacity(const_map_size + 1);
    // K const_map entries
    for i in 0..const_map_size {
        exprs.push(eq(
            logic_fn_call(&format!("uf_{i}"), vec![var("a")]),
            int(i as i64),
        ));
    }
    // Build a deeply nested BinOp tree of depth T.
    // Each leaf is a uf_i(a) call that matches a const_map entry,
    // so substitute_constants must recurse through the entire tree.
    let mut tree = logic_fn_call("uf_0", vec![var("a")]);
    for d in 1..tree_depth {
        let leaf = logic_fn_call(&format!("uf_{}", d % const_map_size), vec![var("a")]);
        tree = PureExpr::BinOp(Arc::new(tree), BinOp::Add, Arc::new(leaf));
    }
    // Wrap in a comparison to make it a substitutable ghost expression
    exprs.push(PureExpr::BinOp(Arc::new(tree), BinOp::Gt, Arc::new(int(0))));
    exprs
}

fn measure_flatten_deep_tree_time(
    const_map_size: usize,
    tree_depth: usize,
    iters: usize,
) -> std::time::Duration {
    let exprs = build_ghost_deep_tree_chain(const_map_size, tree_depth);
    let start = Instant::now();
    for _ in 0..iters {
        let mut encoder = AYEncoder::new_with_quantifiers();
        // Pre-declare UFs
        for i in 0..const_map_size {
            let name = format!("uf_{i}");
            if !encoder.decls().has_logic_func(&name) {
                let decl = encoder.solver.declare_fun(&name, &[Sort::Int], Sort::Int);
                encoder.decls_for_test_mut().insert_logic_func(name, decl);
            }
        }
        let _ = encoder.get_or_declare_var("a", Sort::Int);
        let _ = flatten_ghost_implications(&mut encoder, &exprs);
    }
    start.elapsed()
}

/// Proves that `flatten_ghost_implications` Phase 4 substitute_constants
/// scales linearly in expression tree depth when const_map size is fixed.
///
/// `substitute_constants` recursively walks the expression tree (O(T) nodes).
/// At each node, it scans const_map with `.iter().find()` (O(K)).
/// Total: O(T × K). With K fixed at 5, this should be O(T).
///
/// Scales T from 50 to 400 (8x) and expects at most 16x (linear with overhead).
/// A quadratic regression (O(T²)) from accidental re-traversal would show ~64x.
///
/// Re: #901 — substitute_constants tree-depth dimension
#[test]
#[timeout(30000)]
fn test_flatten_phase4_substitute_constants_tree_depth_scaling() {
    run_with_large_stack(test_flatten_phase4_substitute_constants_tree_depth_scaling_inner);
}

fn test_flatten_phase4_substitute_constants_tree_depth_scaling_inner() {
    let const_map_size = 5; // Fixed K
    let small_t = 50;
    let large_t = 400;
    let rounds = 5;
    let iters = 200;

    // Correctness gate (#2130): verify substitute_constants fires on the nested
    // tree, not just equality self-substitution. Phase 4 substitutes into ALL
    // expressions including the equalities that defined the const_map (producing
    // tautologies like 0==0). We verify >= 3 assertions: 2 equality self-subs
    // + 1 nested tree substitution.
    {
        let gate_exprs = build_ghost_deep_tree_chain(2, 5);
        let mut encoder = AYEncoder::new_with_quantifiers();
        for i in 0..2 {
            let name = format!("uf_{i}");
            let decl = encoder.solver.declare_fun(&name, &[Sort::Int], Sort::Int);
            encoder.decls_for_test_mut().insert_logic_func(name, decl);
        }
        let _ = encoder.get_or_declare_var("a", Sort::Int);
        let rev_before = encoder.assertion_pipeline_for_test().assertion_revision();
        let result = flatten_ghost_implications(&mut encoder, &gate_exprs);
        assert!(
            result.is_ok(),
            "substitute_constants tree-depth gate should succeed: {result:?}"
        );
        let assertions_added =
            encoder.assertion_pipeline_for_test().assertion_revision() - rev_before;
        assert!(
            assertions_added >= 3,
            "Phase 4 should assert simplified forms for equalities AND the nested \
             tree. Got {assertions_added} (expected >= 3). If only 2, the nested \
             tree substitution is not firing."
        );
    }

    // Warm up
    let _ = measure_flatten_deep_tree_time(const_map_size, small_t, iters);
    let _ = measure_flatten_deep_tree_time(const_map_size, large_t, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_flatten_deep_tree_time(const_map_size, small_t, iters);
        let large_time = measure_flatten_deep_tree_time(const_map_size, large_t, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(T): 8x input → 8x. Allow 16x for encoder/solver overhead.
    // Quadratic: 8² = 64x — well above threshold.
    assert!(
        min_ratio < 16.0,
        "substitute_constants tree-depth scaling (T={large_t}/{small_t}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ~8x (O(T) with K={const_map_size} fixed). \
         If > 16x, tree traversal has superlinear regression."
    );

    eprintln!(
        "substitute_constants_tree_depth: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(T) expect ~8x for T={small_t}->{large_t}, K={const_map_size})"
    );
}

// ---------------------------------------------------------------------------
// 3c. flatten_ghost_implications Phase 4: substitute_constants const_map size scaling
// ---------------------------------------------------------------------------

/// Proves that `substitute_constants` scales linearly in const_map size K
/// when expression tree depth T is fixed.
///
/// `substitute_constants` uses `const_map: Vec<(&PureExpr, &PureExpr)>` and
/// calls `.iter().find()` at **every AST node** — a linear scan of O(K) per
/// node. With T fixed, total cost is O(T × K), so scaling K by 8x should
/// yield ~8x slowdown (linear in K).
///
/// This test complements `test_flatten_phase4_substitute_constants_tree_depth_scaling`
/// which scales T at fixed K. Together they prove the O(T × K) bound.
///
/// Scales K from 8 to 64 (8x) and expects at most 16x (linear with overhead).
/// A quadratic regression in K (e.g., from re-scanning const_map during builds)
/// would show ~64x. Observed: ~2.5x (sublinear because per-node traversal
/// cost dominates the K scan at these sizes). The test guards against
/// superlinear regressions that would emerge at larger K.
///
/// Re: #1294 — substitute_constants const_map size dimension
#[test]
#[timeout(30000)]
fn test_flatten_phase4_substitute_constants_const_map_size_scaling() {
    let tree_depth = 100; // Fixed T
    let small_k = 8;
    let large_k = 64;
    let rounds = 5;
    let iters = 100;

    // Correctness gate: verify const_map entries are used in substitution
    {
        let gate_exprs = build_ghost_deep_tree_chain(small_k, 10);
        let mut encoder = AYEncoder::new_with_quantifiers();
        for i in 0..small_k {
            let name = format!("uf_{i}");
            let decl = encoder.solver.declare_fun(&name, &[Sort::Int], Sort::Int);
            encoder.decls_for_test_mut().insert_logic_func(name, decl);
        }
        let _ = encoder.get_or_declare_var("a", Sort::Int);
        let rev_before = encoder.assertion_pipeline_for_test().assertion_revision();
        let result = flatten_ghost_implications(&mut encoder, &gate_exprs);
        assert!(
            result.is_ok(),
            "const_map size gate should succeed: {result:?}"
        );
        let assertions_added =
            encoder.assertion_pipeline_for_test().assertion_revision() - rev_before;
        // K equality self-substitutions + 1 nested tree = K+1 minimum
        assert!(
            assertions_added >= (small_k + 1) as u64,
            "Phase 4 should assert simplified forms for all {small_k} equalities \
             plus the nested tree. Got {assertions_added}."
        );
    }

    // Warm up
    let _ = measure_flatten_deep_tree_time(small_k, tree_depth, iters);
    let _ = measure_flatten_deep_tree_time(large_k, tree_depth, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = measure_flatten_deep_tree_time(small_k, tree_depth, iters);
        let large_time = measure_flatten_deep_tree_time(large_k, tree_depth, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(K): 8x input → 8x. Allow 16x for overhead.
    // Quadratic: 8² = 64x — well above threshold.
    assert!(
        min_ratio < 16.0,
        "substitute_constants const_map size scaling (K={large_k}/{small_k}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ~8x (O(K) with T={tree_depth} fixed). \
         If > 16x, const_map linear scan has superlinear regression."
    );

    eprintln!(
        "substitute_constants_const_map_size: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(K) expect ~8x for K={small_k}->{large_k}, T={tree_depth})"
    );
}

// ---------------------------------------------------------------------------
// 4. substitute_vars_in_expr: co-growing depth+map scaling bound
// ---------------------------------------------------------------------------

/// Build a chain of `depth` nested Forall quantifiers with a leaf that
/// references variables from the binding map. Each quantifier binds a unique
/// variable, so the capture-avoiding substitution must repeatedly update its
/// binder state while preserving the same external behavior.
fn build_nested_forall_with_leaf_vars(depth: usize, map_size: usize) -> PureExpr {
    // Leaf: sum of all substitution targets to ensure the map is relevant
    let mut leaf: PureExpr = var("s_0");
    for i in 1..map_size {
        leaf = PureExpr::BinOp(Arc::new(leaf), BinOp::Add, Arc::new(var(&format!("s_{i}"))));
    }
    // Wrap in `depth` Forall binders, each with a distinct variable
    for d in (0..depth).rev() {
        leaf = PureExpr::Forall {
            var: format!("q_{d}"),
            var_sort: None,
            body: Arc::new(leaf),
            triggers: vec![],
        };
    }
    leaf
}

fn build_substitution_map(size: usize) -> HashMap<String, PureExpr> {
    (0..size)
        .map(|i| (format!("s_{i}"), PureExpr::Int(i as i64)))
        .collect()
}

/// Correctness gate for substitute_vars scaling tests (#2130).
/// Verifies substitution actually replaces Var("s_*") with Int values.
fn assert_substitute_vars_correctness(expr: &PureExpr, map: &HashMap<String, PureExpr>) {
    let result = substitute_vars_in_expr(expr, map);
    fn contains_s_var(e: &PureExpr) -> bool {
        match e {
            PureExpr::Var(name, _) => name.starts_with("s_"),
            PureExpr::BinOp(l, _, r) => contains_s_var(l) || contains_s_var(r),
            PureExpr::Forall { body, .. } => contains_s_var(body),
            PureExpr::Match { scrutinee, arms } => {
                contains_s_var(scrutinee) || arms.iter().any(|arm| contains_s_var(&arm.body))
            }
            _ => false,
        }
    }
    assert!(
        !contains_s_var(&result),
        "substitute_vars should replace all s_* vars with Int values"
    );
    assert_ne!(
        format!("{result:?}"),
        format!("{expr:?}"),
        "substitute_vars output should differ from input when map has matching keys"
    );
}

/// Proves that `substitute_vars_in_expr` with co-growing depth and map size
/// scales at most quadratically: O(d × s) where d = depth, s = map size.
///
/// When d and s grow together (d ≈ s ≈ n), the workload grows in both
/// dimensions at once, so the public wrapper should stay within an O(n²)
/// envelope rather than regressing to a worse bound.
///
/// This test scales n from 15 to 60 (4x) and expects at most 16x (quadratic).
/// A cubic regression (O(n³)) from accidental re-traversal or deep-copy at
/// each level would show up as 64x.
///
/// Complements `test_substitution_depth_scaling_linear_in_public_api` in
/// performance_proofs.rs which scales depth at FIXED map size (proving O(d)
/// at constant s). This test scales BOTH dimensions together.
#[test]
#[timeout(30000)]
fn test_substitute_vars_co_growing_depth_and_map_quadratic() {
    let small_n = 15;
    let large_n = 60;
    let rounds = 5;
    let iters = 200;

    let small_expr = build_nested_forall_with_leaf_vars(small_n, small_n);
    let small_map = build_substitution_map(small_n);
    let large_expr = build_nested_forall_with_leaf_vars(large_n, large_n);
    let large_map = build_substitution_map(large_n);

    // Correctness gate: verify substitution actually replaces vars (#2130)
    assert_substitute_vars_correctness(&small_expr, &small_map);

    // Warm up
    for _ in 0..iters {
        let _ = substitute_vars_in_expr(&small_expr, &small_map);
        let _ = substitute_vars_in_expr(&large_expr, &large_map);
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let _ = substitute_vars_in_expr(&small_expr, &small_map);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let _ = substitute_vars_in_expr(&large_expr, &large_map);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(n²): 4x input → 16x. Allow up to 50x for multi-worker overhead.
    // O(n³): 4³ = 64x — still above threshold.
    // Previous 25x threshold failed consistently in full-suite runs under
    // multi-worker CPU contention (min ratios 33x observed). Passes in
    // isolation at ~16x. Bumped to 50x per #2023 audit. (#2023)
    assert!(
        min_ratio < 50.0,
        "substitute_vars co-growing scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ≤16x (O(n²) for 4x input). \
         If > 50x, substitute_vars_in_expr has regressed past its quadratic bound."
    );

    eprintln!(
        "substitute_vars_co_growing: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(n²) expect ≤16x for n={small_n}->{large_n})"
    );
}

/// Proves that `substitute_vars_in_expr` with Match arms scales at most
/// quadratically in arm count when binding map is proportional.
///
/// Each Match arm clones the full binding HashMap: O(arms × map_size).
/// With arms ≈ map_size ≈ n, this is O(n²).
#[test]
#[timeout(30000)]
fn test_substitute_vars_match_arms_quadratic() {
    let small_n = 15;
    let large_n = 60;
    let rounds = 5;
    let iters = 200;

    let build_match_expr = |n: usize| -> PureExpr {
        use trust_wp_core::formula::{MatchArm, Pattern};
        let arms: Vec<MatchArm> = (0..n)
            .map(|i| MatchArm {
                pattern: Pattern::Wildcard,
                body: var(&format!("s_{}", i % n)),
            })
            .collect();
        PureExpr::Match {
            scrutinee: Arc::new(var("x")),
            arms,
        }
    };

    let small_expr = build_match_expr(small_n);
    let small_map = build_substitution_map(small_n);
    let large_expr = build_match_expr(large_n);
    let large_map = build_substitution_map(large_n);

    // Correctness gate: verify substitution replaces all s_* vars in Match arms (#2130)
    {
        assert_substitute_vars_correctness(&small_expr, &small_map);
    }

    // Warm up
    for _ in 0..iters {
        let _ = substitute_vars_in_expr(&small_expr, &small_map);
        let _ = substitute_vars_in_expr(&large_expr, &large_map);
    }

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let start = Instant::now();
        for _ in 0..iters {
            let _ = substitute_vars_in_expr(&small_expr, &small_map);
        }
        let small_time = start.elapsed();

        let start = Instant::now();
        for _ in 0..iters {
            let _ = substitute_vars_in_expr(&large_expr, &large_map);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(n²): 4x input → 16x. Allow 25x.
    assert!(
        min_ratio < 25.0,
        "substitute_vars Match arms scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ≤16x (O(n²) for 4x input). \
         If > 25x, Match arm HashMap cloning has worse-than-quadratic regression."
    );

    eprintln!(
        "substitute_vars_match_arms: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(n²) expect ≤16x for n={small_n}->{large_n})"
    );
}

// ---------------------------------------------------------------------------
// 5. try_match_expr: bound_vars.contains() linear scan scaling
// ---------------------------------------------------------------------------

/// Build a flat LogicFnCall with `n` Var arguments, all of which are
/// bound variables. This forces `try_match_expr` to call
/// `bound_vars.contains()` at each Var leaf.
fn build_logic_fn_with_var_args(n: usize, prefix: &str) -> PureExpr {
    let args: Vec<PureExpr> = (0..n).map(|i| var(&format!("{prefix}{i}"))).collect();
    PureExpr::LogicFnCall {
        name: "test_fn".to_string(),
        args,
    }
}

/// Correctness gate for try_match_expr scaling tests (#2130).
/// Verifies the function returns true and produces correct bindings.
fn assert_try_match_correctness(
    body: &PureExpr,
    ground: &PureExpr,
    bound_vars: &[String],
    expected_bindings: usize,
) {
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut bindings = Vec::new();
    let matched = try_match_expr(body, ground, bound_vars, &existing, &mut bindings);
    assert!(
        matched,
        "try_match_expr should match structurally identical LogicFnCalls"
    );
    assert_eq!(
        bindings.len(),
        expected_bindings,
        "should produce one binding per bound var"
    );
    assert_eq!(bindings[0].0, "v0", "first binding key should be v0");
    assert!(
        matches!(&bindings[0].1, PureExpr::Var(name, _) if name == "g0"),
        "first binding value should be Var(g0): got {:?}",
        bindings[0].1
    );
    let last = bindings.len() - 1;
    assert!(
        matches!(&bindings[last].1, PureExpr::Var(name, _) if name == &format!("g{last}")),
        "last binding value should be Var(g{last}): got {:?}",
        bindings[last].1
    );
}

fn measure_try_match_expr_time(
    body: &PureExpr,
    ground: &PureExpr,
    bound_vars: &[String],
    iters: usize,
) -> std::time::Duration {
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let start = Instant::now();
    for _ in 0..iters {
        let mut bindings = Vec::new();
        let _ = try_match_expr(body, ground, bound_vars, &existing, &mut bindings);
    }
    start.elapsed()
}

/// Proves that `try_match_expr` scales at most quadratically when
/// bound_vars count and AST node count grow together.
///
/// `try_match_expr` walks the AST recursively (O(T) nodes). At each
/// Var node, `bound_vars.contains(name)` does a linear scan of the
/// bound_vars slice (O(b)). With T ≈ b ≈ n, total is O(n²).
///
/// Scales n from 50 to 200 (4x) and expects at most 16x (quadratic).
#[test]
#[timeout(60000)]
fn test_try_match_expr_bound_vars_scaling() {
    let small_n = 50;
    let large_n = 200;
    let rounds = 5;
    let iters = 2000;

    let small_body = build_logic_fn_with_var_args(small_n, "v");
    let small_ground = build_logic_fn_with_var_args(small_n, "g");
    let small_bound: Vec<String> = (0..small_n).map(|i| format!("v{i}")).collect();

    let large_body = build_logic_fn_with_var_args(large_n, "v");
    let large_ground = build_logic_fn_with_var_args(large_n, "g");
    let large_bound: Vec<String> = (0..large_n).map(|i| format!("v{i}")).collect();

    // Correctness gate: verify return value before measuring timing (#2130)
    assert_try_match_correctness(&small_body, &small_ground, &small_bound, small_n);

    // Warm up
    let _ = measure_try_match_expr_time(&small_body, &small_ground, &small_bound, iters);
    let _ = measure_try_match_expr_time(&large_body, &large_ground, &large_bound, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time =
            measure_try_match_expr_time(&small_body, &small_ground, &small_bound, iters);
        let large_time =
            measure_try_match_expr_time(&large_body, &large_ground, &large_bound, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min_ratio = ratios[0];

    // O(n²): 4x input → 16x. Allow 25x.
    // Threshold distinguishes quadratic (expected) from cubic (regression).
    assert!(
        min_ratio < 25.0,
        "try_match_expr bound_vars scaling ({large_n}/{small_n}) = {min_ratio:.1}x \
         (rounds: {ratios:.1?}). Expected ≤16x (O(n²) for 4x input). \
         If > 25x, bound_vars scan has worse-than-quadratic regression."
    );

    eprintln!(
        "try_match_expr_bound_vars: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(n²) expect ≤16x for n={small_n}->{large_n})"
    );
}
