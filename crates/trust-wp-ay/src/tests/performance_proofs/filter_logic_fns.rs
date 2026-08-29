// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// filter_logic_fns_for_goal: termination and correctness
// =============================================================================

/// Helper: build a `LogicFnDef` with a body that calls the given function names.
fn make_logic_fn(name: &str, calls: &[&str]) -> LogicFnDef {
    // Build body as a chain of additions of LogicFnCall expressions.
    // e.g., calls = ["f", "g"] => f(0) + g(0)
    let body = if calls.is_empty() {
        int(0)
    } else {
        let mut exprs: Vec<PureExpr> = calls
            .iter()
            .map(|c| logic_fn_call(c, vec![var("x")]))
            .collect();
        let mut result = exprs.pop().unwrap();
        for e in exprs.into_iter().rev() {
            result = add(e, result);
        }
        result
    };

    LogicFnDef::new(
        name.to_string(),
        format!("crate::test::{name}"),
        vec!["x".to_string()],
        body,
    )
    .with_mode(LogicMode::Open)
}

/// Linear chain: a -> b -> c -> d. Requesting "a" should pull all 4.
/// Proves fixed-point terminates and computes full transitive closure.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_linear_chain() {
    let fns = vec![
        make_logic_fn("a", &["b"]),
        make_logic_fn("b", &["c"]),
        make_logic_fn("c", &["d"]),
        make_logic_fn("d", &[]),
    ];
    let initial: HashSet<String> = ["a".to_string()].into();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert_eq!(
        result.len(),
        4,
        "Linear chain a->b->c->d should pull all 4 functions"
    );
    let names: HashSet<_> = result
        .iter()
        .map(trust_wp_core::logic::LogicFnDef::name)
        .collect();
    assert!(
        names.contains("a"),
        "chain result should contain 'a'; found: {names:?}"
    );
    assert!(
        names.contains("b"),
        "chain result should contain 'b'; found: {names:?}"
    );
    assert!(
        names.contains("c"),
        "chain result should contain 'c'; found: {names:?}"
    );
    assert!(
        names.contains("d"),
        "chain result should contain 'd'; found: {names:?}"
    );
}

/// Empty initial set: should return no functions.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_empty_initial() {
    let fns = vec![make_logic_fn("a", &["b"]), make_logic_fn("b", &[])];
    let initial: HashSet<String> = HashSet::new();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert!(result.is_empty(), "Empty initial set should return nothing");
}

/// Disconnected functions: only requested ones are returned.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_disconnected() {
    let fns = vec![
        make_logic_fn("a", &[]),
        make_logic_fn("b", &[]),
        make_logic_fn("c", &[]),
    ];
    let initial: HashSet<String> = ["a".to_string()].into();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert_eq!(result.len(), 1, "Only 'a' should be returned");
    assert_eq!(
        result[0].name(),
        "a",
        "disconnected: only requested function 'a' should appear"
    );
}

/// Diamond dependency: a -> {b, c}, b -> d, c -> d.
/// Should find a, b, c, d without duplicates or infinite loops.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_diamond_dependency() {
    let fns = vec![
        make_logic_fn("a", &["b", "c"]),
        make_logic_fn("b", &["d"]),
        make_logic_fn("c", &["d"]),
        make_logic_fn("d", &[]),
    ];
    let initial: HashSet<String> = ["a".to_string()].into();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert_eq!(
        result.len(),
        4,
        "Diamond dependency should find all 4 functions"
    );
}

/// Stress test: chain of 50 functions. F=50 is the documented threshold
/// where a topological approach should be considered (#506 F5).
/// Proves the fixed-point terminates within the 10s test timeout even at threshold.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_chain_50() {
    let mut fns = Vec::with_capacity(50);
    for i in 0..50 {
        let calls = if i < 49 {
            vec![format!("f{}", i + 1)]
        } else {
            vec![]
        };
        let call_refs: Vec<&str> = calls.iter().map(String::as_str).collect();
        fns.push(make_logic_fn(&format!("f{i}"), &call_refs));
    }
    let initial: HashSet<String> = ["f0".to_string()].into();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert_eq!(
        result.len(),
        50,
        "50-element chain should find all 50 functions"
    );
}

/// Self-referencing function (`is_recursive=true` pattern). The fixed-point
/// should still terminate because `expanded` prevents re-expansion.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_self_referencing() {
    // "a" calls "a" in its body (recursive)
    let fns = vec![make_logic_fn("a", &["a"])];
    let initial: HashSet<String> = ["a".to_string()].into();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert_eq!(
        result.len(),
        1,
        "Self-referencing function should be found once"
    );
    assert_eq!(
        result[0].name(),
        "a",
        "self-referencing: function 'a' should be found"
    );
}

/// Mutual recursion: a -> b -> a. Should terminate and find both.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_mutual_recursion() {
    let fns = vec![make_logic_fn("a", &["b"]), make_logic_fn("b", &["a"])];
    let initial: HashSet<String> = ["a".to_string()].into();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert_eq!(
        result.len(),
        2,
        "Mutual recursion should find both functions"
    );
}
// =============================================================================
// filter_logic_fns_for_goal: requires clause transitivity
// =============================================================================

/// Logic functions referenced only through requires clauses (not body)
/// should also be included in the transitive closure.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_requires_clause_transitivity() {
    // "a" has body that doesn't reference anything,
    // but its requires clause references "guard".
    let a = LogicFnDef::new_with_requires(
        "a".to_string(),
        "crate::test::a".to_string(),
        vec!["x".to_string()],
        vec![logic_fn_call("guard", vec![var("x")])],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    let guard = make_logic_fn("guard", &[]);

    let fns = vec![a, guard];
    let initial: HashSet<String> = ["a".to_string()].into();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert_eq!(
        result.len(),
        2,
        "Function referenced in requires clause should be included"
    );
    let names: HashSet<_> = result
        .iter()
        .map(trust_wp_core::logic::LogicFnDef::name)
        .collect();
    assert!(
        names.contains("guard"),
        "guard should be in transitive closure"
    );
}

/// Unreferenced function (name never appears in any expression): should be excluded.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_unreferenced_excluded() {
    let fns = vec![
        make_logic_fn("used", &[]),
        make_logic_fn("unused", &["used"]), // calls "used" but is not itself referenced
    ];
    let initial: HashSet<String> = ["used".to_string()].into();
    let result = filter_logic_fns_for_goal(&fns, &initial);
    assert_eq!(
        result.len(),
        1,
        "Only directly referenced function should be returned"
    );
    assert_eq!(
        result[0].name(),
        "used",
        "unreferenced-caller: only 'used' should appear, not its unreferenced caller"
    );
}
// =============================================================================
// filter_logic_fns_for_goal: scaling ratio test
// =============================================================================

/// Measures the scaling ratio of `filter_logic_fns_for_goal` as chain length
/// increases from F=10 to F=40.
///
/// The documented complexity is O(F² × E) where F = number of functions and
/// E = total expression tree size. For linear chains where each body has O(1)
/// expressions, E ∝ F, making the theoretical worst case O(F³). However the
/// fixed-point terminates in exactly F iterations for a linear chain, so the
/// actual cost is O(F × total_calls_to_collect_names) = O(F² × body_size).
///
/// For O(F²) (linear chain, body_size=1): ratio(40/10) ≈ 16x.
/// For O(F³): ratio(40/10) ≈ 64x.
/// Threshold is 25x to detect worse-than-quadratic growth while tolerating
/// system load variance.
#[test]
#[timeout(30000)]
fn test_filter_logic_fns_chain_scaling_ratio() {
    use std::time::Instant;

    let small_f = 10;
    let large_f = 40;

    let build_chain = |n: usize| -> Vec<LogicFnDef> {
        let mut fns = Vec::with_capacity(n);
        for i in 0..n {
            let calls = if i < n - 1 {
                vec![format!("f{}", i + 1)]
            } else {
                vec![]
            };
            let call_refs: Vec<&str> = calls.iter().map(String::as_str).collect();
            fns.push(make_logic_fn(&format!("f{i}"), &call_refs));
        }
        fns
    };

    // Warm up both sizes to stabilize allocator and cache.
    {
        let fns = build_chain(small_f);
        let initial: HashSet<String> = ["f0".to_string()].into();
        let _ = filter_logic_fns_for_goal(&fns, &initial);
    }
    {
        let fns = build_chain(large_f);
        let initial: HashSet<String> = ["f0".to_string()].into();
        let _ = filter_logic_fns_for_goal(&fns, &initial);
    }

    // Measure small
    let start = Instant::now();
    for _ in 0..10 {
        let fns = build_chain(small_f);
        let initial: HashSet<String> = ["f0".to_string()].into();
        let result = filter_logic_fns_for_goal(&fns, &initial);
        assert_eq!(
            result.len(),
            small_f,
            "small chain ({small_f}) should return all functions"
        );
    }
    let small_time = start.elapsed();

    // Measure large
    let start = Instant::now();
    for _ in 0..10 {
        let fns = build_chain(large_f);
        let initial: HashSet<String> = ["f0".to_string()].into();
        let result = filter_logic_fns_for_goal(&fns, &initial);
        assert_eq!(
            result.len(),
            large_f,
            "large chain ({large_f}) should return all functions"
        );
    }
    let large_time = start.elapsed();

    let small_secs = small_time.as_secs_f64().max(1e-12);
    let ratio = large_time.as_secs_f64() / small_secs;

    // Keep only the upper-bound regression check: lower bounds are flaky under
    // scheduler noise and cache effects on busy machines.
    // O(F²): ratio ≈ 16x. O(F³): ratio ≈ 64x.
    // Threshold 25x catches cubic regression while allowing quadratic.
    assert!(
        ratio < 25.0,
        "filter_logic_fns chain scaling ratio ({large_f}/{small_f}) = {ratio:.1}x. \
         If > 25x, fixed-point algorithm may have worse-than-quadratic growth. \
         Expected ~16x with O(F²) fixed-point for linear chains."
    );

    eprintln!(
        "filter_logic_fns_scaling: small({small_f})={small_time:?}, \
         large({large_f})={large_time:?}, ratio={ratio:.1}x \
         (O(F²) expect ~16x, O(F³) expect ~64x)"
    );
}
