// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Instant;

use super::*;

/// Generate a chain of additions: "x + x + x + ... + x" with `n` terms.
/// This produces an input of length O(n) that exercises `try_consume` O(n)
/// times during precedence-climbing binary expression parsing.
fn make_addition_chain(n: usize) -> String {
    vec!["x"; n].join(" + ")
}

/// Prove parser scaling is linear for binary expression chains.
///
/// This test measures the time ratio between parsing 2000 terms vs 500 terms.
/// For O(n), the expected ratio is (2000/500) = 4x. For O(n²), it would be 16x.
///
/// We assert the ratio is < 8x (midpoint between linear and quadratic).
/// If this test fails, it means the parser has superlinear scaling that
/// needs investigation (e.g., a regression reintroducing O(remaining)
/// allocations in `try_consume` or similar hot paths).
#[test]
fn test_parser_scaling_addition_chain() {
    let small_input = make_addition_chain(500);
    let large_input = make_addition_chain(2000);

    // Warm up
    let _ = parse_contract(&small_input);

    // Measure small
    let start = Instant::now();
    for _ in 0..3 {
        let result = parse_contract(&small_input);
        assert!(
            result.is_ok(),
            "500-term chain should parse: {:?}",
            result.as_ref().err()
        );
    }
    let small_time = start.elapsed();

    // Measure large
    let start = Instant::now();
    for _ in 0..3 {
        let result = parse_contract(&large_input);
        assert!(
            result.is_ok(),
            "2000-term chain should parse: {:?}",
            result.as_ref().err()
        );
    }
    let large_time = start.elapsed();

    let small_secs = small_time.as_secs_f64().max(1e-12);
    let ratio = large_time.as_secs_f64() / small_secs;

    // For O(n): ratio ~= 4x. For O(n²): ratio ~= 16x.
    // The fix (using self.input[self.position..] instead of
    // chars.clone().collect()) makes each try_consume() O(|s|)
    // instead of O(remaining), so total parse is O(n).
    assert!(
        ratio < 8.0,
        "Parser scaling ratio (2000/500 terms) = {ratio:.1}x. \
         Expected < 8x for O(n) scaling. If > 8x, check for \
         O(remaining) allocations reintroduced in try_consume paths."
    );

    // Document actual ratio for tracking
    eprintln!(
        "parser_scaling: small={small_time:?}, large={large_time:?}, ratio={ratio:.1}x \
         (O(n) expect ~4x, O(n²) expect ~16x)"
    );
}

/// Prove parser handles deeply nested expressions within timeout.
///
/// Nested parenthesized expressions like "((((x + 1))))" exercise
/// recursive descent with `try_consume("(")` at each level.
/// Each level does `O(remaining)` work in `try_consume`, but `remaining`
/// shrinks by 1 per level, so total is O(d²) in nesting depth d.
///
/// Depth is limited to 50 because the recursive-descent parser uses
/// stack frames proportional to nesting depth. Depths > ~150 overflow
/// the default test-thread stack.
#[test]
fn test_parser_scaling_nested_parens() {
    let depth = 50;
    let mut input = String::new();
    for _ in 0..depth {
        input.push('(');
    }
    input.push_str("x + 1");
    for _ in 0..depth {
        input.push(')');
    }

    let start = Instant::now();
    let result = parse_contract(&input);
    let elapsed = start.elapsed();

    assert!(
        result.is_ok(),
        "{depth}-deep nested parens should parse: {result:?}"
    );
    assert!(
        elapsed.as_millis() < 500,
        "{depth}-deep nested parens should parse in < 500ms, took {elapsed:?}"
    );

    eprintln!("parser_nested_parens: depth={depth}, elapsed={elapsed:?}");
}

/// Prove parser handles long identifier paths without quadratic blowup.
///
/// Path expressions like `"a::b::c::d::e::f"` exercise `try_consume("::")`
/// at each segment, each collecting remaining input.
#[test]
fn test_parser_scaling_long_path() {
    let segments = 100;
    let mut parts = Vec::with_capacity(segments);
    for i in 0..segments {
        parts.push(format!("seg{i}"));
    }
    let input = parts.join("::");

    let start = Instant::now();
    let result = parse_contract(&input);
    let elapsed = start.elapsed();

    assert!(
        result.is_ok(),
        "100-segment path should parse: {:?}",
        result.as_ref().err()
    );
    assert!(
        elapsed.as_millis() < 500,
        "100-segment path should parse in < 500ms, took {elapsed:?}"
    );

    eprintln!("parser_long_path: segments={segments}, elapsed={elapsed:?}");
}

/// Prove parser handles many keyword probes efficiently.
///
/// An expression like "x0 + x1 + x2 + ... + xN" forces the parser to
/// try ~10 keyword checks per identifier (forall, exists, match, if, etc.)
/// before falling through to the identifier branch. Each keyword check
/// calls `try_consume_keyword`, which collects remaining input.
#[test]
fn test_parser_scaling_keyword_probes() {
    // Build "x0 + x1 + x2 + ... + x99" — 100 identifiers, each probed
    // against ~10 keywords before matching as an identifier
    let n = 100;
    let mut parts = Vec::with_capacity(n);
    for i in 0..n {
        parts.push(format!("x{i}"));
    }
    let input = parts.join(" + ");

    let start = Instant::now();
    let result = parse_contract(&input);
    let elapsed = start.elapsed();

    assert!(
        result.is_ok(),
        "100-identifier expression should parse: {result:?}"
    );
    assert!(
        elapsed.as_millis() < 500,
        "100-identifier expression should parse in < 500ms, took {elapsed:?}"
    );

    eprintln!("parser_keyword_probes: identifiers={n}, elapsed={elapsed:?}");
}
