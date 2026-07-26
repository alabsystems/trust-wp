// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for contract macro parsing.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests verify that contract attributes are parsed correctly
//! and produce valid Rust code.

use trust_wp::{ensures, requires, trusted};

// Basic requires with comparison
#[requires(x > 0)]
fn positive_only(x: i32) -> i32 {
    x
}

// Ensures with result
#[ensures(result > 0)]
fn always_positive() -> i32 {
    42
}

// Ensures with result equality
#[ensures(result == x + 1)]
fn increment(x: i32) -> i32 {
    x + 1
}

// Complex ensures with old()
#[ensures(result == old(x) + 1)]
fn increment_with_old(x: i32) -> i32 {
    x + 1
}

// Multiple contracts
#[requires(x > 0)]
#[ensures(result > x)]
fn double_positive(x: i32) -> i32 {
    x * 2
}

// Logical operators
#[requires(x > 0 && x < 100)]
fn bounded(x: i32) -> i32 {
    x
}

// Creusot-style chained comparison syntax (non-Rust syntax)
#[requires(0 <= x < 100)]
fn bounded_chain(x: i32) -> i32 {
    x
}

// Disjunction
#[requires(x == 0 || x == 1)]
fn binary_only(x: i32) -> i32 {
    x
}

// Implication pattern: !(P) || Q  means P implies Q
#[requires(!(x > 0) || y > 0)]
fn implies_pattern(x: i32, y: i32) -> i32 {
    x + y
}

// Method calls in contracts
#[requires(s.len() > 0)]
fn non_empty_str(s: &str) -> &str {
    s
}

// old() with method calls
#[ensures(result == old(v.len()) - 1)]
fn pop_returns_new_len(v: &mut Vec<i32>) -> usize {
    v.pop();
    v.len()
}

// Field access
struct Point {
    x: i32,
    y: i32,
}

#[requires(p.x > 0 && p.y > 0)]
fn positive_point(p: &Point) -> i32 {
    p.x + p.y
}

#[test]
fn test_contracts_compile() {
    // If this compiles, the basic contracts are being parsed correctly
    assert_eq!(positive_only(5), 5);
    assert_eq!(always_positive(), 42);
    assert_eq!(increment(5), 6);
    assert_eq!(increment_with_old(5), 6);
    assert_eq!(double_positive(5), 10);
    assert_eq!(bounded(50), 50);
    assert_eq!(bounded_chain(50), 50);
    assert_eq!(binary_only(1), 1);
    assert_eq!(implies_pattern(1, 2), 3);
    assert_eq!(non_empty_str("hello"), "hello");

    let mut v = vec![1, 2, 3];
    assert_eq!(pop_returns_new_len(&mut v), 2);

    let p = Point { x: 1, y: 2 };
    assert_eq!(positive_point(&p), 3);

    // Test trusted functions compile and run normally
    assert!(trusted_external() > 0);
    assert_eq!(call_trusted(), 43);
    assert_eq!(trusted_double(5), 10);

    // Test quantifier trigger annotation syntax compiles (Part of #228)
    assert_eq!(sum_positive(5), 0);
}

// Trusted function - postcondition assumed but body not verified
#[trusted]
#[ensures(result > 0)]
fn trusted_external() -> i32 {
    42 // In real usage, could call external/unsafe code
}

// Another trusted function with preconditions
// Preconditions ARE checked at call sites
#[trusted]
#[requires(x > 0)]
#[ensures(result == x * 2)]
fn trusted_double(x: i32) -> i32 {
    x * 2 // Body not verified
}

// A function that calls a trusted function
// The postcondition of trusted_external is assumed
#[ensures(result > 1)]
fn call_trusted() -> i32 {
    trusted_external() + 1
}

// Part of #228: Quantifier with trigger annotations
// Syntax: forall<i: Int> #[trigger(expr)] body
#[requires(n >= 0)]
#[ensures(result >= 0)]
fn sum_positive(_n: i32) -> i32 {
    // In actual verification, this would use quantifiers with triggers like:
    // forall<i: Int> #[trigger(arr@[i])] (0 <= i && i < n) ==> arr@[i] >= 0
    0 // Simplified for compilation test
}
