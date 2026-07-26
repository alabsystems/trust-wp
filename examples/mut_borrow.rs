// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mutable borrow example demonstrating RustHorn-style verification.
//!
//! This file demonstrates the syntax for mutable borrow contracts
//! using Creusot-style `*v` (current value) and `^v` (final value) notation.
//!
//! STATUS: Phase 6 - Mutable borrow verification implemented
//!
//! The implementation now supports:
//! - `*v` (deref current) maps to `v_current` in SMT
//! - `^v` (final/prophecy) maps to `v_final` in SMT
//! - `old(*v)` correctly maps to `v_current` (entry state value)
//! - MIR body extraction for mutable borrow functions
//! - Conditional body extraction (for if/else patterns like abs_mut)
//!
//! References:
//! - designs/2026-02-01-rusthorn-vs-sl.md (RustHorn vs Separation Logic)
//! - reference/creusot/ARCHITECTURE.md (Creusot's approach)

use trust_wp::{ensures, requires};

/// Increment a mutable reference.
///
/// RustHorn encoding:
/// - `*v` (deref current) becomes `v_current` in SMT
/// - `^v` (final/prophecy) becomes `v_final` in SMT
/// - Contract: v_final == v_current + 1
///
/// The body `*v += 1` resolves the prophecy: v_final = v_current + 1.
#[requires(*v > i32::MIN)]
#[ensures(^v == old(*v) + 1)]
fn increment_ref(v: &mut i32) {
    *v += 1;
}

/// Swap two values via mutable references.
///
/// RustHorn encoding uses separate (current, final) pairs for each reference.
/// - a_current, a_final for `a`
/// - b_current, b_final for `b`
///
/// Postconditions:
/// - a_final == b_current (a ends with b's original value)
/// - b_final == a_current (b ends with a's original value)
#[requires(true)]
#[ensures(^a == old(*b) && ^b == old(*a))]
fn swap(a: &mut i32, b: &mut i32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

/// Absolute value in-place.
#[requires(true)]
#[ensures(^v >= 0)]
fn abs_mut(v: &mut i32) {
    if *v < 0 {
        *v = -*v;
    }
}

fn main() {
    let mut x = 5;
    increment_ref(&mut x);
    assert_eq!(x, 6);
    println!("After increment_ref: x = {}", x);

    let mut a = 10;
    let mut b = 20;
    swap(&mut a, &mut b);
    assert_eq!(a, 20);
    assert_eq!(b, 10);
    println!("After swap: a = {}, b = {}", a, b);

    let mut y = -42;
    abs_mut(&mut y);
    assert_eq!(y, 42);
    println!("After abs_mut: y = {}", y);
}
