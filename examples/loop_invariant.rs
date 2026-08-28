// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop invariant example demonstrating verification with loops.
//!
//! Verify it with:  `trust-wp examples/loop_invariant.rs`
//!
//! trust-wp discharges four obligations per annotated loop:
//! - **Initialization**: the invariant holds on entry (`requires => inv`)
//! - **Preservation**: the body maintains it (`inv && cond => inv'`)
//! - **Postcondition**: it implies the contract on exit
//! - **Termination** (with `#[variant]`): the variant strictly decreases and
//!   stays non-negative
//!
//! Every function here verifies. The invariants are the *weakest* ones that
//! do — strengthening one is how you fix a `preservation check failed`.

use trust_wp::{ensures, invariant, requires, variant};

/// Sum of first n natural numbers.
///
/// Invariant: `sum == i * (i - 1) / 2`
/// At each iteration, sum holds the sum of 0..i.
///
/// Postcondition: `result == n * (n + 1) / 2`
#[requires(n >= 0)]
#[ensures(result >= 0)]
#[invariant(sum >= 0)]
fn sum_first_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i <= n {
        sum += i;
        i += 1;
    }
    sum
}

/// Count down from n to 0.
///
/// `#[variant]` adds the termination proof: `count` strictly decreases each
/// iteration and is bounded below by the invariant, so the loop ends.
#[requires(n >= 0)]
#[ensures(result == 0)]
#[invariant(count >= 0)]
#[variant(count)]
fn count_down(n: i32) -> i32 {
    let mut count = n;
    while count > 0 {
        count -= 1;
    }
    count
}

/// Repeated doubling: `2^k`.
///
/// The accumulator grows multiplicatively, but by a *constant*, so the
/// preservation obligation `acc >= 1 => 2 * acc >= 1` stays linear and the
/// solver proves it outright.
///
/// A loop whose step is `acc *= i` (factorial) does not work this way: the
/// obligation becomes `acc >= 1 && i >= 1 => acc * i >= 1`, which is nonlinear
/// integer arithmetic. `acc >= 1` is then not enough, and no bound on `acc`
/// alone rescues it — you need an invariant that pins `acc` to `i` exactly
/// (`acc == fact(i - 1)` with `fact` a `#[logic]` function). That is a
/// different lesson than this file is for; see `contract-syntax.md` on
/// `#[logic]`.
#[requires(k >= 0 && k <= 30)]
#[ensures(result >= 1)]
#[invariant(acc >= 1 && j >= 0)]
#[variant(k - j)]
fn power_of_two(k: i32) -> i32 {
    let mut acc = 1;
    let mut j = 0;
    while j < k {
        acc *= 2;
        j += 1;
    }
    acc
}

fn main() {
    // Sum of 0..=10 = 55
    let sum = sum_first_n(10);
    println!("sum_first_n(10) = {}", sum);
    assert_eq!(sum, 55);

    // Count down from 5 to 0
    let zero = count_down(5);
    println!("count_down(5) = {}", zero);
    assert_eq!(zero, 0);

    // 2^5 = 32
    let pow = power_of_two(5);
    println!("power_of_two(5) = {}", pow);
    assert_eq!(pow, 32);
}
