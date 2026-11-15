//@ expect: reject
//@ mechanism: find_body_for_receiver's unique-ensures shortcut bound a source-typed receiver
//@ mechanism: that failed the name lookup (a &dyn Fn or generic F parameter `f`) to the only
//@ mechanism: ensures-bearing sibling closure `c`, so f(5) was given c's contract (6).
//@ fixed-by: wp-s43 (shortcuts refuse source-typed Var receivers)
//@ accept-means: an unrelated closure's ensures are again inlined for a different receiver.
//@ WHY THE CONTRACTS ARE FALSE: f is arbitrary; nothing says f(5) == 6.
//@ teeth: before the fix the [TRUST_WP_DEBUG] closure shortcut=unique_ensures trace bound
//@ teeth: receiver f to candidate c; the verdict was withheld only by the vacuity gate
//@ teeth: (unknown), not by the encoding - measured on both receiver spellings here, the &dyn Fn and the generic F.
//@ also-verified: dyn_with_ensures_closure::{closure#1}, generic_with_ensures_closure::{closure#1}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(forall<x: i32> f.precondition((x,)))]
pub fn dyn_with_ensures_closure(f: &dyn Fn(i32) -> i32) {
    let c = #[requires(x@ < 100)]
    #[ensures(result@ == x@ + 1)]
    |x: i32| x + 1;
    let _a = c(0);
    let r = f(5);
    proof_assert!(r@ == 6);
}

#[requires(forall<x: i32> f.precondition((x,)))]
pub fn generic_with_ensures_closure<F: Fn(i32) -> i32>(f: F) {
    let c = #[requires(x@ < 100)]
    #[ensures(result@ == x@ + 1)]
    |x: i32| x + 1;
    let _a = c(0);
    let r = f(5);
    proof_assert!(r@ == 6);
}
