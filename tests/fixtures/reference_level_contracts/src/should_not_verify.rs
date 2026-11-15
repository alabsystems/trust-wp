// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! False contracts, each verified while the text was read another way. The
//! chained comparison `0 < 1 < 2` keeps an ill-typed clause from the Rust
//! type-check, so only trust-wp's own reading stands between it and a
//! verdict.

use trust_wp::prelude::*;

#[logic(open)]
fn addn<const N: i32>(x: i32) -> i32 {
    x + N
}

// True exactly of the `m` at most 0.
#[logic(open)]
fn le_all_nonneg(m: Int) -> bool {
    pearlite! { forall<i: Int> 0 <= i ==> m <= i }
}

// A reference pattern: `t` is `*p`, the value `p` is left with (the clause
// reads `old`). Reading `t` as `p` itself reads the entry value.
#[requires(*p < 100)]
#[ensures({ let &mut t = p; t == old(*p) })]
fn inc_let(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(match p { &mut t => t == old(*p) })]
fn inc_match(p: &mut i32) {
    *p += 1;
}

// `p@` and `view(p)` are `(*p)@`: in a clause that reads `old`, the value
// `p` is left with, as `*p` is. They were read at entry.
#[requires(*p < 100)]
#[ensures(*p == old(*p) + 1 && p@ == old(p@))]
fn star_plus_one_and_view_unchanged(p: &mut u32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(*p == old(*p) + 1 && view(p) == old(view(p)))]
fn star_plus_one_and_view_call_unchanged(p: &mut u32) {
    *p += 1;
}

#[requires(p@ < 100)]
#[ensures(p@ == old(p@) && (*p)@ == old((*p)@) + 1)]
fn view_unchanged_and_referent_view_plus_one(p: &mut u32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(*p == old(*p) + 1 && p@ == old(*p)@)]
fn star_plus_one_and_view_is_entry(p: &mut u32) {
    *p += 1;
}

// `x @ y` binds both to `x + 1`, so `y == x`. Matched against the value
// after `x` was rebound, `y` read the new `x` plus one.
#[requires(x < 1000)]
#[ensures({ let x @ y = x@ + 1; y == x@ + 1 })]
fn alias_rereads_the_value(x: i32) -> i32 {
    x
}

// `(a, b) = (b, a)` swaps. Each field's binding read the value inside the
// ones before it, so the new `b` was the new `a`.
#[ensures({ let (a, b) = (b, a); a == b })]
fn swap_reads_the_new_names(a: i32, b: i32) -> i32 {
    let _ = b;
    a
}

// `{ 2 * 3 }` and `{ 1 * 3 }` are const arguments; each was read as a type
// (it holds a `*`) and dropped, so both sides read `addn(x)`.
#[requires(x < 1000 && x > -1000)]
#[ensures(addn::<{ 2 * 3 }>(x) == addn::<{ 1 * 3 }>(x))]
fn const_block_arguments_differ(x: i32) -> i32 {
    x
}

// A substitution captured a name a binder rebinds. Unfolding
// `le_all_nonneg` at `m := i@` read `forall<i> 0 <= i ==> i@ <= i`, true; it
// is `5 <= 0`.
#[requires(i == 5)]
#[ensures(le_all_nonneg(i@))]
fn logic_unfolding_captures(i: i32) {}

// `result := y` read `forall<y> y == y`.
#[ensures(forall<y: i32> y == result)]
fn result_substitution_captures(y: i32) -> i32 {
    y
}

#[ensures(forall<x: i32> x == result)]
fn forall_shadows_a_param(x: i32) -> i32 {
    x
}

// A binder that shadows a `&mut` param was read as the param: its sort, its
// view, its final value.
#[requires(*p < 100)]
#[ensures({ let e = old(*p); let p = e; p@ == e@ + 1 })]
fn let_shadows_a_mut_ref(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures({ let e = old(*p); let p = e + 7; p@ == e@ })]
fn let_shadows_a_mut_ref_view(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100 && *p > -100)]
#[ensures({ let e = old(*p); *p == e + 1i32 && forall<p: i32> p == 0i32 ==> p == e + 1i32 })]
fn forall_shadows_a_mut_ref(p: &mut i32) {
    *p += 1;
}

fn main() {}
