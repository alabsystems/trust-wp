// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! True contracts that read a reference level, a pattern's bindings and a
//! binder where the text puts them: a borrow a `let` binds, a binding by
//! reference with and without a subpattern, a reference pattern, an `@`
//! binding, a tuple pattern over the names it binds, a view, a `let` that
//! shadows a parameter. Each was refuted (a counterexample to a true
//! contract) or left unknown while the text was read another way.

use trust_wp::prelude::*;

// True exactly of the `m` at most 0.
#[logic(open)]
fn le_all_nonneg(m: Int) -> bool {
    pearlite! { forall<i: Int> 0 <= i ==> m <= i }
}

#[ensures({ let r = &x; *r == result })]
fn id(x: i32) -> i32 {
    x
}

#[ensures({ let ref t = x; *t == result })]
fn id_by_reference(x: i32) -> i32 {
    x
}

// Only `a` binds by reference: `t` is `x` itself.
#[ensures({ let ref a @ t = x; t == result && *a == result })]
fn id_by_reference_alias(x: i32) -> i32 {
    x
}

#[ensures({ let &t = y; t == result })]
fn read_through(y: &i32) -> i32 {
    *y
}

// The clause reads `old`, so `*p` outside it is the value `p` is left with.
#[requires(*p < 100)]
#[ensures({ let &mut t = p; t == old(*p) + 1 })]
fn inc(p: &mut i32) {
    *p += 1;
}

#[requires(x < 100)]
#[ensures(result@ == x@ + 1)]
fn succ(x: u32) -> u32 {
    x + 1
}

// `p@` is `(*p)@`: in a clause that reads `old`, both are the value `p` is
// left with.
#[requires(*p < 100)]
#[ensures(*p == old(*p) + 1)]
#[ensures(p@ == old(p@) + 1)]
fn inc_view(p: &mut u32) {
    *p += 1;
}

// Without `old`, `*p` is the value at entry.
#[requires(*p == 5)]
#[ensures(*p == 5)]
fn entry_value(p: &mut i32) {
    *p = 0;
}

// `x @ y` binds both to the value, read once: `y` is the new `x`.
#[requires(x < 1000)]
#[ensures({ let x @ y = x@ + 1; y == x })]
fn alias_reads_the_value_once(x: i32) -> i32 {
    x + 1
}

// `(a, b) = (b, a)` swaps: the new `b` is the old `a`.
#[ensures({ let (a, b) = (b, a); result == b })]
fn swap_binds_the_old_values(a: i32, b: i32) -> i32 {
    let _ = b;
    a
}

#[requires(i == -5)]
#[ensures(le_all_nonneg(i@))]
fn logic_unfolding_at_a_negative(i: i32) {}

// The `p` the `let` binds is `e + 7`, not the parameter.
#[requires(*p < 100)]
#[ensures({ let e = old(*p); let p = e + 7i32; p@ == (e + 7i32)@ })]
fn let_shadows_a_mut_ref_view(p: &mut i32) {
    *p += 1;
}

// The twins of should_not_verify's rebinding contracts: each reads the value
// `p` is left with where the text reads `*p`.
#[requires(*p < 100)]
#[ensures(match p { p => *p == old(*p) + 1 })]
fn match_rebinds_the_param(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(if let q = p { *q == old(*p) + 1 } else { true })]
fn if_let_binds_the_param(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(*(if true { p } else { p }) == old(*p) + 1)]
fn deref_of_a_branch(p: &mut i32) {
    *p += 1;
}

// The condition is read where the `let` is, in the state the clause reads.
#[requires(*p < 100)]
#[ensures({ let q = if *p > 0 { p } else { p }; *q == old(*p) + 1 })]
fn alias_of_a_branch(p: &mut i32) {
    *p += 1;
}

// No `old`: Creusot's reading, `*q` at entry and `^q` final.
#[requires(*p < 100)]
#[ensures(match p { q => ^q == *q + 1 })]
fn final_of_an_alias(p: &mut i32) {
    *p += 1;
}

#[ensures(|(x @ y, _z)| y == 1 && x == 1)]
fn closure_alias_reads_the_first_field() -> (i32, i32) {
    (1, 2)
}

// `(a)` is `a` parenthesized, not a one-element tuple.
#[ensures({ let (a) = x; a == result })]
fn parenthesized_pattern(x: i32) -> i32 {
    x
}

fn main() {}
