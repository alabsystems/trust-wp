// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! False contracts that bind or branch a `&mut` parameter before reading its
//! referent, each verified at exit 0 while the read was placed by the
//! parameter's spelling. The chained comparison is not needed: each clause
//! type-checks.

use trust_wp::prelude::*;

// Each of the following binds or branches the `&mut` parameter `p` before
// reading its referent. In a clause that reads `old`, every `*p` outside it
// is the value `p` is left with; the `*p -> ^p` rewrite was keyed by the
// spelling `p`, so the read through a binder or a branch stayed the entry
// value and `*q == old(*p)` held of `*p += 1`. A binder that shadows `p` was
// renamed apart before the rewrite looked for `p`.
#[requires(*p < 100)]
#[ensures(match p { p => *p == old(*p) })]
fn match_rebinds_the_param(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(match p { p => *p == old(*p) && true })]
fn match_rebinds_the_param_u8(p: &mut u8) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures((match p { p => *p == old(*p) }) && true)]
fn match_rebinds_the_param_in_a_conjunction(p: &mut u8) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures({ let p = p; *p == old(*p) })]
fn let_rebinds_the_param(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(if let p = p { *p == old(*p) } else { true })]
fn if_let_rebinds_the_param(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(match (p, 0) { (p, _) => *p == old(*p) })]
fn tuple_pattern_rebinds_the_param(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(match p { p => p@ == old(p@) })]
fn match_rebinds_the_param_view(p: &mut u32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(match p { q => *q == old(*p) })]
fn match_binds_the_param(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(if let q = p { *q == old(*p) } else { true })]
fn if_let_binds_the_param(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures({ let q = p; q@ == old(q@) })]
fn let_binds_the_param_view(p: &mut u32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(*(if true { p } else { p }) == old(*p))]
fn deref_of_a_branch(p: &mut i32) {
    *p += 1;
}

// Only `p` changes; the branch taken is `p`.
#[requires(*p < 100)]
#[ensures(*(if true { p } else { q }) == old(*p))]
fn deref_of_a_branch_of_two(p: &mut i32, q: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(*(if old(*p) > 1000 { p } else { p }) == old(*p))]
fn deref_of_a_branch_on_old(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(*(match 0 { _ => p }) == old(*p))]
fn deref_of_a_match(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(*(match b { true => p, false => p }) == old(*p))]
fn deref_of_a_match_on_a_param(p: &mut i32, b: bool) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(*(p, 0).0 == old(*p))]
fn deref_of_a_tuple_field(p: &mut i32) {
    *p += 1;
}

fn main() {}
