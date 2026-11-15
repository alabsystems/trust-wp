//@ expect: verify
//@ xfail: `caller` is FAILED with a counterexample on a TRUE program, and was before D-141: the
//@ xfail: post-loop lane does not bind `s` to the value it was built as (its block collector starts
//@ xfail: at the entry block, which is not a post-loop block, and pins a user variable to its bare
//@ xfail: name), so the written `requires` over it is refuted with `s` arbitrary. No type invariant
//@ xfail: is involved. Retire this directive when the post-loop lane binds a local to the value it
//@ xfail: was built as. At D-165 `caller` is `unknown (incomplete loop: no single post-loop
//@ xfail: return value)` first: the post-loop return walk gives `total(s)`'s result no value, so
//@ xfail: `result` is unbound and the refutation is withheld.
//@ mechanism: the evidence twin of post_loop_callee_typeinv_uncharged_control: the same false
//@ mechanism: refutation with a WRITTEN precondition in place of the invariant grant.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Pair {
    pub a: i32,
    pub b: i32,
}

#[requires(s.a@ + s.b@ == 10)]
#[ensures(result@ == 10)]
pub fn total(s: Pair) -> i32 {
    s.a + s.b
}

#[ensures(result@ == 10)]
pub fn caller(n: u32) -> i32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let s = Pair { a: 3, b: 7 };
    total(s)
}
