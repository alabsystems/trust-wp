//@ expect: verify
//@ mechanism: control for program_ensures_none_through_pre_loop_loan_after_loop_read_as_some, writing `Some(2)` through the loan made before the loop where the case writes `None`, so the postcondition holds.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
//@ xfail: the post-loop walk forgets a local some loan points at when a write through a pointer may change it, and follows no loan to the local it names, so `result` is unbound and the check is `unknown (incomplete loop: no single post-loop return value)`; verified at the campaign tip only because the walk read `o` as the `Some(1)` it held before the loop. Following a loan to its local here is a completeness gap, not a soundness one.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result != None)]
pub fn prog(n: u32) -> Option<u32> {
    let mut o = Some(1u32);
    let r = &mut o;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    *r = Some(2);
    o
}
