//@ expect: verify
//@ xfail: D-129: a proof_assert reads no local a holder of its borrow may have written, and D-127
//@ xfail: counts every call handed a value holding a borrow as a write through it, `Vec::push`
//@ xfail: included, whatever the callee is; so `c` is refused as a stale read. D-140's scan, which
//@ xfail: asks whether the callee can write through the borrow, lets both calls through.
//@ mechanism: the isolating control for drop_glue_run_in_place_by_callee_unseen and
//@ mechanism: drop_glue_reach_through_call_stored_borrow_unseen: the same guard is pushed into a `Vec`
//@ mechanism: and the `Vec` forgotten, with no `clear` and no `Drop` between, so no glue runs.
//@ mechanism: `Vec::push` and `mem::forget` are standard functions that never drop a value of their
//@ mechanism: type argument, and being generic in it they cannot write through the borrow it holds, so
//@ mechanism: neither is a hand-off and `c` keeps its value. A hand-off at every call handed a guard,
//@ mechanism: or at every call handed a `&mut Vec<G>`, fails here.
//@ accept-means: n/a (control): `c` is never written.
//@ fixed-by: n/a (control)
//@ teeth: control: verifies before and after D-140; refused (`stale read refused`) with D-129.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

pub fn pushed_then_forgotten() {
    let mut c = 0u32;
    let mut v: Vec<G<'_>> = Vec::new();
    v.push(G(&mut c));
    std::mem::forget(v);
    proof_assert!(c@ == 0);
}
