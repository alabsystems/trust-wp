//@ expect: verify
//@ xfail: D-129: a proof_assert reads no local a holder of its borrow may have written, and D-127
//@ xfail: counts every call or drop handed a value holding a borrow as a write through it, the
//@ xfail: `#[may_dangle]` destructors and `Vec::push` included, so `c` is refused as a stale read.
//@ mechanism: the isolating control for std_destructor_calls_user_code_unseen: the same kind of
//@ mechanism: borrowing value, held by a `Vec` and by a `Box` whose `Drop` impls take their element type
//@ mechanism: `#[may_dangle]`: they only drop the element, which has no glue, so no user code runs and
//@ mechanism: `c` keeps its value. `Vec::push` and `Box::new` are generic in the element and cannot
//@ mechanism: write through the borrow it holds. A scan that made every standard destructor over a
//@ mechanism: borrowing argument a hand-off fails here.
//@ accept-means: n/a (control): `c` is never written.
//@ fixed-by: n/a (control)
//@ teeth: control: verifies before and after D-140; refused (`stale read refused`) with D-129.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W<'a>(pub &'a mut u32);

pub fn vec_of_borrowers() {
    let mut c = 0u32;
    {
        let mut v: Vec<W<'_>> = Vec::new();
        v.push(W(&mut c));
    }
    proof_assert!(c@ == 0);
}

pub fn boxed_borrower() {
    let mut c = 0u32;
    {
        let _b = Box::new(W(&mut c));
    }
    proof_assert!(c@ == 0);
}
