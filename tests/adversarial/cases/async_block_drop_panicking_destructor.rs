//@ expect: reject
//@ mechanism: the drop spelling beside D-117's obligation list. A coroutine body is refused only when it owes something, and a MIR `Drop` is on the short list of terminators that owe nothing, as it owes nothing at a contract-free program fn's drop site. That is sound only because a local destructor's body is a verification target of its own: here the `async` block's single obligation is the drop of a `D`, whose destructor panics at `self.0 == 3`, and the rejection must come from `D::drop` itself.
//@ accept-means: a destructor that panics, run by a coroutine body, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: `f(3)` builds a block that, when polled, drops `D(3)`, and `D::drop` panics at `self.0 == 3`.
//@ teeth: UNVERIFIED as a gate of D-117: rejected on the parent commit as well, because `<D as std::ops::Drop>::drop` is examined as its own item (`unknown`). It pins the premise the obligation list rests on; the sync twin (the same `let _d = D(x)` in `f` itself) is rejected on `D::drop` in the same way.
//@ verdict: unknown
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct D(pub u32);

impl Drop for D {
    fn drop(&mut self) {
        if self.0 == 3 {
            panic!()
        }
    }
}

pub fn f(x: u32) {
    let _fut = async move {
        let _d = D(x);
    };
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
