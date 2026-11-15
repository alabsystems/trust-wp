//@ expect: reject
//@ mechanism: an `async fn` in a trait, called through a generic bound. The trait and each impl carry a synthesized associated type for the method's future, and that item has no name: the call graph asked every associated item of the impl for its name and the driver panicked before any verdict. With the crash gone, the impl method is refused as a coroutine item, and `f`, which only builds the future, is granted none of the `ensures(false)` a refused body owes: a call to an async method runs none of its body.
//@ accept-means: an async trait method's unproved contract discharges a generic caller's postcondition, or the driver crashes on an async trait method instead of refusing it.
//@ WHY IT IS FALSE: `f` returns 0 and claims `result@ == 1`.
//@ teeth: MEASURED on the parent: the driver panicked (`name of non-Rpitit assoc item`, exit 101), which the runner scores TEETH LOST (CRASH). Rejected at the fix: `<S as Tr>::m` refused, `f vacuous` while the call still granted the `ensures`, `f FAILED` once it grants none.
//@ fixed-by: D-117 — an associated item is matched by `opt_name`, so the synthesized future type of an async trait method is skipped
//@ verdict: failed
//@ fn-failed: f
//@ refused-with: which trust-wp does not verify; refused instead of credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(false)]
    async fn m(&self) -> u32;
}

pub struct S;
impl Tr for S {
    #[ensures(false)]
    async fn m(&self) -> u32 {
        0
    }
}

#[ensures(result@ == 1)]
pub fn f<T: Tr>(t: &T) -> u32 {
    let _fut = t.m();
    0
}
