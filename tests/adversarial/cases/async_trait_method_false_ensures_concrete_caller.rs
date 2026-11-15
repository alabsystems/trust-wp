//@ expect: reject
//@ mechanism: the concrete-receiver spelling of async_trait_method_false_ensures_generic_caller: `s.m()` on `&S` resolves straight to the impl method, and that item is refused as a coroutine item. `f`, which only builds the future, is granted none of the `ensures(false)` a refused body owes: a call to an async method runs none of its body.
//@ accept-means: an async trait method's unproved contract discharges a concrete caller's postcondition.
//@ WHY IT IS FALSE: `f` returns 0 and claims `result@ == 1`.
//@ teeth: UNVERIFIED as a gate: rejected on the parent too (`<S as Tr>::m` refused, `f vacuous`, the `ensures` still granted at the call); only the generic spelling reached the associated-item scan that panicked. `f FAILED` once the call grants nothing. It pins the grant side for a concrete receiver.
//@ fixed-by: n/a (rejected on the parent as well; a pin of the grant side beside its generic twin)
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
pub fn f(s: &S) -> u32 {
    let _fut = s.m();
    0
}
