//@ expect: reject
//@ mechanism: the async-trait-method spelling of async_fn_mut_param_ensures_granted_at_unpolled_call, through a generic bound (`T: Tr`); its twin async_trait_mut_param_ensures_granted_concrete_caller calls on a concrete receiver. Calling an `async fn` in a trait runs none of the impl's body either, so the declaration's `ensures` is no fact of the call.
//@ accept-means: a caller is credited on the postcondition of an async trait method whose body its call does not run.
//@ WHY IT IS FALSE: the future is dropped unpolled, so `f` returns 0 and claims `result@ == 5`.
//@ teeth: MEASURED on the parent: `<S as Tr>::m` refused, `f verified ✓`. At the fix `f` is not credited.
//@ fixed-by: D-117 — `ensures_granted_at_call` grants a call to an item that only builds a coroutine none of its `ensures`, in the user and the trait spec table alike
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[ensures((^x)@ == 5)]
    async fn m(&self, x: &mut u32);
}

pub struct S;
impl Tr for S {
    #[ensures((^x)@ == 5)]
    async fn m(&self, x: &mut u32) {
        *x = 5;
    }
}

#[ensures(result@ == 5)]
pub fn f<T: Tr>(t: &T) -> u32 {
    let mut y = 0u32;
    drop(t.m(&mut y));
    y
}
