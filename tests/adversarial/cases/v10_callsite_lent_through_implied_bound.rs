//@ expect: reject
//@ mechanism: `params_lent_into_another_parameter` built its outlives relation from the INPUT
//@ mechanism: types (and closure captures) and the explicit bounds of the item and its parents.
//@ mechanism: Borrowck also assumes the output type and an enclosing impl's header well-formed:
//@ mechanism: `-> Option<&'b &'a ()>` implies `'a: 'b`, and so does `impl<'a, 'b> P<'a, 'b>`
//@ mechanism: for `struct P<'a, 'b>(PhantomData<&'b &'a ()>)`. Under either bound the body stores
//@ mechanism: `p: &'a mut i32` into `slot: &mut Option<&'b mut i32>`, the signature recorded no
//@ mechanism: lend, and the callee's `^p == *p` was read at each call.
//@ accept-means: a caller is credited with the final value of a borrow it lent into another
//@ accept-means: argument under an outlives bound the signature analysis did not read.
//@ WHY THE CONTRACT IS FALSE: each caller writes 5 through the slot the callee stored `x` in, so
//@ WHY THE CONTRACT IS FALSE: `^x` is 5 and the precondition makes the entry `*x` something else.
//@ fixed-by: D-108 (the outlives relation also reads the output type and the impl header)
//@ teeth: MEASURED (debug driver): f6039647 verifies `stash_ret_caller` and
//@ teeth: `stash_impl_caller`; on D-108 both callee clauses are refused by name and no caller
//@ teeth: verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::marker::PhantomData;

use creusot_std::prelude::*;

#[ensures(^p == *p)]
pub fn stash_ret<'a, 'b>(p: &'a mut i32, slot: &mut Option<&'b mut i32>) -> Option<&'b &'a ()> {
    *slot = Some(p);
    None
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_ret_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    let _ = stash_ret(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

pub struct P<'a, 'b>(PhantomData<&'b &'a ()>);

impl<'a, 'b> P<'a, 'b> {
    #[ensures(^p == *p)]
    pub fn stash(p: &'a mut i32, slot: &mut Option<&'b mut i32>) {
        *slot = Some(p);
    }
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_impl_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    P::stash(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}
