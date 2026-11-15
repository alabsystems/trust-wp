//@ expect: verify
//@ xfail: the reborrow `set(&mut *x)` mints contradictory premises (the defect
//@ xfail: reborrow_call_final_credit_no_later_write_control.rs is xfail for), so W's impl is
//@ xfail: vacuous, proves nothing, and every credit resting on it is withdrawn although the
//@ xfail: contract is true. Retire when the reborrow-child chain stops contradicting the call.
//@ mechanism: the true twin of trait_impl_vacuous_body_grant_kept.rs, differing only in the value
//@ mechanism: the contract names. Before the fix both printed `go verified ✓` and `gen_bump verified ✓`;
//@ mechanism: after it both withdraw them. A vacuous implementation pays for no grant, true or not:
//@ mechanism: that is the price, and it lasts exactly as long as the vacuity does.
//@ accept-means: n/a (control): once W's impl is proved, `go` and `gen_bump` must verify.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

pub trait Bump {
    #[requires(*x == 0i32)]
    #[ensures(^x == 1i32)]
    fn bump(&self, x: &mut i32);
}

pub struct W;

impl Bump for W {
    fn bump(&self, x: &mut i32) {
        set(&mut *x);
    }
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn go(x: &mut i32) {
    W.bump(x)
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn gen_bump<T: Bump>(t: &T, x: &mut i32) {
    t.bump(x)
}
