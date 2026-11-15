//@ expect: reject
//@ mechanism: an impl whose body verdict is VACUOUS never discharged the contract it inherited, and
//@ mechanism: the trait-credit ledger read it as discharged. The reborrow `set(&mut *x)` mints
//@ mechanism: contradictory premises (the defect reborrow_call_final_credit_no_later_write_control.rs
//@ mechanism: is xfail for), so `<W as Bump>::bump` reports `vacuous (contradictory premises)`, which
//@ mechanism: counts in `counters.vacuous` and not in `verified`: no genuine proof was produced.
//@ mechanism: `end_item` recorded a shortfall only for a panic, a failure, a withheld refutation, an
//@ mechanism: error, an assumption or no verdict at all, so a vacuous body recorded nothing, and `go`
//@ mechanism: (pinned to W's impl) and `gen_bump` (any impl) kept the trait grant.
//@ fixed-by: a vacuous verdict on an implementation is a shortfall, as an error is (`end_item`)
//@ accept-means: `go` and `gen_bump` claim `^x == 2`; the body that runs writes 1.
//@ teeth: MEASURED before the fix: `go verified ✓` and `gen_bump verified ✓` beside `<W as Bump>::bump vacuous (contradictory premises)`, with no withdrawal. Its twin trait_impl_vacuous_body_grant_kept_true_twin.rs differs only in the value the contract names (`1`, which is true) and printed the identical lines: the verdict did not depend on the truth.
//@ also-verified: set
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
    #[ensures(^x == 2i32)]
    fn bump(&self, x: &mut i32);
}

pub struct W;

impl Bump for W {
    fn bump(&self, x: &mut i32) {
        set(&mut *x);
    }
}

#[requires(*x == 0i32)]
#[ensures(^x == 2i32)]
pub fn go(x: &mut i32) {
    W.bump(x)
}

#[requires(*x == 0i32)]
#[ensures(^x == 2i32)]
pub fn gen_bump<T: Bump>(t: &T, x: &mut i32) {
    t.bump(x)
}
