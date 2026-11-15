//@ expect: reject
//@ fn-failed: caller
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: the generic spelling of fn_item_through_fnonce_call_once_typeinv_uncharged.rs, and the
//@ mechanism: one D-141 opened: `via<T: Total>` holds `inv_T(t)` (D-141's type-parameter grant),
//@ mechanism: which discharges its hop into the impl that holds `inv(self)`, and
//@ mechanism: `FnOnce::call_once(via::<Sum10>, (s,))` owed only `via`'s written `requires`: the
//@ mechanism: extern-spec lane replaced the `Fn*` spec with `via`'s own and never charged the grant.
//@ mechanism: `Fn::call(&via::<Sum10>, ..)`, `FnMut::call_mut` through a local, and a by-reference
//@ mechanism: `via_ref<T>(t: &T)` were ACCEPTED the same way and are rejected by the same fix.
//@ accept-means: a crate reported verified panics inside a function it credits: the call that fixed
//@ accept-means: `T` handed `via` a broken value and owed nothing for it.
//@ WHY THE CONTRACT IS FALSE: `caller` hands `via` `Sum10 { a: 1, b: 1 }`, the impl returns 2, so
//@ WHY THE CONTRACT IS FALSE: `100 / (r - 2)` panics; `caller` claims to return 10.
//@ fixed-by: D-141 — a fn item whose body holds a parameter invariant premise keeps the `Fn*`
//@ fixed-by: spec's opaque `precondition` (`resolve_effective_spec`).
//@ teeth: MEASURED REJECTED on wp-campaign's code, which has no D-141 (`via` unknown: its hop was
//@ teeth: refused under D-75); ACCEPTED, exit 0 (`via verified`, `caller verified`) on this branch
//@ teeth: with the fix knobbed off, one build; `caller` FAILED with it on.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(fn_traits, unboxed_closures)]

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for Sum10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self) -> i32;
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T) -> i32 {
    let r = t.total();
    100 / (r - 2) + 10 - 100 / (r - 2)
}

#[ensures(result@ == 10)]
pub fn caller() -> i32 {
    FnOnce::call_once(via::<Sum10>, (Sum10 { a: 1, b: 1 },))
}
