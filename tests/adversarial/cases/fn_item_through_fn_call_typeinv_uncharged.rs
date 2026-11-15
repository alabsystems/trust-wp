//@ expect: reject
//@ fn-failed: caller
//@ also-verified: take
//@ mechanism: the `Fn::call(&take, (s,))` spelling of
//@ mechanism: fn_item_through_fnonce_call_once_typeinv_uncharged.rs: the extern-spec lane stated
//@ mechanism: `take`'s written `#[requires]` in place of the `Fn*` spec, and not the parameter
//@ mechanism: invariant its body holds.
//@ accept-means: a crate reported verified panics inside a function it credits, because the call that
//@ accept-means: broke that function's invariant premise owed nothing.
//@ WHY THE CONTRACT IS FALSE: `caller` hands `take` `Sum10 { a: 1, b: 1 }`, so `r - 2 == 0` and
//@ WHY THE CONTRACT IS FALSE: `100 / (r - 2)` panics; `caller` claims to return 10.
//@ fixed-by: D-141 — a fn item whose body holds a parameter invariant premise keeps the `Fn*`
//@ fixed-by: spec's opaque `precondition` (`resolve_effective_spec`): the item's own spec stands in
//@ fixed-by: for it only while its written `requires` is all a call into it owes.
//@ teeth: MEASURED on one build with the fix below knobbed off: ACCEPTED, exit 0 (`take verified`,
//@ teeth: `caller verified`), as on wp-campaign's code, which has no D-141 — the concrete grant
//@ teeth: predates it. With the fix on, `caller` FAILED on its opaque `precondition`.
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

#[ensures(result@ == 10)]
pub fn take(t: Sum10) -> i32 {
    let r = t.a + t.b;
    100 / (r - 2) + 10 - 100 / (r - 2)
}

#[ensures(result@ == 10)]
pub fn caller() -> i32 {
    Fn::call(&take, (Sum10 { a: 1, b: 1 },))
}
