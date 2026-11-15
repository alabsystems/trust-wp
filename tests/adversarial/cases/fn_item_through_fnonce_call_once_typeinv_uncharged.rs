//@ expect: reject
//@ fn-failed: caller
//@ also-verified: take
//@ mechanism: a fn item called through the `Fn*` trait's own method, `FnOnce::call_once(take, (s,))`.
//@ mechanism: `take`'s body holds its parameter's invariant `inv(t)` as a premise (the grant the spec
//@ mechanism: table stores), so every call into it owes that clause. The extern-spec lane replaced
//@ mechanism: the `Fn*` spec with `take`'s own and stated its WRITTEN clauses alone: the same route
//@ mechanism: with a callee `#[requires(x@ != 0)]` handed `0` is refuted at the site (`(0@ != 0)`),
//@ mechanism: while the grant was charged by no one. The by-reference spelling (`take_ref(t: &Sum10)`)
//@ mechanism: and an inherent method path (`Sum10::total`) were ACCEPTED the same way;
//@ mechanism: fn_item_through_fn_call_typeinv_uncharged.rs and
//@ mechanism: fn_item_through_fnmut_call_mut_typeinv_uncharged.rs are the `Fn::call` and `FnMut::call_mut`
//@ mechanism: spellings, generic_fn_item_through_fnonce_call_once_typeinv_uncharged.rs the generic one.
//@ mechanism: Refuted at the site on the build without the fix: a trait impl method
//@ mechanism: (`<Sum10 as Tr>::m`), a `fn` pointer, a closure, this call inside a loop, and the
//@ mechanism: stable spellings `let f = &take; f(s)` and `let f = take; f(s)`.
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
    FnOnce::call_once(take, (Sum10 { a: 1, b: 1 },))
}
