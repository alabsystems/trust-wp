//@ expect: reject
//@ also-verified: take
//@ mechanism: the concrete-parameter spelling of fn_item_generic_hop_to_std_map_typeinv_uncharged.rs.
//@ mechanism: `take(t: Sum10)` is granted `inv(t)` by the parameter-clause builder and every call the
//@ mechanism: spec table reaches owes it; handed to `Option::map` it is called by the combinator, and
//@ mechanism: the D-118 hand-off scan refuses it for that grant as it refuses a WRITTEN `#[requires]`
//@ mechanism: (fn_item_requires_through_option_map_uncharged.rs), so `caller`'s verdict is withdrawn.
//@ accept-means: a crate reported verified panics inside a function it credits as panic-free, called
//@ accept-means: by a std combinator with a value that breaks the invariant the function was granted.
//@ WHY THE PROGRAM IS WRONG: `Option::map` hands `take` a `Sum10` with `a + b == 2`, and
//@ WHY THE PROGRAM IS WRONG: `100 / (r - 2)` in `take` divides by zero.
//@ fixed-by: D-141 — the hand-off refusal that closes its generic sibling.
//@ teeth: MEASURED on one build with the hand-off's grant arm knobbed off: ACCEPTED, exit 0, `take` and
//@ teeth: `caller` verified; with it, `caller` withdrawn. ACCEPTED on the build before D-141 as well.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

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

#[ensures(true)]
pub fn caller() -> Option<i32> {
    Some(Sum10 { a: 1, b: 1 }).map(take)
}
