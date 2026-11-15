//@ expect: reject
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: D-141 grants `via<T>` the premise `inv_T(t)` and makes a CALL that fixes `T` owe it
//@ mechanism: there. Handing the fn item `via::<Sum10>` to `Option::map` fixes `T` without a call in
//@ mechanism: `caller`: the combinator calls it with whatever the option holds. The D-118 hand-off scan
//@ mechanism: (`fn_item_precondition_unstated`) refuses a local fn item whose body a call would owe a
//@ mechanism: parameter invariant, on the predicate that makes a direct caller a target
//@ mechanism: (`call_may_enter_invariant_grant`), so `caller`'s verdict is withdrawn and the run is
//@ mechanism: rejected. Calling `via::<Sum10>` directly with the same value is refuted (`caller`
//@ mechanism: FAILED). The concrete-parameter spelling is fn_item_to_std_map_param_typeinv_uncharged.rs.
//@ accept-means: a crate reported verified panics inside a function it credits as panic-free, called
//@ accept-means: by a std combinator with a value that breaks the invariant the function was granted.
//@ WHY THE PROGRAM IS WRONG: `Option::map` hands `via` a `Sum10` with `a + b == 2`, the impl returns
//@ WHY THE PROGRAM IS WRONG: 2, and `100 / (r - 2)` in `via` divides by zero.
//@ fixed-by: D-141 — a hand-off of a fn item granted a parameter invariant withdraws the host, as
//@ fixed-by: D-118 does for a written `requires`.
//@ teeth: MEASURED on one build with the hand-off's grant arm knobbed off: ACCEPTED, exit 0, `via` and
//@ teeth: `caller` verified; with it, `caller` withdrawn. REJECTED on the build before D-141 too
//@ teeth: (`via` refused at its hop, D-75).
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

#[ensures(true)]
pub fn caller() -> Option<i32> {
    Some(Sum10 { a: 1, b: 1 }).map(via::<Sum10>)
}
