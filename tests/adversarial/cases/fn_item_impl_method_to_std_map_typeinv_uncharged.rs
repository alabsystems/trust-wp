//@ expect: reject
//@ also-verified: <Sum10 as Total>::total
//@ mechanism: the impl method `<Sum10 as Total>::total`, granted `inv(self)`, handed to `Option::map`
//@ mechanism: as a fn item: the combinator calls it with whatever the option holds. The hand-off scan
//@ mechanism: resolves the item to the impl that runs and refuses it for that grant
//@ mechanism: (`fn_item_precondition_unstated` reading `call_may_enter_invariant_grant`), so `caller`'s
//@ mechanism: verdict is withdrawn.
//@ accept-means: a crate reported verified panics inside a trait impl it credits as panic-free, called
//@ accept-means: by a std combinator with a value that breaks the invariant the impl was granted.
//@ WHY THE PROGRAM IS WRONG: `Option::map` calls `total` on a `Sum10` with `a + b == 2`, and `100 / (r - 2)`
//@ WHY THE PROGRAM IS WRONG: in `total` divides by zero.
//@ fixed-by: D-141 — a hand-off of a fn item granted a parameter invariant withdraws the host.
//@ teeth: MEASURED on one build with the three route arms knobbed off: ACCEPTED, exit 0, `total` and
//@ teeth: `caller` verified; with them, `caller` withdrawn.
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
        let r = self.a + self.b;
        100 / (r - 2) + 10 - 100 / (r - 2)
    }
}

#[ensures(true)]
pub fn caller() -> Option<i32> {
    Some(Sum10 { a: 1, b: 1 }).map(<Sum10 as Total>::total)
}
