//@ expect: verify
//@ xfail: D-141's price, the one D-118 pays for a written `requires`: the hand-off is refused whatever
//@ xfail: the option holds (`caller` withdrawn).
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of fn_item_to_std_map_param_typeinv_uncharged.rs: the value the option
//@ mechanism: holds keeps its invariant.
//@ teeth: control — verified before D-141, on a premise the hand-off never owed.
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
    Some(Sum10 { a: 3, b: 7 }).map(take)
}
