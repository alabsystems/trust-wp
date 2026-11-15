//@ expect: verify
//@ xfail: D-141's price, the one D-118 pays for a written `requires`: the hand-off is refused whatever
//@ xfail: the option holds, because `Option::map` calls the item under no precondition this run can
//@ xfail: state (`caller` withdrawn). Creusot charges it at the combinator, where the value is known.
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of fn_item_generic_hop_to_std_map_typeinv_uncharged.rs: the value the
//@ mechanism: option holds keeps its invariant.
//@ teeth: control — refused before D-141 (`via` at its hop, D-75), verified while the hand-off owed
//@ teeth: nothing, refused once it owes the grant.
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
    Some(Sum10 { a: 3, b: 7 }).map(via::<Sum10>)
}
