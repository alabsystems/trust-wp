//@ expect: verify
//@ timeout: 300
//@ mechanism: the value twin of generic_hop_typeinv_mut_ref_type_argument: 3 and 7 keep the
//@ mechanism: invariant, so the charge at the call that fixes `T` is paid and every function
//@ mechanism: verifies. The pair differs in the value alone (D-68).
//@ mechanism: The clause owed is `inv(*v)` over the aggregate `caller` wrote; the D-65 unfold
//@ mechanism: reads `*ctor` as the encoder does, the dereference distributed into the
//@ mechanism: constructor's arguments. With that reading disabled by a local knob this twin
//@ mechanism: is refuted on a TRUE program, the `inv(*ctor)` symbol left undecided.
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

impl<'a> Total for &'a mut Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 3;
    s.b = 7;
    via(&mut s)
}
