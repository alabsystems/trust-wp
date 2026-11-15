//@ expect: verify
//@ timeout: 300
//@ mechanism: the value twin of generic_hop_typeinv_mut_ref: 3 and 7 keep the invariant. The owed
//@ mechanism: clause is `inv(*v)` over the aggregate `caller` wrote, and the D-65 unfold reads `*ctor`
//@ mechanism: as the encoder does, the dereference distributed into the constructor's arguments.
//@ mechanism: With that reading disabled by a local knob this twin is refuted on a TRUE program, the
//@ mechanism: `inv(*ctor)` symbol left undecided (D-141).
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

pub trait Bump {
    #[ensures(result@ == 10)]
    fn total_mut(&mut self) -> i32;
}

impl Bump for Sum10 {
    fn total_mut(&mut self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Bump>(t: &mut T) -> i32 {
    t.total_mut()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 3;
    s.b = 7;
    via(&mut s)
}
