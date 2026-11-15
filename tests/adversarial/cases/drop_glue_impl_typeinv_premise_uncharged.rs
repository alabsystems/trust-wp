//@ expect: reject
//@ fn-failed: <Sum10 as std::ops::Drop>::drop
//@ also-verified: dropper
//@ mechanism: drop glue is not a call: the drop site credits a contracted `Drop::drop(&mut self)`
//@ mechanism: through its written contract (cp_drop_control.rs) and can owe nothing else, so a local
//@ mechanism: impl of a FOREIGN trait's method is granted no parameter premise
//@ mechanism: (`implements_foreign_trait_method`), the `inv(*self)` side condition of a `&mut`
//@ mechanism: receiver included. `drop`, which divides by a value only the invariant bounds, is
//@ mechanism: refuted. `dropper` is credited TRUE: its drop owes the written `requires(true)` alone,
//@ mechanism: and `drop` is the function whose body breaks its contract. Before the foreign impl lost
//@ mechanism: its premise, `drop` was credited on `inv(*self)` and the crate exited 0.
//@ accept-means: a crate reported verified panics inside a destructor it credits as panic-free, run
//@ accept-means: by drop glue on a value that breaks the invariant the destructor was granted.
//@ WHY THE PROGRAM IS WRONG: dropping `_d` runs `drop` on a `Sum10` with `a + b == 2`, and
//@ WHY THE PROGRAM IS WRONG: `100 / (r - 2)` divides by zero.
//@ fixed-by: D-141 — an impl of a foreign trait's method holds no parameter premise.
//@ teeth: MEASURED on one build with foreign impls granted again by a knob: ACCEPTED, exit 0, `drop`
//@ teeth: and `dropper` verified; with the rule, `drop` FAILED. ACCEPTED on the build before D-141 too.
//@ timeout: 300
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

impl Drop for Sum10 {
    #[requires(true)]
    #[ensures(true)]
    fn drop(&mut self) {
        let r = self.a + self.b;
        let _q = 100 / (r - 2);
    }
}

#[ensures(result@ == x@)]
pub fn dropper(x: u8) -> u8 {
    let _d = Sum10 { a: 1, b: 1 };
    x
}
