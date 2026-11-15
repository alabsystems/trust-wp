//@ expect: reject
//@ fn-failed: <Sum10 as std::ops::Drop>::drop
//@ mechanism: a `Vec`'s drop glue runs a local `impl Drop for Sum10` on every element, the spelling of
//@ mechanism: drop_glue_impl_typeinv_premise_uncharged.rs one container down and with no written
//@ mechanism: contract on `drop`. A local impl of a FOREIGN trait's method holds no parameter premise
//@ mechanism: (`implements_foreign_trait_method`), the `inv(*self)` side condition of a `&mut`
//@ mechanism: receiver included, so `drop`, which divides by a value only the invariant bounds, is
//@ mechanism: refuted. With the premise, `drop` was credited on a premise no drop owed (`dropper` is
//@ mechanism: refused for its own reasons, so the run was rejected while `drop`'s credit was false).
//@ accept-means: a crate credits as panic-free a destructor drop glue runs on a value that breaks the
//@ accept-means: invariant the destructor was granted.
//@ WHY THE PROGRAM IS WRONG: dropping `_v` runs `drop` on a `Sum10` with `a + b == 2`, and `100 / (r - 2)`
//@ WHY THE PROGRAM IS WRONG: divides by zero.
//@ fixed-by: D-141 — an impl of a foreign trait's method holds no parameter premise.
//@ teeth: MEASURED on one build with the three route arms knobbed off: `drop` verified (the
//@ teeth: per-function gate's TEETH LOST); with them, `drop` FAILED.
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
    fn drop(&mut self) {
        let r = self.a + self.b;
        let _q = 100 / (r - 2);
    }
}

#[ensures(result@ == x@)]
pub fn dropper(x: u8) -> u8 {
    let _v = vec![Sum10 { a: 1, b: 1 }];
    x
}
