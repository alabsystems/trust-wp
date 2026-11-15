//@ expect: reject
//@ fn-failed: <Sum10 as std::clone::Clone>::clone
//@ mechanism: `Vec::clone` runs a local `impl Clone for Sum10` on every element: std's body makes the
//@ mechanism: call, and no lane walks it. A local impl of a FOREIGN trait's method holds no parameter
//@ mechanism: premise (`implements_foreign_trait_method`), so `clone`, which divides by a value only
//@ mechanism: the invariant bounds, is refuted. Its goal `inv(result)` stays owed. With the premise,
//@ mechanism: `clone` was credited on `inv(*self)` that no call owed (`caller` is refused for its own
//@ mechanism: reasons, so the run was rejected while `clone`'s credit was false).
//@ accept-means: a crate credits as panic-free a trait impl std runs on a value that breaks the
//@ accept-means: invariant the impl was granted.
//@ WHY THE PROGRAM IS WRONG: `v.clone()` runs `clone` on a `Sum10` with `a + b == 2`, and `100 / (r - 2)`
//@ WHY THE PROGRAM IS WRONG: divides by zero.
//@ fixed-by: D-141 — an impl of a foreign trait's method holds no parameter premise.
//@ teeth: MEASURED on one build with the three route arms knobbed off: `clone` verified (the
//@ teeth: per-function gate's TEETH LOST); with them, `clone` FAILED.
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

impl Clone for Sum10 {
    fn clone(&self) -> Sum10 {
        let r = self.a + self.b;
        let _q = 100 / (r - 2);
        Sum10 { a: self.a, b: self.b }
    }
}

#[ensures(true)]
pub fn caller() -> usize {
    let v = vec![Sum10 { a: 1, b: 1 }];
    let w = v.clone();
    w.len()
}
