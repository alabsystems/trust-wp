//@ expect: reject
//@ mechanism: 444d896b treats a type parameter T as value-stable in the interior-mutability walk (ty_may_reach_interior_mutability), so a read through `c` is not re-bound after a call. That is sound only while Creusot logic cannot observe UnsafeCell memory behind T/dyn; this case is the guard for that argument.
//@ accept-means: f(&Cell::new(1)) computes 0 - 1 on u8 (`c.zap()` sets the cell to 0 between the two reads), which panics. Two reads of `val` through a type parameter T across a mutating call were conflated. FALSE.
//@ fixed-by: wp-s16 overflow-obligations v3 (444d896b argument); guard added at the s16 merge
//@ teeth: UNVERIFIED as a regression gate. No build with logic reading through T/dyn exists to show it accepting. Shape from the soundness review probes logic_gen_c / logic_dyn_c, FAILED on 42007ede
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::cell::Cell;

pub trait Tr {
    #[logic]
    fn val(&self) -> u8;
    #[ensures(result == self.val())]
    fn get2(&self) -> u8;
    fn zap(&self);
}

impl Tr for Cell<u8> {
    #[logic]
    fn val(&self) -> u8 {
        self.get()
    }
    #[ensures(result == self.val())]
    fn get2(&self) -> u8 {
        self.get()
    }
    fn zap(&self) {
        self.set(0)
    }
}

#[requires(true)]
pub fn f<T: Tr>(c: &T) -> u8 {
    let a = c.get2();
    c.zap();
    let b = c.get2();
    b - a
}
