//@ expect: reject
//@ mechanism: two more `Drop` bodies that write through the `&mut` their value holds: one hands it to a
//@ mechanism: verified helper (`set5(self.0)`), one is generic over the pointee (`*self.0 = self.1` with
//@ mechanism: `T: Copy`); and a guard that is dropped on one arm of a branch. D-140's scan of a `Drop`
//@ mechanism: body treats any call handed a write capability, and any store through a dereference other
//@ mechanism: than into the value's own plain fields, as a write.
//@ accept-means: a host is reported `verified` although dropping the guard sets `c` to 5 on the path it
//@ accept-means: claims `c == 0`.
//@ WHY THE CONTRACT IS FALSE: `helper` and `generic` return 5; `branch(true)` returns 5.
//@ fixed-by: D-140
//@ teeth: MEASURED: with D-140's hand-off disabled every host is ACCEPTED, exit 0, `verified`; with it
//@ teeth: `helper` and `generic` are `unknown` and `branch` is FAILED with a counterexample.
//@ also-verified: set5, <H<'_> as std::ops::Drop>::drop, <P<'_, T> as std::ops::Drop>::drop, <G<'_> as std::ops::Drop>::drop
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

#[ensures((^r)@ == 5)]
pub fn set5(r: &mut u32) {
    *r = 5;
}

pub struct H<'a>(pub &'a mut u32);

impl Drop for H<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        set5(self.0);
    }
}

pub struct P<'a, T: Copy>(pub &'a mut T, pub T);

impl<T: Copy> Drop for P<'_, T> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = self.1;
    }
}

#[ensures(result@ == 0)]
pub fn helper() -> u32 {
    let mut c = 0u32;
    {
        let _h = H(&mut c);
    }
    c
}

#[ensures(result@ == 0)]
pub fn generic() -> u32 {
    let mut c = 0u32;
    {
        let _p = P(&mut c, 5u32);
    }
    c
}

#[ensures(result@ == 0)]
pub fn branch(b: bool) -> u32 {
    let mut c = 0u32;
    if b {
        let _g = G(&mut c);
    }
    c
}
