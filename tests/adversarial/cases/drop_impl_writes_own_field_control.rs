//@ expect: verify
//@ xfail: D-127 counts a drop of a value holding a borrow as a store through it, whatever the
//@ xfail: `Drop` impl's body does (it is not read), so the host's read of `c` is stale and fails
//@ xfail: closed; D-140's scan, which reads the body, lets this store through.
//@ mechanism: the isolating control for drop_impl_write_through_held_mut_unseen on the other side from
//@ mechanism: drop_impl_reads_held_mut_control: the `Drop` impl DOES store, but into a plain field of the
//@ mechanism: dying value itself (`self.1 = 0`), never through the `&mut` it holds. D-140's scan lets
//@ mechanism: exactly that store through; a scan that refused every store behind `self`'s dereference
//@ mechanism: fails here.
//@ accept-means: n/a (control): `c` is never written.
//@ fixed-by: n/a (control)
//@ teeth: control: verifies before and after D-140, and with D-127's drop arm disabled by a local
//@ teeth: knob on a tree that carries both; `unknown` with that arm in place.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32, pub u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        self.1 = 0;
    }
}

#[ensures(result@ == 0)]
pub fn host() -> u32 {
    let mut c = 0u32;
    {
        let _g = G(&mut c, 1);
    }
    c
}
