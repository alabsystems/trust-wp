//@ expect: reject
//@ mechanism: the field spelling of the unnested `&mut &mut T` prophecy gap — `&mut (**qq).b` out of a `&mut &mut Struct` yields a borrow whose prophecy is tied to no field of the doubly-borrowed local, so the write through it constrains nothing.
//@ accept-means: an ACCEPT proves a write through a field borrow taken out of a nested `&mut` is invisible to the owner and the owner's entry value stays provable — the same unconstrained-term defect as the whole-value shape, reached through a field projection.
//@ fixed-by: 7bb3a696 — the resolver walks the unnesting hop by hop and keeps the field path to the owner.
//@ teeth: CLOSED in the adversarial direction: the case rejects, on the same resolution as the whole-value shape carried through a field path.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Pair {
    pub a: i32,
    pub b: i32,
}

pub fn mirror6() {
    let mut p = Pair { a: 0, b: 0 };
    let mut q = &mut p;
    let qq = &mut q;
    let inner: &mut i32 = &mut (**qq).b;
    *inner = 9;
    // FALSE: `*inner = 9` writes through qq -> q -> p, so p.b is 9 here.
    proof_assert!(p.b == 0);
}
