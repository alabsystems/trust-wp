//@ expect: reject
//@ mechanism: a `&mut` local reassigned from another borrow local (`let q = &mut y; r = q;`) and then written: the write through `r` reaches neither the place `r` was first created on nor the place it was reassigned to, so the NEW target keeps its entry value. The corpus already gates the old target staying wrongly credited; dropping that stale edge did not record the new one, and this half of the same reassignment is still open.
//@ fixed-by: ?
//@ accept-means: after a borrow local is reassigned, a write through it is attributed to no place at all, so the place it now points at is proved unchanged by a write that hit it.
//@ WHY THE PROGRAM IS WRONG: after `r = q`, `r` points at `y`; `*r = 7` sets `y` to 7, and the assertion claims 5.
//@ teeth: RED, open. OBSERVED ACCEPTED by this runner on the tip that carries the case, and ACCEPTED by the campaign binary too, so the hole pre-exists this corpus entry. Its control asserts the TRUE half of the same post-state and VERIFIES, so the accept is a real hole and not blanket over-refusal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let mut y = 5i32;
    let mut r: &mut i32 = &mut x;
    let q: &mut i32 = &mut y;
    r = q;
    *r = 7;
    proof_assert!(y == 5i32);
}
