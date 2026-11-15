//@ expect: reject
//@ mechanism: a `&mut` local is MOVED into a second local and the source local is then reassigned to a different place (`let r2 = r; r = &mut y;`) before the write through the moved copy. The reassignment drops the edge the source held and the moved copy's own edge is derived from that source, so `*r2 = 7` reaches nothing and the original target keeps its entry value — a move edge invalidated by a later write to the local it was copied FROM.
//@ fixed-by: ?
//@ accept-means: reassigning a borrow local retroactively erases the target of a copy taken from it earlier, so a write already committed through that copy is proved never to have happened.
//@ WHY THE PROGRAM IS WRONG: `r2` is the original `&mut x`; `*r2 = 7` sets `x` to 7, and the assertion claims 5.
//@ teeth: RED, open. OBSERVED ACCEPTED by this runner on the tip that carries the case, and ACCEPTED by the campaign binary too, so the hole pre-exists this corpus entry. Its control is `xfail`: the true twin does not verify either, which is the signature of a write that reached nothing.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let mut y = 5i32;
    let mut r: &mut i32 = &mut x;
    let r2 = r;
    r = &mut y;
    *r2 = 7;
    *r = 8;
    proof_assert!(x == 5i32);
}
