//@ expect: reject
//@ mechanism: a `&mut` moved into a TUPLE field and written through it. The named-struct
//@ mechanism: spelling of this shape is gated by struct_held_borrow_write_lost.rs; the tuple
//@ mechanism: aggregate is a separate constructor path and carries no chain edge either, so
//@ mechanism: gating only the struct leaves the same defect reachable one keystroke away.
//@ fixed-by: 7bb3a696 — the resolver reads the borrow back out of the aggregate constructor; the tuple constructor is the same hop as the struct one.
//@ accept-means: a write through a borrow held in a tuple is invisible to a later read of
//@ accept-means: the borrowed local, so any aggregate can launder a write out of existence.
//@ teeth: CLOSED in the adversarial direction: the case rejects, on the same
//@ teeth: aggregate hop as the struct spelling. The corpus carries no control for it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let t = (&mut x,);
    *t.0 = 7;
    proof_assert!(x == 5i32);
}
