//@ expect: reject
//@ mechanism: a borrow local reassigned DIRECTLY to a fresh borrow (`r = &mut y`) with no
//@ mechanism: intermediate borrow local. reassigned_borrow_new_target_write_lost.rs gates the
//@ mechanism: spelling that goes through a temporary; this one drops the stale edge and
//@ mechanism: records none for the new target, so the write lands nowhere.
//@ fixed-by: ?
//@ accept-means: reassigning a borrow to a new place makes every later write through it
//@ accept-means: invisible, so the new target keeps its entry value however often it is written.
//@ teeth: RED, open. OBSERVED ACCEPTED by this runner on the tip that carries the case and
//@ teeth: ACCEPTED by the campaign binary, so the hole pre-exists this entry. The program is
//@ teeth: wrong by execution: `*r = 7` sets y to 7 and the assertion claims 5.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let mut y = 5i32;
    let mut r: &mut i32 = &mut x;
    r = &mut y;
    *r = 7;
    proof_assert!(y == 5i32);
}
