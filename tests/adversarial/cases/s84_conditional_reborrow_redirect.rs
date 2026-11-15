//@ expect: reject
//@ mechanism: a `&mut` local reassigned on ONE branch (`let mut t = &mut x; if c { t = &mut y; }`) and written after the join: the substitution lane's borrow chain for `t` is per-branch state, and the merged substitutions carry the write to NEITHER target — `x` and `y` both keep their entry values (`x == 5` and `y == 5` are each accepted; the exact disjunction is refuted).
//@ accept-means: a write through a conditionally redirected borrow is dropped at the join, so every read of either possible target sees the entry value — a false accept on whichever side the assertion picks.
//@ WHY THE PROGRAM IS WRONG: when `c` is false, `t` still points at `x` and `*t = 7` sets `x` to 7; the assertion claims 5 unconditionally.
//@ teeth: LIVE on the campaign tip 684821d0: ACCEPTED, base_exit_code=0
//@ teeth: (z_redirect_plain_false2.out); the `y == 5` side is
//@ teeth: ACCEPTED too (z_redirect_plain_false3.out) and the exact control is REFUTED
//@ teeth: (z_redirect_plain_control.out). PRE-EXISTING; found by this front's probes.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k(c: bool) {
    let mut x = 5i32;
    let mut y = 5i32;
    let mut t: &mut i32 = &mut x;
    if c {
        t = &mut y;
    }
    *t = 7;
    proof_assert!(x == 5i32);
}
