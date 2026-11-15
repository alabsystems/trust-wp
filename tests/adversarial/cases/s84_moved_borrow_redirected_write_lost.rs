//@ expect: reject
//@ mechanism: the moved-borrow shape of s84_moved_borrow_write_lost after the borrow local was REDIRECTED through a pointer to it (`let rr = &mut r; *rr = &mut y;`): the write through the moved copy `r2` reaches neither the place `r` was created on nor the place it was redirected to, so `y` keeps its entry value. A moved-borrow chain edge cannot close this — `r`'s own address escapes, so no chain can say where `r2` points — and nothing forgets `y` either.
//@ accept-means: a borrow local redirected through `&mut &mut` and then moved freezes both candidate targets at their entry values.
//@ WHY THE PROGRAM IS WRONG: after `*rr = &mut y`, `r` points at `y`; `r2` is `r`; `*r2 = 7` sets `y` to 7, and the assertion claims 5.
//@ teeth: LIVE on the campaign tip 684821d0: ACCEPTED, base_exit_code=0
//@ teeth: on this `y == 5` spelling of the program. The `x == 7` side
//@ teeth: is refuted (z_escape_redirect_move_false.out), as it should be. PRE-EXISTING; found by this
//@ teeth: front's probes.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let mut y = 5i32;
    let mut r: &mut i32 = &mut x;
    let rr: &mut &mut i32 = &mut r;
    *rr = &mut y;
    let r2 = r;
    *r2 = 7;
    proof_assert!(y == 5i32);
}
