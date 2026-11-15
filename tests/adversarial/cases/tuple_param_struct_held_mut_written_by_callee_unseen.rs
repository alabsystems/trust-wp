//@ expect: reject
//@ also-verified: destructured, plain
//@ mechanism: the tuple spellings of by_value_held_mut_written_by_callee_unseen.rs: a callee takes a
//@ mechanism: tuple whose first element is a struct holding a `&mut` and writes through it, once
//@ mechanism: through a destructuring parameter `(w, _q): (W, i32)` and once through a plain tuple
//@ mechanism: parameter `t: (W, i32)`. D-181 reads such a parameter as holding a `&mut` for the
//@ mechanism: state rule, and D-179 opened the call lane to a destructured `&mut`, which makes the
//@ mechanism: caller's `*x` unknown after the call when the tuple holds the `&mut` directly
//@ mechanism: (destructured_mut_ref_callee_write_reaches_caller.rs). Held below a struct field the
//@ mechanism: call lane gives the pointee no post-call value, so the host reads `a` after the call at
//@ mechanism: its value before it. Found probing sideways from D-179 and D-181.
//@ accept-means: a host is reported `verified` although the callee sets `a` to 5 through the borrow it
//@ accept-means: was handed inside a tuple.
//@ WHY THE CONTRACT IS FALSE: both hosts return 5.
//@ fixed-by: OPEN: committed RED, with by_value_held_mut_written_by_callee_unseen.rs. The call lane
//@ fixed-by: must treat a by-value argument that carries a `&mut` at any depth as handing the
//@ fixed-by: pointee to the callee, as a top-level `&mut` argument and one a tuple holds directly are.
//@ teeth: LIVE at the head D-181 was reviewed at: ACCEPTED, exit 0, all four functions `verified`, and each
//@ teeth: spelling alone the same. ACCEPTED, exit 0, at the campaign tip the branch that carries
//@ teeth: D-179 and D-181 merged too, as by_value_held_mut_written_by_callee_unseen.rs is.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    pub r: &'a mut i32,
}

#[ensures(true)]
pub fn destructured((w, _q): (W<'_>, i32)) {
    *w.r = 5i32;
}

#[ensures(true)]
pub fn plain(t: (W<'_>, i32)) {
    *t.0.r = 5i32;
}

#[ensures(result == 0i32)]
pub fn destructured_host() -> i32 {
    let mut a = 0i32;
    destructured((W { r: &mut a }, 0i32));
    a
}

#[ensures(result == 0i32)]
pub fn plain_host() -> i32 {
    let mut a = 0i32;
    plain((W { r: &mut a }, 0i32));
    a
}
