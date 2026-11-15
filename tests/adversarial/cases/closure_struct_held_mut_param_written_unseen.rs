//@ expect: reject
//@ also-verified: one_param::{closure#2}, two_params::{closure#2}
//@ mechanism: the closure spellings of by_value_held_mut_written_by_callee_unseen.rs: a closure with
//@ mechanism: its own contract takes, by value, a struct that holds a `&mut`, and writes through it.
//@ mechanism: A `Fn*` call on a local closure is held to the local-callee rule (D-103), and a
//@ mechanism: closure parameter that reaches a `&mut` binds no parameter at the call (D-180), but
//@ mechanism: neither gives the pointee a post-call value when the `&mut` is below a struct field,
//@ mechanism: so the host reads `a` after the call at its value before it, for a closure of one
//@ mechanism: parameter and for one of two alike. Found probing sideways from D-180.
//@ accept-means: a host is reported `verified` although the closure it calls sets `a` to 5 through the
//@ accept-means: borrow it was handed inside a struct.
//@ WHY THE CONTRACT IS FALSE: both hosts return 5.
//@ fixed-by: OPEN: committed RED, with by_value_held_mut_written_by_callee_unseen.rs. The call lane
//@ fixed-by: must treat a by-value argument that carries a `&mut` at any depth as handing the
//@ fixed-by: pointee to the callee.
//@ teeth: LIVE at the head D-181 was reviewed at: ACCEPTED, exit 0, both hosts and both closures
//@ teeth: `verified`, and each host alone the same. ACCEPTED, exit 0, at the campaign tip the branch
//@ teeth: that carries D-180 merged too.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    pub r: &'a mut i32,
}

#[ensures(result == 0i32)]
pub fn one_param() -> i32 {
    let mut a = 0i32;
    let f = #[ensures(true)]
    |w: W<'_>| {
        *w.r = 5i32;
    };
    f(W { r: &mut a });
    a
}

#[ensures(result == 0i32)]
pub fn two_params() -> i32 {
    let mut a = 0i32;
    let f = #[ensures(true)]
    |w: W<'_>, k: i32| {
        *w.r = k;
    };
    f(W { r: &mut a }, 5i32);
    a
}
