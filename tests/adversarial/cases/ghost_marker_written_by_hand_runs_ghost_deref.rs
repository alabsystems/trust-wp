//@ expect: reject
//@ verdict: error
//@ refused-with: cannot create a ghost variable in program context
//@ mechanism: the ghost-block finder treats every `let` carrying `#[doc = "__trust_wp_ghost"]` as a
//@ mechanism: `ghost!` expansion and takes its initializer as ghost code: the program-context
//@ mechanism: validator skips everything inside it, so neither `Ghost::new` nor the deref in its
//@ mechanism: argument is refused. `ghost!` keeps its block under `cfg(trust_wp)` and behind `if false`
//@ mechanism: otherwise, so its own block never runs; the same marker written by hand on an ordinary
//@ mechanism: `let` marks code that runs in every build. Here `*g` runs
//@ mechanism: `<Ghost<i32> as Deref>::deref`, which panics, while the verifier reads it as the
//@ mechanism: ghost's value.
//@ accept-means: a program body that dereferences a ghost at run time, inside a `let` marked as a ghost
//@ accept-means: block by hand, is reported verified and the crate exits 0.
//@ fixed-by: D-193: the marker is honoured only where every copy of it was written by a
//@ fixed-by: `trust-wp-macros` expansion (`has_ghost_marker`), so the `let` is program code and its
//@ fixed-by: `Ghost::new` and deref are refused.
//@ WHY THE CONTRACT IS FALSE: `f` panics on every call ("Ghost deref called at runtime").
//@ teeth: ACCEPTED (`f verified`, exit 0) at the campaign base 6e6bf5f3. Natively, built against
//@ teeth: trust-wp-std, `f` panics at `*g`. Refused at wp-s150; ghost_marker_from_ghost_let_control,
//@ teeth: the same deref in the blocks `ghost!` and `ghost_let!` write, verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 7i32)]
pub fn f() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    #[doc = "__trust_wp_ghost"]
    let _v = Ghost::new({
        let x: i32 = *g;
        x
    });
    7
}
