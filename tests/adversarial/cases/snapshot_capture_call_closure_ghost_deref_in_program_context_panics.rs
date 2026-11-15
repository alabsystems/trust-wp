//@ expect: reject
//@ verdict: error
//@ refused-with: cannot dereference a ghost value in program context
//@ mechanism: the program-context validator walks the arguments of a `Snapshot::capture` call at a
//@ mechanism: raised snapshot-capture depth, where a ghost deref is not refused, because the
//@ mechanism: `snapshot!` macro's own capture never runs (it sits under `cfg(trust_wp)`, and behind
//@ mechanism: `if false` in a normal build). The recogniser is the call's path, so a
//@ mechanism: `Snapshot::capture(..)` written by hand in program code is trusted the same way, and its
//@ mechanism: argument runs in every build. D-133 item 7 extends the trust to a closure written inside
//@ mechanism: those arguments (`closure_is_inside_snapshot_capture`, the same recognisers): its body
//@ mechanism: is no longer validated at depth zero as a body owner of its own. Here the closure is
//@ mechanism: called on the spot, so `*g` runs `<Ghost<i32> as Deref>::deref`, which panics, while the
//@ mechanism: verifier reads it as the ghost's value.
//@ accept-means: a program body that dereferences a ghost at run time, through a closure called inside
//@ accept-means: a hand-written `Snapshot::capture` argument, is reported verified and exits 0.
//@ fixed-by: D-139 item 7 and D-193: the closure search and the argument walk trust only a capture
//@ fixed-by: trust-wp's `snapshot!` expansion wrote (`ghost::program_context`), so the closure and the
//@ fixed-by: argument here are validated as program code.
//@ WHY THE CONTRACT IS FALSE: `f` panics on every call ("Ghost deref called at runtime").
//@ teeth: refused at the campaign base 4c832882 ("cannot dereference a ghost value in program
//@ teeth: context", the closure visited at depth zero); ACCEPTED (`f verified`, exit 0) at wp-s140
//@ teeth: 598eed1d, when committed; refused as at the base under the `from_expansion` guard, while
//@ teeth: snapshot_closure_reading_snapshot_control verifies with and without it. Natively, `f` built
//@ teeth: against trust-wp-std panics at `*g`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 7i32)]
pub fn f() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let _s = Snapshot::capture(&(|| *g)());
    7
}
