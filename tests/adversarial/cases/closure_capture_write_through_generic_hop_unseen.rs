//@ expect: reject
//@ mechanism: a closure that writes a host local through a `&mut` it captured, handed to a VERIFIED
//@ mechanism: local hop: by value (`apply` requires `f.precondition(())` and calls `f`), by `&mut`
//@ mechanism: (`apply_mut(&mut g)`), as a `move` closure over a `&mut` bound beforehand, inside a
//@ mechanism: `Box`, and coerced to `&mut dyn FnMut()` (`apply_dyn`). The hop owes the closure's
//@ mechanism: precondition, but its contract cannot name the host local the closure borrows, and the
//@ mechanism: host's call lane gives a post-call value only to a top-level `&mut` argument, never to
//@ mechanism: the local behind a closure argument's capture: the host read `c` at its value before
//@ mechanism: the call. The trait object erases the closure type, so no walk of the call that
//@ mechanism: receives it can see the capture at all.
//@ accept-means: a host is reported `verified` although the hop runs the closure, which sets `c` to
//@ accept-means: 5 before the host returns `c`.
//@ WHY THE CONTRACT IS FALSE: every hop calls its closure once, which sets `c` to 5.
//@ fixed-by: D-118: a closure that writes through a captured `&mut` refuses its host wherever it goes
//@ fixed-by: other than a direct call: into a verified callee, and through a coercion to a trait
//@ fixed-by: object, as into code trust-wp does not verify.
//@ teeth: ACCEPTED, exit 0, every host `verified`, on the binary before D-118; `host`, `via_mut_ref`,
//@ teeth: `via_moved_mut_ref` and `via_dyn` still ACCEPTED on the one that refused the hand-off into
//@ teeth: unverified code only (`via_box` was refused there by reading `Box::new` as running its
//@ teeth: argument). After D-118 each host's credit is withdrawn.
//@ also-verified: anchor, apply, apply_mut, apply_dyn
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

#[requires(f.precondition(()))]
pub fn apply<F: FnOnce()>(f: F) {
    f()
}

#[requires(f.precondition(()))]
pub fn apply_mut<F: FnMut()>(f: &mut F) {
    f()
}

#[requires(f.precondition(()))]
pub fn apply_dyn(f: &mut dyn FnMut()) {
    f()
}

// FALSE: `host()` returns 5.
#[ensures(result@ == 0)]
pub fn host() -> u32 {
    let mut c = 0u32;
    apply(|| c = 5);
    c
}

#[ensures(result@ == 0)]
pub fn via_mut_ref() -> u32 {
    let mut c = 0u32;
    let mut g = || c = 5;
    apply_mut(&mut g);
    c
}

#[ensures(result@ == 0)]
pub fn via_moved_mut_ref() -> u32 {
    let mut c = 0u32;
    let r = &mut c;
    apply(move || *r = 5);
    c
}

#[ensures(result@ == 0)]
pub fn via_box() -> u32 {
    let mut c = 0u32;
    apply(Box::new(|| c = 5));
    c
}

#[ensures(result@ == 0)]
pub fn via_dyn() -> u32 {
    let mut c = 0u32;
    apply_dyn(&mut || c = 5);
    c
}
