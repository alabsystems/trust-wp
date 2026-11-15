//@ expect: verify
//@ mechanism: the isolating control for closure_capture_write_through_generic_hop_unseen: the same
//@ mechanism: verified hops and the same spellings (by value, by `&mut`, inside a `Box`, coerced to
//@ mechanism: `&mut dyn FnMut`), but every closure only READS `c` through a shared capture. A shared
//@ mechanism: borrow writes nothing, so the host keeps its credit; a rule that refused every closure
//@ mechanism: handed to a verified hop, or every coercion of one to a trait object, fails here.
//@ accept-means: n/a (control) — `c` is never written.
//@ fixed-by: n/a (control)
//@ teeth: control — every host verifies, before and after D-118.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(f.precondition(()))]
pub fn apply<F: FnOnce() -> bool>(f: F) -> bool {
    f()
}

#[requires(f.precondition(()))]
pub fn apply_mut<F: FnMut() -> bool>(f: &mut F) -> bool {
    f()
}

#[requires(f.precondition(()))]
pub fn apply_dyn(f: &mut dyn FnMut() -> bool) -> bool {
    f()
}

#[ensures(result@ == 0)]
pub fn host() -> u32 {
    let c = 0u32;
    let _ = apply(|| c == 0);
    c
}

#[ensures(result@ == 0)]
pub fn via_mut_ref() -> u32 {
    let c = 0u32;
    let mut g = || c == 0;
    let _ = apply_mut(&mut g);
    c
}

#[ensures(result@ == 0)]
pub fn via_box() -> u32 {
    let c = 0u32;
    let _ = apply(Box::new(|| c == 0));
    c
}

#[ensures(result@ == 0)]
pub fn via_dyn() -> u32 {
    let c = 0u32;
    let _ = apply_dyn(&mut || c == 0);
    c
}
