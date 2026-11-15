//@ expect: verify
//@ xfail: D-118's price. The host states what the closure may write, but no lane gives `c` a value
//@ xfail: after a verified hop runs a closure that writes it, so the host is refused whatever it
//@ xfail: claims. Creusot proves it through `f.postcondition_once`, which states the closure's
//@ xfail: post-state and so `c`'s.
//@ mechanism: the TRUE twin of closure_capture_write_through_generic_hop_unseen's `host`: the same
//@ mechanism: hop and closure, the host claiming only what holds after the closure may have run.
//@ accept-means: n/a (control) — `c` is 0 or 5.
//@ fixed-by: n/a (control)
//@ teeth: control — verified on the binary before D-118 (on the stale read of `c`), refused after it:
//@ teeth: the price of refusing the write rather than modelling it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(f.precondition(()))]
pub fn apply<F: FnOnce()>(f: F) {
    f()
}

#[ensures(result@ == 0 || result@ == 5)]
pub fn host() -> u32 {
    let mut c = 0u32;
    apply(|| c = 5);
    c
}
