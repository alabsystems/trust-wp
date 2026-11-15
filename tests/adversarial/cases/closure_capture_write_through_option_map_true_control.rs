//@ expect: verify
//@ xfail: D-118's price. The host states what the closure may write, but no lane gives `c` a value
//@ xfail: after a library call runs a closure that writes it, so the host is refused whatever it
//@ xfail: claims. Creusot proves it through `Option::map`'s postcondition, which states the closure's.
//@ mechanism: the TRUE twin of closure_capture_write_through_combinators_unseen's `via_map`: the
//@ mechanism: same host, claiming only what holds after the closure may have run.
//@ accept-means: n/a (control) — `c` is 0 or 5.
//@ fixed-by: n/a (control)
//@ teeth: control — the write is refused after D-118, the price of refusing it rather than modelling
//@ teeth: it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 0 || result@ == 5)]
pub fn via_map(o: Option<u32>) -> u32 {
    let mut c = 0u32;
    let _ = o.map(|_| c = 5);
    c
}
