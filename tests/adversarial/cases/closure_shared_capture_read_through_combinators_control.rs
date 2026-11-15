//@ expect: verify
//@ mechanism: the isolating control for closure_capture_write_through_combinators_unseen and
//@ mechanism: option_mut_ref_written_by_mapped_closure_unseen: the same hosts, combinators and local,
//@ mechanism: but every closure only READS `c`, through a shared capture or a shared reference
//@ mechanism: inside the `Option`. A shared borrow writes nothing, so the host keeps its credit; a
//@ mechanism: rule that refused every capture, or every reference beside a callable, fails here.
//@ accept-means: n/a (control) — `c` is never written.
//@ fixed-by: n/a (control)
//@ teeth: control — every host verifies, before and after D-118.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn via_map(o: Option<u32>) -> u32 {
    let c = 0u32;
    let _ = o.map(|x| x == c);
    c
}

#[ensures(result@ == 0)]
pub fn via_unwrap_or_else(o: Option<u32>) -> u32 {
    let c = 0u32;
    let _ = o.unwrap_or_else(|| c);
    c
}

#[ensures(result@ == 0)]
pub fn via_shared_ref_in_option(b: bool) -> u32 {
    let c = 0u32;
    let o = if b { Some(&c) } else { None };
    let _ = o.map(|r| *r == 0);
    c
}
