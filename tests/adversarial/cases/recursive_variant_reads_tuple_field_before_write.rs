//@ expect: reject
//@ mechanism: the recursive call-site extraction (`extract_recursive_call_args`, which the variant
//@ mechanism: decrease check reads) binds a local only on an assignment to the whole local: a write into
//@ mechanism: one of its fields (`p.0 = n`) is skipped, so a later read of the field sees the value the
//@ mechanism: aggregate was built with. `tuple_field` is checked as `tuple_field(0)`, and `0 < n` proves
//@ mechanism: the variant decreases. Not a float reading: found probing the extractor's assignment walk
//@ mechanism: sideways from recursive_variant_reads_local_before_refused_cast.rs.
//@ accept-means: `tuple_field(1)` calls `tuple_field(1)` forever; an accept claims it terminates.
//@ fixed-by: D-140 — a write into part of a local leaves the local unbound in the recursive call-site
//@ fixed-by: walk, so a read of it at a recursive call is refused.
//@ teeth: ACCEPTED when committed (`tuple_field verified (termination)`), and on the campaign tip before
//@ teeth: D-140 reached it; FAILED (variant decrease) once the write leaves the local unbound.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n@)]
pub fn tuple_field(n: u32) {
    if n == 0 {
        return;
    }
    let mut p = (0u32, 0u32);
    p.0 = n;
    tuple_field(p.0);
}
