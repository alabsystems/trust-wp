//@ expect: reject
//@ mechanism: a program function reborrows its `&mut` parameter before an annotated loop, stores `5` through the reborrow after it, and claims `^x == *x`. When the post-loop final values (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_deref_final_values`) hold no entry for a `&mut` parameter its postcondition names, the annotated-loop lane (`callbacks::loop_verify::single_loop`) mints the identity `^x == *x` (the pointee at entry), guarded only by writes INSIDE and BEFORE the loop; a post-loop write the final-value walk does not record is erased by it. The walk files the store under the reborrow's own name, never the parameter's, because it follows reborrows made after the loop only.
//@ fixed-by: OPEN — committed RED rather than hidden; closes with mut_param_final_identity_after_loop_branch_write.rs.
//@ accept-means: a function that stores `5` through its `&mut` parameter is credited with leaving the pointee unchanged; the crate exits 0.
//@ WHY IT IS FALSE: `prog(&mut v, 0)` with `v == 0` leaves `v == 5`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: prog verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn prog(x: &mut u32, n: u32) {
    let r = &mut *x;
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    *r = 5;
}
