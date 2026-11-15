//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then calls `core::mem::replace(x, 7)` on its `&mut` parameter, and claims `^x == *x`. When the post-loop final values (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_deref_final_values`) hold no entry for a `&mut` parameter its postcondition names, the annotated-loop lane (`callbacks::loop_verify::single_loop`) mints the identity `^x == *x` (the pointee at entry), guarded only by writes INSIDE and BEFORE the loop; a post-loop write the final-value walk does not record is erased by it. The walk reads statements only, so a call that writes through the parameter leaves no entry.
//@ fixed-by: OPEN — committed RED rather than hidden; closes with mut_param_final_identity_after_loop_branch_write.rs.
//@ accept-means: a function that stores `7` through its `&mut` parameter is credited with leaving the pointee unchanged; the crate exits 0.
//@ WHY IT IS FALSE: `prog(&mut v, 0)` with `v == 0` leaves `v == 7`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: prog verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn prog(x: &mut u32, n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let _old = core::mem::replace(x, 7);
}
