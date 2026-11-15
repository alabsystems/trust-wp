//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then stores `5` through its `&mut` parameter under a branch, and claims `^x == *x`. When the post-loop final values (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_deref_final_values`) hold no entry for a `&mut` parameter its postcondition names, the annotated-loop lane (`callbacks::loop_verify::single_loop`) mints the identity `^x == *x` (the pointee at entry), guarded only by writes INSIDE and BEFORE the loop; a post-loop write the final-value walk does not record is erased by it. The final-value walk returns no entry at all once a post-loop block branches, though `extract_post_loop_deref_writes` records this write. The same store without the branch is not proved (`prog unknown (incomplete)`). Sibling of annotated_loop_param_write_prophecy_lost.rs (a write inside the loop) and annotated_loop_prior_write_prophecy_erased.rs (before it). Found probing sideways from D-165.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means the identity is minted only where the walk saw every post-loop path and none writes the parameter.
//@ accept-means: a function that may store `5` through its `&mut` parameter is credited with leaving the pointee unchanged, and callers read that; the crate exits 0.
//@ WHY IT IS FALSE: `prog(&mut v, 0, true)` with `v == 0` leaves `v == 5`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: prog verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn prog(x: &mut u32, n: u32, c: bool) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    if c {
        *x = 5;
    }
}
