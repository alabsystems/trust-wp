//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then stores a call's result `id(y)` through its `&mut` parameter, and claims `^x == *x`. When the post-loop final values (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_deref_final_values`) hold no entry for a `&mut` parameter its postcondition names, the annotated-loop lane (`callbacks::loop_verify::single_loop`) mints the identity `^x == *x` (the pointee at entry), guarded only by writes INSIDE and BEFORE the loop; a post-loop write the final-value walk does not record is erased by it. The walk cannot translate the call's result, so it records nothing for the store, though `extract_post_loop_deref_writes` names the parameter. The same store of `y` itself is not proved (`prog unknown (incomplete)`).
//@ fixed-by: OPEN — committed RED rather than hidden; closes with mut_param_final_identity_after_loop_branch_write.rs.
//@ accept-means: a function that stores `y` through its `&mut` parameter is credited with leaving the pointee unchanged; the crate exits 0.
//@ WHY IT IS FALSE: `prog(&mut v, 0, 1)` with `v == 0` leaves `v == 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: id verified ✓`, `trust-wp: prog verified ✓`.
//@ also-verified: id
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == y)]
pub fn id(y: u32) -> u32 {
    y
}

#[ensures(^x == *x)]
pub fn prog(x: &mut u32, n: u32, y: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    *x = id(y);
}
