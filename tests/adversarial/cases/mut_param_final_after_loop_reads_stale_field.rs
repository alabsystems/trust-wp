//@ expect: reject
//@ mechanism: a program function builds a tuple `(0, 0)`, runs an annotated loop, writes its input `z` into the first field, stores that field through its `&mut` parameter and claims `^x == 0`. The post-loop final values of `&mut` parameters (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_deref_final_values`), which give the function-level check `^x` after an annotated loop, start from the expressions locals had BEFORE the loop and change a local only at a projection-free assignment they can translate; a field write is not one, so the tuple keeps `(0, 0)` and `^x` is read as `0` (program_ensures_after_loop_field_write_read_as_stale_field.rs is the `result` spelling D-165 closed).
//@ fixed-by: OPEN — committed RED rather than hidden; closes with mut_param_final_after_loop_reads_stale_call_result.rs.
//@ accept-means: a function that stores `z` through its `&mut` parameter is credited with leaving `0` there, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(&mut v, 0, 1)` leaves `v == 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: prog verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(^x == 0u32)]
pub fn prog(x: &mut u32, n: u32, z: u32) {
    let mut t = (0u32, 0u32);
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    t.0 = z;
    *x = t.0;
}
