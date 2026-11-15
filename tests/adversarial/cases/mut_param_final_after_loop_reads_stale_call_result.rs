//@ expect: reject
//@ mechanism: a program function sets a local `y` to `0`, runs an annotated loop, assigns `y` from a call returning its argument `n`, stores `y` through its `&mut` parameter and claims `^x == 0`. The post-loop final values of `&mut` parameters (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_deref_final_values`), which give the function-level check `^x` after an annotated loop, start from the expressions locals had BEFORE the loop and change a local only at a projection-free assignment they can translate; a call is a terminator they never read, so `y` keeps `0` and `^x` is read as `0`. This is the walk D-165 item 2 replaced for `result` (program_ensures_after_loop_call_result_read_as_stale_local.rs), still in use for `^x`. Found probing sideways from D-165.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means the final-value walk forgets a local wherever the return walk does (a call, a partial write, a loan), or refuses.
//@ accept-means: a function that stores `n` through its `&mut` parameter is credited with leaving `0` there, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(&mut v, 1)` leaves `v == 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: id verified ✓`, `trust-wp: prog verified ✓`.
//@ also-verified: id
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == n)]
pub fn id(n: u32) -> u32 {
    n
}

#[ensures(^x == 0u32)]
pub fn prog(x: &mut u32, n: u32) {
    let mut y = 0u32;
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    y = id(n);
    *x = y;
}
