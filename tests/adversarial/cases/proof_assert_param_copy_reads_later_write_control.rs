//@ expect: verify
//@ mechanism: the control for proof_assert_param_copy_reads_later_write.rs: the write to the parameter
//@ mechanism: itself is seen by the assertion lane, the function lane keeps the copy's value, and so does
//@ mechanism: the assertion lane when the copied place is a local rather than a parameter.
//@ accept-means: n/a (control) — every claim here holds in every execution.
//@ fixed-by: n/a (control)
//@ teeth: verified when committed and on the campaign tip before D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn write_seen(mut a: i64) {
    let c = a;
    a = 0;
    proof_assert!(a@ == 0);
    let _ = c;
}

#[ensures(result == a)]
pub fn copy_returned(mut a: i64) -> i64 {
    let c = a;
    a = 0;
    let _ = a;
    c
}

#[ensures(true)]
pub fn local_copy_kept(x: i64) {
    let mut a = x;
    let c = a;
    a = 0;
    proof_assert!(c == x);
    proof_assert!(a@ == 0);
}
