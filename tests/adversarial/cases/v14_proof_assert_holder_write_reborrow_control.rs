//@ expect: verify
//@ mechanism: the reborrow control of v14_proof_assert_holder_write_controls: a store through a
//@ mechanism: reborrow `r = &mut *x` is read at `*x` at its new value.
//@ xfail: D-185 refuses an assertion reading memory a write it does not record as the memory's
//@ xfail: current value may have changed; a store through an alias of `x` is one (the governed
//@ xfail: write-back retires the `*x` record and the reborrow's edge, so no `*x` value is left),
//@ xfail: and the assertion is refused as a stale read. Measured: on 67fd4ea7 it verified; the
//@ xfail: refusal's twin store_through_reborrow (proof_assert_mut_param_pointee_store_reads_entry_requires)
//@ xfail: is the false claim a recorded-value reading of this shape VERIFIED when tried.
//@ xfail-verdict: unknown
//@ fixed-by: n/a (over-refusal guard, priced by D-185)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn reborrow_write(x: &mut i32) {
    let r = &mut *x;
    *r = 5i32;
    proof_assert!(*x == 5i32);
}
