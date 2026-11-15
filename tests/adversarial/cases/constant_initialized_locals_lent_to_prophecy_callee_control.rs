//@ expect: verify
//@ xfail: the caller lends `&mut` borrows of locals that hold constants to a callee whose `ensures`
//@ xfail: names their final values, so the call's credit is stated over `^` of each constant
//@ xfail: (`^Int(3)`), and the final-collapse guard's constant-carrier arm refuses it (D-14's Fix A):
//@ xfail: `error: unsupported formula: final-collapse refused (fail-closed): ^Int(3) applies a prophecy
//@ xfail: to a constant carrier`. The caller is a verification target because it owes the callee's
//@ xfail: precondition (D-71). Retire this directive when a borrow of a constant-initialized local
//@ xfail: gets a prophecy carrier at a call whose ensures reads its final value.
//@ mechanism: control — the caller half of the rusthorn `inc_max_3` program; the callee's own
//@ mechanism: verdict is pinned by the driver's nested_transfer_soundness test.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(^mma == *mmb && ^mmb == *mma)]
fn swap<'a, 'b>(mma: &'a mut &'b mut u32, mmb: &'a mut &'b mut u32) {
    std::mem::swap(mma, mmb);
}

#[requires(*ma <= 1_000_000u32 && *mb <= 1_000_000u32 && *mc <= 1_000_000u32)]
#[ensures(^ma != ^mb && ^mb != ^mc && ^mc != ^ma)]
pub fn inc_max_3<'a>(mut ma: &'a mut u32, mut mb: &'a mut u32, mut mc: &'a mut u32) {
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    if *mb < *mc {
        swap(&mut mb, &mut mc);
    }
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    *ma += 2;
    *mb += 1;
}

pub fn caller() {
    let (mut a, mut b, mut c) = (3u32, 2u32, 1u32);
    inc_max_3(&mut a, &mut b, &mut c);
}
