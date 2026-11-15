//@ expect: verify
//@ xfail: the loop-written pointee is not attributed either — the TRUE claim on the body of
//@ xfail: annotated_loop_param_write_prophecy_lost is unknown while the FALSE identity claim
//@ xfail: on the same body verifies. It records that the grant is unconditional rather than
//@ xfail: a wrong attribution; retire it when the loop lane owes what it grants.
//@ mechanism: The TRUE claim on annotated_loop_param_write_prophecy_lost's body. It pins the
//@ mechanism: direction: the identity premise is minted, not the written value.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 9i32)]
pub fn f(r: &mut i32) {
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        *r = 9;
        i += 1;
    }
}
