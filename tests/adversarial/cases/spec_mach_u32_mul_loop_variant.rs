//@ expect: reject
//@ mechanism: a loop `#[variant(x * 2u32)]` under `#[check(terminates)]` -- an arithmetic operator
//@ mechanism: on machine-integer operands in spec text. D-135 item 3: in the pinned oracle it means
//@ mechanism: creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u32 + u32`
//@ mechanism: is `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: x = 2^31: the variant's wrapping product is 0, and after `x -= 1` it
//@ WHY THE CONTRACT IS FALSE: is 2^32 - 2, an increase.
//@ teeth: rejected `unknown` when written (a fail-closed `false` in the loop's call obligations),
//@ teeth: so the case pins the shape and its teeth are UNVERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[check(terminates)]
#[requires(true)]
pub fn mul_loop_variant(mut x: u32) {
    #[variant(x * 2u32)]
    while x > 0 {
        x -= 1;
    }
}
