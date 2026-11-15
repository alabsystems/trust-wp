//@ expect: reject
//@ verdict: failed
//@ fn-failed: and_high
//@ mechanism: the encoder takes a bit operation at 64 bits whatever the operand's type
//@ mechanism: (`encode_int_binop_bv`: an Int operand is converted with `int2bv` at
//@ mechanism: `DEFAULT_BV_WIDTH`, 64). At `x == 2^64` a `u128`'s `x & 2^64` reads as `0`, so
//@ mechanism: `result == false` is proved where the function returns `true`. A contracted body is
//@ mechanism: never capped, so this is live independent of D-142.
//@ fixed-by: D-242: a `u128` bit operation is computed at 128 bits (`__trust_wp_int_bitop_u128`).
//@ accept-means: a function whose result contradicts its postcondition is verified, exit 0.
//@ WHY THE CONTRACT IS FALSE: `and_high(1 << 64)` returns `true`.
//@ teeth: ACCEPTED (`and_high verified`), with and without D-149, which only touches clause-free
//@ teeth: bodies. The twin u128_bitand_control.rs states the true postcondition.
//@ teeth: ACCEPTED on trust-wp 7726ea81 (the parent of D-242); `and_high FAILED` with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == false)]
pub fn and_high(x: u128) -> bool {
    if x == 18446744073709551616 {
        return x & 18446744073709551616 != 0;
    }
    false
}
