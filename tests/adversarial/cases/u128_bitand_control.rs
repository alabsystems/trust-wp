//@ expect: verify
//@ xfail: the `&` is read at 64 bits (u128_bitand_read_at_64_bits.rs), so the true postcondition is
//@ xfail: not proved at `x == 2^64`.
//@ mechanism: twin of u128_bitand_read_at_64_bits.rs with the true postcondition.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (x@ == 18446744073709551616))]
pub fn and_high(x: u128) -> bool {
    if x == 18446744073709551616 {
        return x & 18446744073709551616 != 0;
    }
    false
}
