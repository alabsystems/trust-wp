//@ expect: verify
//@ xfail: the body's cast is a bit-vector truncation and the contract's is Euclidean `mod`;
//@ xfail: ay does not relate the two here and the run ends `unknown (timeout)`. While the
//@ xfail: parser read the contract's cast as its operand this TRUE claim was FAILED instead.
//@ mechanism: control: a contract cast and the body cast it describes denote one value
//@ fixed-by: n/a (control; open)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == x as u8)]
pub fn h(x: u64) -> u8 {
    x as u8
}
