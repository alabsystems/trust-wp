// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A shared reference to a `dyn Fn` passed to an extern-spec call (`Fn::call`)
//! has an operand type carrying borrowck inference regions (`&'?N Box<dyn Fn>`).
//! Asking the `Freeze` query with that key panicked the driver
//! ("region variables should not be hashed"). The call divides by `x`, which
//! may be 0, so `bd` must be REJECTED by the verifier, not by a crash.

#![allow(unexpected_cfgs)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn bd(x: u8) -> u8 {
    let f: Box<dyn Fn(u8) -> u8> = Box::new(|y: u8| 10 / y);
    f(x)
}

fn main() {
    let _ = bd(1);
}
