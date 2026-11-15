//@ expect: reject
//@ mechanism: call through Box<dyn Fn> owes an opaque precondition
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: calling a boxed closure that divides by its argument verified for x = 0.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn bd(x: u8) -> u8 {
    let f: Box<dyn Fn(u8) -> u8> = Box::new(|y: u8| 10 / y);
    f(x)
}
