//@ expect: reject
//@ mechanism: the `Result` spelling of user_enum_named_option_read_with_std_variant_numbering.rs: a user enum named `Result` whose variants are declared `Err(E), Ok(T)` is read with the standard `Result`'s numbering (`Ok` first). A program function requires its argument to be `m::Result::Ok`, matches on it and returns `0` for `Ok` and `1` for `Err`, claiming `result == 1`; the precondition's tester and the body's switch read the user's `Ok` at two different discriminants, so the switch takes the `Err` arm.
//@ fixed-by: OPEN — committed RED rather than hidden; closes with user_enum_named_option_read_with_std_variant_numbering.rs.
//@ accept-means: a program function is credited on a postcondition its body violates whenever a user enum shares the standard `Result`'s name, and the crate exits 0.
//@ WHY IT IS FALSE: under the precondition `r` is `m::Result::Ok(_)`, so `prog(r)` returns `0`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: prog verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m {
    pub enum Result<T, E> {
        Err(E),
        Ok(T),
    }
}

#[requires(match r { m::Result::Ok(_) => true, m::Result::Err(_) => false })]
#[ensures(result == 1u32)]
pub fn prog(r: m::Result<u32, u32>) -> u32 {
    match r {
        m::Result::Ok(_) => 0,
        m::Result::Err(_) => 1,
    }
}
