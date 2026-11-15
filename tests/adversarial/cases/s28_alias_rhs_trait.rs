//@ expect: reject
//@ mechanism: call-site alias vocabulary (`value`/`rhs`/`argN`) must never override a real parameter name.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: rhs alias bound T::m(1,2) to its second argument.
//@ teeth: FAILED on 5f5fa607 (review rev28/c2); regression guard.
//@ also-verified: <S as Tr>::m
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(result == rhs)]
    fn m(rhs: u32, y: u32) -> u32;
}
pub struct S;
impl Tr for S {
    #[ensures(result == rhs)]
    fn m(rhs: u32, y: u32) -> u32 { rhs }
}
// WRONG: T::m(1, 2) == 1.
#[ensures(result == 2u32)]
pub fn through<T: Tr>() -> u32 { T::m(1, 2) }
