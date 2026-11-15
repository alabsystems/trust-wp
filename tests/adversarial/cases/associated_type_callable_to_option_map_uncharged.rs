//@ expect: reject
//@ mechanism: a generic host hands `Option::map` a value of an ASSOCIATED type the trait bounds by
//@ mechanism: `Fn` (`type F: Fn(usize) -> u32`). The bound is an item bound of the associated type,
//@ mechanism: not a where-clause of the host, so a scan that reads only the host's caller bounds sees a
//@ mechanism: plain type and records no hand-off. Creusot refutes the host on `Option::map`'s
//@ mechanism: `f.precondition((t,))`, which nothing states for `T::F`.
//@ accept-means: `host` is reported `verified` although an impl whose `F` is a fn pointer to an
//@ accept-means: indexing function makes `host(f, Some(9))` panic inside the call `Option::map` makes.
//@ fixed-by: D-118: an opaque or associated type is callable when its item bounds say so.
//@ teeth: ACCEPTED, exit 0, `host verified`, on the binary before D-118. After it the hand-off is
//@ teeth: unresolved and `host`'s credit is withdrawn. associated_type_value_through_option_map_control
//@ teeth: is the twin whose associated type is not callable, and verifies before and after.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

pub trait Tr {
    type F: Fn(usize) -> u32;
}

// FALSE as a verified program function: `T::F`'s precondition is unknown here.
#[ensures(result@ == 1)]
pub fn host<T: Tr>(f: T::F, o: Option<usize>) -> u32 {
    let _ = o.map(f);
    1
}
