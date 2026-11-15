//@ expect: reject
//@ mechanism: the post-loop spelling of user_enum_named_option_read_with_std_variant_numbering.rs: the same match on a user enum named `Option` (variants `Some(T)`, `None`) follows an annotated loop, and the post-loop return walk's `ite` over the switch reads it with the standard `Option`'s numbering, so `result == 1` is proved where the body returns `0`.
//@ fixed-by: OPEN — committed RED rather than hidden; closes with user_enum_named_option_read_with_std_variant_numbering.rs.
//@ accept-means: a program function is credited after a loop on a postcondition its body violates whenever a user enum shares the standard `Option`'s name, and the crate exits 0.
//@ WHY IT IS FALSE: under the precondition `o` is `m::Option::Some(_)`, so `prog(n, o)` returns `0`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: prog verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m {
    pub enum Option<T> {
        Some(T),
        None,
    }
}

#[requires(match o { m::Option::Some(_) => true, m::Option::None => false })]
#[ensures(result == 1u32)]
pub fn prog(n: u32, o: m::Option<u32>) -> u32 {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    match o {
        m::Option::Some(_) => 0,
        m::Option::None => 1,
    }
}
