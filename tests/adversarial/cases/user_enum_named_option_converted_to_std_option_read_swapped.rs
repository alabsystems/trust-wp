//@ expect: reject
//@ mechanism: the conversion spelling of user_enum_named_option_read_with_std_variant_numbering.rs: a program function maps a user `m::Option` (variants `Some(T)`, `None`) that its precondition says is `Some` to the standard `Option`, arm by arm, and claims the standard result is `None`. The user's value is read with the standard numbering, so the switch takes the `None` arm and the claim is proved.
//@ fixed-by: OPEN — committed RED rather than hidden; closes with user_enum_named_option_read_with_std_variant_numbering.rs.
//@ accept-means: a program function returning a standard `Option` is credited with `None` where it returns `Some`, and the crate exits 0.
//@ WHY IT IS FALSE: under the precondition `o` is `m::Option::Some(x)`, so `prog(o)` returns `Some(x)`.
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
#[ensures(result == None)]
pub fn prog(o: m::Option<u32>) -> Option<u32> {
    match o {
        m::Option::Some(x) => Some(x),
        m::Option::None => None,
    }
}
