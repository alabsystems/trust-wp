//@ expect: verify
//@ xfail: FAILED on a TRUE program, the over-refusal side of user_enum_named_option_read_with_std_variant_numbering.rs: the same body claims `result == 0`, which holds under the precondition, and a model refutes it because the precondition's tester and the body's switch read the user's `m::Option::Some` at two different discriminants. Open.
//@ xfail-verdict: failed
//@ mechanism: control for user_enum_named_option_read_with_std_variant_numbering.rs: the true claim on the same body.
//@ accept-means: n/a (control) — under the precondition `prog` returns `0` on every execution.
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
#[ensures(result == 0u32)]
pub fn prog(o: m::Option<u32>) -> u32 {
    match o {
        m::Option::Some(_) => 0,
        m::Option::None => 1,
    }
}
