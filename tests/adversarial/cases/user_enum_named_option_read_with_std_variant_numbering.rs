//@ expect: reject
//@ mechanism: a user enum named `Option` whose variants are declared in the other order (`m::Option { Some(T), None }`) is read with the standard `Option`'s variant numbering. A program function requires its argument to be `m::Option::Some`, matches on it and returns `0` for `Some` and `1` for `None`, claiming `result == 1`. rustc numbers the user's `Some` as discriminant `0`, and the body's switch reads it so; the precondition's tester reaches the solver tied to discriminant `1`, the standard `Some`, so the switch takes the `None` arm. The same enum named `MyOpt` is refuted, and a user `Option` declared in the standard order (`None`, `Some(T)`) is refuted, so the type's name alone decides the numbering. The true claim `result == 0` on this body is FAILED (user_enum_named_option_true_claim_control.rs). Found probing sideways from D-165's post-loop branch reading; no loop is involved here.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a user enum is read by its own definition, never by a standard type that shares its name.
//@ accept-means: a program function is credited on a postcondition its body violates whenever a user enum shares the standard `Option`'s name, and the crate exits 0.
//@ WHY IT IS FALSE: under the precondition `o` is `m::Option::Some(_)`, so `prog(o)` returns `0`.
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
pub fn prog(o: m::Option<u32>) -> u32 {
    match o {
        m::Option::Some(_) => 0,
        m::Option::None => 1,
    }
}
