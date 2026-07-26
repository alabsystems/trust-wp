// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED pin (creusot tests/should_fail/recursive_types/impl_arg.rs): logic
//! recursion through an `impl Trait` argument. `Q` is a bound of `Q::f`
//! (via `x: impl Q`), so `f`'s definition can dispatch back into itself —
//! `#[ensures(false)]` would be admitted from a non-terminating definition.
//! Must be rejected as an illegal recursive trait.

use trust_wp::{ensures, logic};

pub trait Q {
    #[logic]
    #[ensures(false)]
    fn f(self, x: impl Q);
}

impl Q for i32 {
    #[logic]
    #[ensures(false)]
    fn f(self, x: impl Q) {
        x.f(x)
    }
}

#[logic]
#[ensures(false)]
pub fn g() {
    0i32.f(0i32)
}

fn main() {}
