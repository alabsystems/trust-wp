//@ expect: verify
//@ mechanism: control for the MIR `Unreachable` exclusion — an exhaustive enum match lowers its
//@ mechanism: otherwise arm to a bare `Unreachable` terminator, which is the dead edge rustc's own
//@ mechanism: exhaustiveness check proved, not a site trust-wp has anything to state. Creusot emits
//@ mechanism: an `Abort` goal there; discharging it from the Rust type system is the parity claim,
//@ mechanism: and this case is what breaks if that edge is ever turned into a stated obligation or
//@ mechanism: into a discovery trigger.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub enum E {
    A,
    B,
}

#[ensures(result@ == 1u32@ || result@ == 2u32@)]
pub fn f(e: E) -> u32 {
    match e {
        E::A => 1,
        E::B => 2,
    }
}
