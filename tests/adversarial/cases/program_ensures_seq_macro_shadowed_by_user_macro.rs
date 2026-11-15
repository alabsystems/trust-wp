//@ expect: reject
//@ verdict: error
//@ refused-with: a macro `seq!` defined by the crate
//@ mechanism: the clause spelling of logic_fn_body_seq_macro_shadowed_by_user_macro.rs: the crate's own `macro_rules! seq` shadows the prelude's, and a program function's `ensures` writes `seq![5].len() == 1`. The contract parser reads the literal, and the vehicle writes its own sequence helper, so the specification refusal (`misread_specification_calls`) never meets the crate's macro. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a program function is credited on a postcondition about a sequence literal its clause does not build, and the crate exits 0.
//@ WHY IT IS FALSE: `seq![5]` expands to `Seq::<Int>::empty()`, whose length is `0`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog verified ✓`. The control is program_ensures_seq_macro_shadowed_by_user_macro_control.rs, which differs in the crate's macro alone and verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! seq {
    ($($x:expr),*) => {
        Seq::<Int>::empty()
    };
}

#[ensures(seq![5].len() == 1)]
pub fn prog() {}
