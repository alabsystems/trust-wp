//@ expect: reject
//@ verdict: error
//@ refused-with: a macro `seq!` defined by the crate
//@ mechanism: a crate's own `macro_rules! seq` shadows the prelude's `seq!` (a macro in textual scope is found before a glob import), and a logic body writes `seq![5]`. rustc and Creusot expand the crate's macro, here the empty sequence; the contract parser reads any `seq![..]` as the sequence literal, and the type-check vehicle writes its own sequence helper for it, so rustc never says which macro the name denotes. D-136 refuses a CALL spelled `seq` beside the macro, and otherwise takes every parsed call named `seq` to be the prelude's macro (`settle_typed_body`, `MACRO_CALL_NAMES`): a macro of that name defined by the crate is not seen. The clause spelling is program_ensures_seq_macro_shadowed_by_user_macro.rs, the `pearlite!` spelling logic_fn_body_pearlite_macro_shadowed_by_user_macro.rs. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a logic function is credited with the length of a sequence literal its body does not build, and the crate exits 0.
//@ WHY IT IS FALSE: `seq![5]` expands to `Seq::<Int>::empty()`, whose length is `0`, so `caller()` is `0`, not `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: creusot_test::caller verified ✓`. The control is logic_fn_body_seq_macro_shadowed_by_user_macro_control.rs, which differs in the crate's macro alone and verifies.
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

#[logic]
#[ensures(result == 1)]
pub fn caller() -> Int {
    seq![5].len()
}
