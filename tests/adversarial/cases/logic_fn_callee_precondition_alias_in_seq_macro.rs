//@ expect: reject
//@ mechanism: the `seq!` spelling of logic_fn_callee_precondition_use_alias: the renamed call sits inside `seq![np(y)]`. The parser keeps the macro as a call of its own name with the elements as arguments, and the type-checked body holds its expansion, so the macro's name is the one call of the parsed body that has no counterpart there by design (`call_resolution::MACRO_CALL_NAMES`); the call inside it must still be matched and owed. The walk (which reads a call's SPELLING, D-120) owed nothing for `np`. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition inside a `seq!` literal, through a renaming import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)` to build the sequence, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_callee_precondition_alias_in_seq_macro_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

use crate::needs_pos as np;

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Seq<Int> {
    seq![np(y)]
}
