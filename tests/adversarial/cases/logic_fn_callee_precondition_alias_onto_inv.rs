//@ expect: reject
//@ mechanism: `use crate::needs_pos_b as inv;` then `inv(y)` in a logic body. The type-check vehicle writes every one-argument `inv(..)` as its own helper (`spec_tc::encode`), so rustc never resolves the renamed call, and the resolution record holds a call of `__spec_tc::inv`, which owes nothing. Creusot's Pearlite leaves `inv(..)` to rustc, which resolves it to `needs_pos_b`. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition, through a rename onto the spelling `inv`, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos_b(0)`, and `needs_pos_b` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_callee_precondition_alias_onto_inv_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos_b(x: Int) -> bool {
    x > 5
}

use crate::needs_pos_b as inv;

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> bool {
    inv(y)
}
