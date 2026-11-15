//@ expect: verify
//@ mechanism: over-refusal control for contract_free_index_bounds_uncharged — an index the array
//@ mechanism: type itself puts in bounds, in a host that carries a contract, so it is a target by
//@ mechanism: the ordinary route. The clause-free twin of the isolating pair is
//@ mechanism: contract_free_index_bounds_clausefree_control.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — it verifies only while the bounds goal is stated AND discharged
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == result@)]
pub fn hop(v: &[u32; 20]) -> u32 {
    v[10]
}
