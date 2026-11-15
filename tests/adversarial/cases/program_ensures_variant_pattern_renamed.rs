//@ expect: reject
//@ verdict: error
//@ refused-with: a name `B` in a specification, while an import of `E::A` as `B` binds it
//@ mechanism: `use E::A as B;` then the PATTERN `B(_)` in a program function's `ensures`. rustc resolves the pattern's path to the variant `E::A`; the contract parser keeps the pattern as a constructor named `B`, and the encoder tests the scrutinee for the variant of that name, `E::B`. D-136's specification refusal visits calls (`misread_specification_calls` reads `ExprKind::Call`): the same rename CALLED, `B(0u32)`, refuses the crate, while a pattern, and a path used as a value (program_ensures_unit_variant_value_renamed.rs), are read by their spelling. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a program function is credited on a postcondition whose match arm a renamed variant selects, read as the variant its spelling names, and the crate exits 0.
//@ WHY IT IS FALSE: `prog()` returns `E::A(0)`, which the pattern `B(_)` (that is, `E::A(_)`) matches, so the postcondition is `false`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog verified ✓`. The control is program_ensures_variant_pattern_renamed_control.rs, which differs in the `use` alone (`use E::B;`) and verifies: the verdict does not change with what `B` resolves to.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E {
    A(u32),
    B(u32),
}

use E::A as B;

#[ensures(match result { B(_) => false, _ => true })]
pub fn prog() -> E {
    E::A(0)
}
