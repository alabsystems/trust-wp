//@ expect: reject
//@ verdict: error
//@ refused-with: a name `B` in a specification, while an import of `E::A` as `B` binds it
//@ mechanism: `use E::A as B;` then the unit variant `B` as a VALUE in a program function's `ensures`: `result == B`. rustc resolves the path to `E::A`; the contract parser and the encoder read the bare `B` as the variant of that name, `E::B`. D-136's specification refusal reads calls only (`misread_specification_calls`), so a renamed path that is not called is read by its spelling. The pattern spelling is program_ensures_variant_pattern_renamed.rs, the logic-body spelling logic_fn_body_unit_variant_value_renamed.rs. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a program function is credited on a postcondition naming a renamed unit variant read as the variant its spelling names, and the crate exits 0.
//@ WHY IT IS FALSE: `prog()` returns `E::B`, and `B` is `E::A`, so `result == B` is false.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog verified ✓`. The control is program_ensures_unit_variant_value_renamed_control.rs, which differs in the `use` alone (`use E::B;`) and verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(PartialEq, Eq)]
pub enum E {
    A,
    B,
}

use E::A as B;

#[ensures(result == B)]
pub fn prog() -> E {
    E::B
}
