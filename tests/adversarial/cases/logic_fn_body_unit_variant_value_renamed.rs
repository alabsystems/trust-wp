//@ expect: reject
//@ verdict: error
//@ refused-with: a name `B` in a specification, while an import of `E::A` as `B` binds it
//@ mechanism: `use E::A as B;` then the unit variant `B` as the VALUE of a logic body. rustc resolves the path to `E::A`; the parsed body is the bare name `B`, which the encoder reads as the variant of that name, `E::B`, so the ensures lane proves `result == E::B`. `settle_spelled_calls` reads the body's calls against the type-checked closure, and a path that is not called is none of them (`CallCollector::record` records calls, method calls, struct literals and overloaded operators). The clause spelling is program_ensures_unit_variant_value_renamed.rs. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a logic function whose body is a renamed unit variant is credited with the variant its spelling names, and the crate exits 0.
//@ WHY IT IS FALSE: `caller()` is `E::A`, and `E::A == E::B` is false.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: creusot_test::caller verified ✓`. The control is logic_fn_body_unit_variant_value_renamed_control.rs, which differs in the `use` alone (`use E::B;`) and verifies.
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

#[logic]
#[ensures(result == E::B)]
pub fn caller() -> E {
    B
}
