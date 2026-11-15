//@ expect: verify
//@ xfail: with the crate root's `type u8 = u32;`, the `u8` of `as u8` is the alias, and the clause
//@ xfail: is refused (D-202): the parser does not read a type name through Rust's scopes. Before
//@ xfail: D-202 it was read as the primitive `u8` and the contract refuted. The isolating twin
//@ xfail: of cast_target_module_alias_shadows_primitive_granted.rs.
//@ mechanism: control: `f` returns 300, which is `300u32 as u8` with `u8` the alias of `u32`.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` with D-199 in force)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[allow(non_camel_case_types)]
type u8 = u32;

#[ensures(result == 300u32 as u8)]
pub fn f() -> u8 {
    300
}
