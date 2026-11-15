//@ expect: reject
//@ also-verified: g
//@ mechanism: cast_target_module_alias_callee_contract_granted.rs through a PRECONDITION. With the crate
//@ mechanism: root's `type u8 = u32;`, `g`'s `requires(x == 300u32 as u8)` is `x == 300`, and `caller`
//@ mechanism: calls `g(44)`, which violates it. The contract parser reads the cast's target by its
//@ mechanism: spelling and lowers it to the low eight bits (44), so the call site owes `44 == 44`:
//@ mechanism: `caller` is credited on a call Rust's reading of the precondition forbids.
//@ fixed-by: D-202 — REFUSED: a spelled type name the crate declares or imports with another
//@ fixed-by: meaning anywhere is refused wherever a clause spells it in a type position or as a
//@ fixed-by: path's head (`spelled_types`, `callbacks::spelled_type_names`).
//@ accept-means: `caller` calls `g` outside its precondition; ACCEPTED means that credit is printed.
//@ teeth: not shown on a build without D-202: a sideways guard of
//@ teeth: cast_target_module_alias_callee_contract_granted.rs.
//@ teeth: With D-202: REFUSED (`unknown`): `g`'s requires fails to parse and `caller` carries a
//@ teeth: fail-closed `false`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[allow(non_camel_case_types)]
type u8 = u32;

#[requires(x == 300u32 as u8)]
pub fn g(x: u32) -> u32 {
    x
}

#[ensures(result == 44u32)]
pub fn caller() -> u32 {
    g(44)
}
