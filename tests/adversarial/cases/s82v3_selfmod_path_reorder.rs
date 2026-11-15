//@ expect: reject
//@ verdict: unknown
//@ mechanism: the s82 field-order defect spelled `self::E::C` — a module-relative path rustc
//@ mechanism: resolves and `path_spellings()` never produces, so `tables.ctors` had NO entry
//@ mechanism: and `place_named_fields` fell through to the flat name->index map. The flat map
//@ mechanism: is built from the decoy STRUCT `D` in the signature (`a`->0, `b`->1), so `aa`
//@ mechanism: was placed at index 0 — which in `E::C { b, a }` is the field `b`. An ENUM
//@ mechanism: contributes nothing to that map at all (`build_struct_field_map` returns early
//@ mechanism: on `!adt_def.is_struct()`), so a struct elsewhere in the signature answered for
//@ mechanism: a variant's fields unchallenged.
//@ accept-means: the SPELLING of a resolved path decides where a field is bound: `E::C`
//@ accept-means: places at declaration indices and `self::E::C`, one token longer, places at
//@ accept-means: whatever a neighbouring struct's field names happen to say.
//@ WHY THE CONTRACT IS FALSE: the precondition constrains the field named `a`; the body
//@ WHY THE CONTRACT IS FALSE: returns the field named `b`, which nothing constrains, so
//@ WHY THE CONTRACT IS FALSE: `E::C { b: 0, a: 5 }` returns 0 and `result == 5` is false.
//@ teeth: measured ACCEPTED, exit 0, `g verified ✓` on the s82 v2 fix. Its twin
//@ teeth: `s82v3_selfmod_path_reorder_control` differs only in which field the body returns
//@ teeth: and VERIFIES, so the pair shows declaration-order placement rather than a blanket
//@ teeth: refusal of the spelling. The verdict is pinned to `unknown`: with the constructor
//@ teeth: resolved, this case reaches the solver exactly as the `E::C` spelling does
//@ teeth: (`s82v3_canonical_path_reorder`), and a bare refusal would not be the same evidence.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// `b` is declared FIRST (index 0), `a` SECOND (index 1).
pub enum E { C { b: u32, a: u32 }, N }

// Decoy struct in the signature: the flat map learns `a`->0, `b`->1 from it.
pub struct D { pub a: u32, pub b: u32 }

#[requires(match e { self::E::C { a: aa, b: _bb } => aa@ == 5, self::E::N => false })]
#[ensures(result@ == 5)]
pub fn g(e: E, _d: D) -> u32 { match e { E::C { b, a: _a } => b, E::N => 0 } }
