//@ expect: reject
//@ mechanism: the crate root declares `type Int = u8;`, which shadows the prelude's glob-imported
//@ mechanism: `Int`, so Rust's `forall<x: Int> x@ < 256` ranges over `u8` and holds. The contract
//@ mechanism: parser maps a binder written `Int` to the unbounded integer sort by its SPELLING
//@ mechanism: (`quantifiers::type_annotation_sort`), where the quantifier is false; `f`, which returns
//@ mechanism: false, is credited against `result == true`.
//@ fixed-by: D-202 — REFUSED: a spelled type name the crate declares or imports with another
//@ fixed-by: meaning anywhere is refused wherever a clause spells it in a type position or as a
//@ fixed-by: path's head (`spelled_types`, `callbacks::spelled_type_names`).
//@ accept-means: `f` claims `result == (forall<x: u8> x@ < 256)`, which is true, returns false, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-199 in force.
//@ teeth: With D-202: REFUSED (`unknown`): `f`'s ensures fails to parse (`Int`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[allow(dead_code)]
type Int = u8;

#[ensures(result == (forall<x: Int> x@ < 256))]
pub fn f() -> bool {
    false
}
