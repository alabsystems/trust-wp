//@ expect: reject
//@ mechanism: the `proof_assert!` and import spelling of
//@ mechanism: raw_ptr_clause_cast_to_str_shadowed_by_block_alias.rs: `use core::primitive::u8 as str;`
//@ mechanism: in the function's block makes `str` name `u8` there, and the classifier, reading the
//@ mechanism: written text, took `p1 as *const str` for a fat-to-fat identity. The assertion read
//@ mechanism: `p1 != p2`, which the branch condition proves.
//@ fixed-by: D-146 (narrows D-145): `written_pointee` does not read `str`.
//@ accept-means: a proof assertion comparing the thin casts of two slice pointers is proved from the
//@ accept-means: pointers differing, although the casts drop the lengths.
//@ WHY THE CONTRACT IS FALSE: `pa_thin_differs(slice_from_raw_parts(a, 1), slice_from_raw_parts(a, 2))`
//@ WHY THE CONTRACT IS FALSE: enters the branch, and both casts are `a`.
//@ teeth: ACCEPTED (`proof_assert in creusot_test::pa_thin_differs verified`) while
//@ teeth: `written_pointee` read `str`; refused after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn pa_thin_differs(p1: *const [u8], p2: *const [u8]) {
    #[allow(unused_imports)]
    use core::primitive::u8 as str;

    if p1 != p2 {
        proof_assert!((p1 as *const str) != (p2 as *const str));
    }
}
