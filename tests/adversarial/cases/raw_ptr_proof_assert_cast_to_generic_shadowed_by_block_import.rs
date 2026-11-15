//@ expect: reject
//@ mechanism: the import spelling of raw_ptr_proof_assert_cast_to_generic_shadowed_by_block_alias.rs:
//@ mechanism: `use core::primitive::u8 as T;` in the owner's block makes `T` name `u8` there, and the
//@ mechanism: classifier, reading the written text, took `p1 as *const T` for the generic parameter
//@ mechanism: and so for the identity.
//@ fixed-by: D-148 (narrows D-145): a written target is read as a generic parameter only while no
//@ fixed-by: item written in the owner's body can name it, so the cast stays a pending marker
//@ fixed-by: and the encoder refuses it.
//@ accept-means: a proof assertion comparing the thin casts of two fat pointers is proved from the
//@ accept-means: pointers differing, although the casts drop the metadata.
//@ WHY THE CONTRACT IS FALSE: at `T = [u8]`, two slice pointers at one address with lengths 1 and 2
//@ WHY THE CONTRACT IS FALSE: enter the branch and both casts are that address.
//@ verdict: unknown
//@ teeth: ACCEPTED (`proof_assert in creusot_test::pa_thin_differs verified`) under D-145 and
//@ teeth: D-146; `unsupported formula: raw pointer cast ... was not classified` after D-148.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn pa_thin_differs<T: ?Sized>(p1: *const T, p2: *const T) {
    #[allow(unused_imports)]
    use core::primitive::u8 as T;
    if p1 != p2 {
        proof_assert!((p1 as *const T) != (p2 as *const T));
    }
}
