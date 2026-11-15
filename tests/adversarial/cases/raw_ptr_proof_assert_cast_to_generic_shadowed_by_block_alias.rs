//@ expect: reject
//@ mechanism: D-145 reads a clause's raw-pointer cast target from its written text: a name that
//@ mechanism: spells a generic parameter of the owner is taken as that parameter
//@ mechanism: (`written_pointee` -> `generic_type_param`) before anything else is asked. An item in
//@ mechanism: the owner's body block shadows the parameter there: after `type T = u8;`, rustc
//@ mechanism: resolves the assertion's `p1 as *const T` to `*const u8`, a cast that drops the
//@ mechanism: metadata of a pointer to the `?Sized` parameter. The classifier read it as the
//@ mechanism: identity (same pointee), and the branch condition `p1 != p2` proved the assertion.
//@ mechanism: The `str` spelling of this shadowing is closed by not reading `str`; a generic
//@ mechanism: parameter is lang/cast_ptr.rs's target and cannot be dropped the same way.
//@ fixed-by: D-148 (narrows D-145): a written target is read as a generic parameter only while no
//@ fixed-by: item written in the owner's body can name it, so the cast stays a pending marker
//@ fixed-by: and the encoder refuses it.
//@ accept-means: a proof assertion comparing the thin casts of two fat pointers is proved from the
//@ accept-means: pointers differing, although the casts drop the metadata.
//@ WHY THE CONTRACT IS FALSE: at `T = [u8]`, `pa_thin_differs(slice_from_raw_parts(a, 1),
//@ WHY THE CONTRACT IS FALSE: slice_from_raw_parts(a, 2))` enters the branch and both casts are `a`.
//@ verdict: unknown
//@ teeth: ACCEPTED (`proof_assert in creusot_test::pa_thin_differs verified`) under D-145 and
//@ teeth: D-146; `unsupported formula: raw pointer cast ... was not classified` after D-148. The
//@ teeth: twin raw_ptr_proof_assert_cast_to_generic_control.rs differs in the alias alone, and
//@ teeth: raw_ptr_proof_assert_cast_to_generic_beside_unrelated_block_item_control.rs in its name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn pa_thin_differs<T: ?Sized>(p1: *const T, p2: *const T) {
    #[allow(non_camel_case_types, dead_code)]
    type T = u8;
    if p1 != p2 {
        proof_assert!((p1 as *const T) != (p2 as *const T));
    }
}
