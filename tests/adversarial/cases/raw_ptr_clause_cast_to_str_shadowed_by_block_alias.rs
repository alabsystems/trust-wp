//@ expect: reject
//@ mechanism: D-145 reads a clause's raw-pointer cast target from its written text
//@ mechanism: (`written_pointee`), not through rustc's name resolution: `str` was taken as the
//@ mechanism: primitive unless the owner's MODULE declares a type of that name. An item in a block is
//@ mechanism: no module child, so `type str = u8;` in the block around the function left the clause's
//@ mechanism: `p1 as *const str` read as a fat-to-fat identity, while rustc resolves it to
//@ mechanism: `*const u8`, a cast that drops the length. The clause read `p1 != p2` and the
//@ mechanism: precondition proved it. `str` is the one written target this matters for: every
//@ mechanism: other spelling the classifier reads is sized (a shadowing then reads a real identity
//@ mechanism: as `thin`, which proves less) or a slice, which no item can shadow.
//@ fixed-by: D-146 (narrows D-145): `written_pointee` does not read `str`, so a clause cast to
//@ fixed-by: `*const str` stays a pending marker and the encoder refuses it.
//@ accept-means: a metadata-dropping cast written in a clause is read as the identity, and the thin
//@ accept-means: casts of two slice pointers that differ only in length are proved different.
//@ WHY THE CONTRACT IS FALSE: `thin_differs(slice_from_raw_parts(a, 1), slice_from_raw_parts(a, 2))`
//@ WHY THE CONTRACT IS FALSE: meets the precondition, and both casts are `a`.
//@ teeth: ACCEPTED (`outer::thin_differs verified`) under D-145, where `written_pointee` read
//@ teeth: `str`; an `unsupported formula` error after. The twin
//@ teeth: raw_ptr_clause_cast_to_str_control.rs differs in the alias alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn outer() {
    #[allow(non_camel_case_types)]
    type str = u8;

    #[requires(p1 != p2)]
    #[ensures((p1 as *const str) != (p2 as *const str))]
    pub fn thin_differs(p1: *const [u8], p2: *const [u8]) {
        let _ = (p1, p2);
    }

    let _ = thin_differs;
}
