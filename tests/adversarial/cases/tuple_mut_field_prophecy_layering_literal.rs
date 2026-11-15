//@ expect: reject
//@ mechanism: The same tuple-of-`&mut` mis-layering, reached WITHOUT a reflexive clause. The
//@ mechanism: precondition constrains the CURRENT value of `p.0` at entry; because `^p.0` and
//@ mechanism: `*p.0` share a layer for a by-value tuple carrier, that entry constraint is granted
//@ mechanism: as a fact about the FINAL value, and the postcondition is discharged from it. The
//@ mechanism: leak is field-local: moving the precondition to `*p.1` while the postcondition
//@ mechanism: still names `^p.0` stops the accept, which is what identifies the carried term.
//@ fixed-by: ?
//@ accept-means: a precondition about a borrow's value on entry is being spent as a postcondition
//@ accept-means: about its value at expiry. This is the sharper half of the tuple layering defect:
//@ accept-means: no reflexivity, no identical subterms, just the wrong layer supplying the fact.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; let mut w = 0;
//@ m((&mut v, &mut w)); the precondition holds on entry, and afterwards v == 9, so the final
//@ value of the first borrow is 9 and not 0.
//@ teeth: SELF-EVIDENT, committed RED: ACCEPTED today on a fresh build of the tip and on the
//@ teeth: separately built campaign tree binary. Three discriminating runs show the accept is the
//@ teeth: layering and not a poisoned premise set: `#[ensures(false)]` under this very
//@ teeth: precondition is still REFUTED, so the premises are consistent; the same postcondition
//@ teeth: with the precondition deleted is REFUTED; and the same postcondition with the
//@ teeth: precondition moved to `*p.1` is REFUTED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*p.0 == 0)]
#[ensures(^p.0 == 0)]
pub fn m<'a>(p: (&'a mut i32, &'a mut i32)) {
    *p.0 = 9;
}

// The refutation, in executable Rust.
pub fn caller() {
    let mut v = 0i32;
    let mut w = 0i32;
    m((&mut v, &mut w));
    assert!(v == 9);
}
