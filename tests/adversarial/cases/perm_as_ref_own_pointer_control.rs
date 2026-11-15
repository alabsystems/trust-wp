//@ expect: verify
//@ mechanism: the TRUE twin of perm_as_ref_null_pointer_uncharged.rs: the pointer is the one
//@ mechanism: `Perm::new` returned with the permission, so the permission guards it.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ xfail: `unknown (incomplete)` under D-138. The owed `p == *own.ward()` is an assumption `Perm::new`
//@ xfail: states, but `ghost!(&*own)` wraps the permission in `Ghost::new`, whose result sort differs
//@ xfail: from the tuple getter's that `own` is read at, and ay's soundness gate rejects the model its
//@ xfail: theory search returns. Passing `&own` (no `Ghost::new`) verifies; so does a field (the twin).
//@ teeth: control — `f verified`, exit 0, when committed, with no precondition owed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn f() -> i32 {
    let (p, own) = Perm::new(1i32);
    let r = unsafe { Perm::as_ref(p, ghost!(&*own)) };
    *r
}
