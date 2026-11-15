//@ expect: reject
//@ mechanism: snapshot-capture ignore — a named &mut captured by snapshot!(t) is written through AFTER the capture; the capture is not its sole consumer, so the borrow must still make b1 non-final
//@ accept-means: whole-borrow equality b1 == bor credited for a reborrow Creusot classifies non-final (borrow_mut, fresh id)
//@ note: the pre-hardening matcher only walked the capture's own block and never checked other uses of the chain locals
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn snapshot_named_escape(bor: &mut i32) {
    let b1 = &mut *bor;
    let t = &mut *bor;
    let _s = snapshot!(t);
    *t = 1;
    proof_assert!(b1 == bor);
}
