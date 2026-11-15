//@ expect: reject
//@ mechanism: a whole-local move of a `&mut` whose binding carries an explicit TYPE ANNOTATION (`let r: &mut i32 = &mut x; let r2 = r;`). The annotation lowers the borrow through a dying temporary — `_4 = &mut _1; _3 = &mut *_4; StorageDead(_4)` — and the StorageDead handler's `retain(origin != local)` severs the borrow chain at that temporary, so the move edge that would carry the write back to `x` is already gone. The unannotated spelling of the same program rejects; the annotation alone decides it.
//@ fixed-by: 7bb3a696 — the resolver never consults the edge map, so the StorageDead of the annotation's coercion temporary cannot sever it.
//@ accept-means: a type annotation on a `&mut` binding silently erases the borrow chain, freezing the pointee at its entry value for every later read — a plain-Rust false accept the unannotated twin of the same program does not have.
//@ WHY THE PROGRAM IS WRONG: `r2` is `r` is `&mut x`; `*r2 = 7` sets `x` to 7, and the assertion claims 5.
//@ teeth: CLOSED. The case now rejects and its control verifies, so both directions of the defect moved together — the signature of a write that reaches its place rather than one that reaches nothing.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let r: &mut i32 = &mut x;
    let r2 = r;
    *r2 = 7;
    proof_assert!(x == 5i32);
}
