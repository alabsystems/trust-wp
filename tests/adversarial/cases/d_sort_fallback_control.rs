//@ expect: verify
//@ mechanism: sort-fallback premise drop — the over-refusal direction, which is the direction the
//@ mechanism: defect actually moved: the neutralized premise weakened the base and produced a
//@ mechanism: model-validated FALSE counterexample on a TRUE claim (arc_and_rc, ~67% flaky-fail)
//@ fixed-by: 90fdf8f (sortplan)
//@ accept-means: n/a (control). This is THE case with teeth for the sort-fallback mechanism.
//@
//@ Shape requirements, both needed to reach the defect:
//@   * a datatype-view var compared to an INT LITERAL OUTSIDE {0,1} (`5`, `9`) — in-range
//@     literals encode fine against a Bool plan and never reach the placeholder path;
//@   * the same vars pulled into a BOOLEAN context (`Arc::ptr_eq` feeding `proof_assert!(!same)`),
//@     which is what minted the spurious Bool hint that froze the view sort.
//@ Before 90fdf8f, which var the hint landed on was decided by hash-iteration order, so this
//@ shape failed intermittently rather than deterministically.
//@ teeth: UNVERIFIED (honest). Method (ii): the 90fdf8f vetoes disabled in-tree — this control still
//@ teeth: VERIFIED, so the defect did not reproduce on this shape. The historical failure needed a
//@ teeth: spurious Bool hint to land on the view var, which was decided by hash-iteration order of the
//@ teeth: driver ghost maps (~19-67% flaky); two attempts to mint that hint deterministically (a Bool
//@ teeth: peer in `==`, and an `&&` conjunction) made the assertion unprovable for unrelated reasons
//@ teeth: and were reverted. Standing SHAPE gate for the out-of-range-literal view lane.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use ::std::sync::Arc;
use creusot_std::prelude::*;

pub fn arc_out_of_range_view_literals() {
    let a = Arc::new(5i32);
    let b = Arc::new(9i32);
    proof_assert!(*a@ == 5i32);
    proof_assert!(*b@ == 9i32);
    let same = Arc::ptr_eq(&a, &b);
    proof_assert!(!same);
}
