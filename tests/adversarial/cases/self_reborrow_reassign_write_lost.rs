//@ expect: reject
//@ mechanism: a `&mut` local reassigned to a reborrow of ITSELF (`r = &mut *r;`): the assignment drops the edge the local held, and the reborrow of the place being overwritten does not re-record one, so the later write through `r` reaches nothing and the pointee keeps its entry value. Source and destination of the reborrow are the same local, which is exactly what the drop-then-re-record order cannot serve.
//@ fixed-by: ?
//@ accept-means: an identity reborrow through a borrow local erases that local's target, so every later write through it is lost and the pointee is proved frozen at its entry value.
//@ WHY THE PROGRAM IS WRONG: `r` still points at `x` after the self-reborrow; `*r = 7` sets `x` to 7, and the assertion claims 5.
//@ teeth: RED, open. OBSERVED ACCEPTED by this runner on the tip that carries the case, and ACCEPTED by the campaign binary too, so the hole pre-exists this corpus entry. Its control is `xfail`: the true twin does not verify either, which is the signature of a write that reached nothing.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let mut r: &mut i32 = &mut x;
    r = &mut *r;
    *r = 7;
    proof_assert!(x == 5i32);
}
