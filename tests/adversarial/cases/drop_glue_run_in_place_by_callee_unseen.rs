//@ expect: reject
//@ mechanism: drop glue a callee runs IN PLACE, on a value it was lent rather than handed: `v.clear()`
//@ mechanism: and `v.truncate(0)` drop the guard inside `Vec`, through the `&mut Vec<G>` they are handed,
//@ mechanism: and the container is then forgotten so no `Drop` of it follows; the same through the
//@ mechanism: `DerefMut` of a `ManuallyDrop`, which never drops its content, and by `ManuallyDrop::drop`
//@ mechanism: on a `&mut ManuallyDrop<G>`, whose type has no glue at all. A call was a hand-off only
//@ mechanism: for a value it was handed BY MOVE, so `c` kept its value before the borrow. `*r = None`
//@ mechanism: through a `&mut Option<G>` is the `Drop` terminator's spelling of the same in-place drop.
//@ accept-means: a `proof_assert!` is credited although a callee dropped the guard, whose `Drop` impl set
//@ accept-means: the asserted local to 5.
//@ WHY THE CONTRACT IS FALSE: at each assertion `c` is 5: the guard was dropped by `clear`, `truncate`,
//@ WHY THE CONTRACT IS FALSE: `ManuallyDrop::drop` or the assignment through `r`, and `G::drop` wrote it.
//@ fixed-by: D-140: a call handed mutable access to a value whose glue may write
//@ fixed-by: (`drop_glue_writes::ty_lends_writing_glue`) is a hand-off, unless the callee is a standard
//@ fixed-by: function known never to drop a value of its type arguments.
//@ teeth: MEASURED: with D-140's hand-off disabled every assertion is `verified`; with the by-move
//@ teeth: hand-off alone, `clear` and `truncate` are still `verified`; with D-140 every one is FAILED.
//@ also-verified: <G<'_> as std::ops::Drop>::drop
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::mem::ManuallyDrop;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

pub fn clear() {
    let mut c = 0u32;
    let mut v: Vec<G<'_>> = Vec::new();
    v.push(G(&mut c));
    v.clear();
    std::mem::forget(v);
    proof_assert!(c@ == 0);
}

pub fn truncate() {
    let mut c = 0u32;
    let mut v: Vec<G<'_>> = Vec::new();
    v.push(G(&mut c));
    v.truncate(0);
    std::mem::forget(v);
    proof_assert!(c@ == 0);
}

pub fn manually_dropped_clear() {
    let mut c = 0u32;
    let mut v: ManuallyDrop<Vec<G<'_>>> = ManuallyDrop::new(Vec::new());
    v.push(G(&mut c));
    v.clear();
    proof_assert!(c@ == 0);
}

pub fn manually_drop_drop() {
    let mut c = 0u32;
    let mut m = ManuallyDrop::new(G(&mut c));
    unsafe { ManuallyDrop::drop(&mut m) };
    proof_assert!(c@ == 0);
}

pub fn assign_through_reference() {
    let mut c = 0u32;
    let mut o = Some(G(&mut c));
    {
        let r = &mut o;
        *r = None;
    }
    std::mem::forget(o);
    proof_assert!(c@ == 0);
}
