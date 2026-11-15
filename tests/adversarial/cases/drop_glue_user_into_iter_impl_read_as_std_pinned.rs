//@ expect: reject
//@ mechanism: a writing guard handed BY MOVE to a USER impl of a standard trait method that D-140's
//@ mechanism: keep-list names: `IntoIterator::into_iter(G(&mut c))` and `G(&mut c).into_iter()`, where
//@ mechanism: `into_iter(self)` drops `self`, so `G::drop` stores 5 into `c` before the host reads it.
//@ mechanism: `call_handoff_roots` asked `std_callee_never_drops_type_args` of the callee `DefId` the
//@ mechanism: call operand names, which for a trait method is the trait's declaration in `core`
//@ mechanism: (`IntoIterator::into_iter`), not the impl that runs; so a user impl was read as a
//@ mechanism: standard-library function known never to drop its arguments and the call as no hand-off.
//@ mechanism: The same host over a trait the list does not name (`MyInto::my_into(G(&mut c))`) and over
//@ mechanism: a free function (`consume(G(&mut c))`) is a hand-off. The keep-list also names `Index::index`
//@ mechanism: and `IndexMut::index_mut`, whose index is taken by value.
//@ accept-means: a host is credited against the value a local had before drop glue, run inside a user
//@ accept-means: trait impl the keep-list takes for the standard library's, wrote it.
//@ WHY THE CONTRACT IS FALSE: each host returns 5: `into_iter` drops the guard, whose `Drop` stores 5 into
//@ WHY THE CONTRACT IS FALSE: `c`, and `c` is read after the call.
//@ fixed-by: D-140 closes the keep-list gap: a trait method is looked up as the impl rustc resolves it to
//@ fixed-by: (`call_never_drops_type_args`), and a local impl is never the standard library's. Each host
//@ fixed-by: here is still rejected first by an unrelated refusal (see teeth); the proof_assert spelling,
//@ fixed-by: which that refusal does not reach, is drop_glue_user_into_iter_impl_write_unseen_by_proof_assert.
//@ teeth: PINNED: each host is `unknown` on a fail-closed `false` that a trait-method call handed a
//@ teeth: borrow-holding value by move gets whatever its `Drop` does, before and after the lookup by the
//@ teeth: resolved impl; the same file with a `Drop` that only reads is `unknown` too. A change that lifts
//@ teeth: that refusal must keep this case rejected.
//@ also-verified: <G<'_> as std::ops::Drop>::drop, <G<'a> as std::iter::IntoIterator>::into_iter
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

impl<'a> IntoIterator for G<'a> {
    type Item = u32;
    type IntoIter = std::iter::Empty<u32>;
    #[requires(true)]
    fn into_iter(self) -> std::iter::Empty<u32> {
        std::iter::empty()
    }
}

#[ensures(result@ == 0)]
pub fn path_call() -> u32 {
    let mut c = 0u32;
    let _it = IntoIterator::into_iter(G(&mut c));
    c
}

#[ensures(result@ == 0)]
pub fn method_call() -> u32 {
    let mut c = 0u32;
    let it = G(&mut c).into_iter();
    let _ = it;
    c
}
