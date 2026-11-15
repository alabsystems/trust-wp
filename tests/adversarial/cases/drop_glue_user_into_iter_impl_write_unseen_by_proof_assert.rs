//@ expect: reject
//@ mechanism: the proof_assert spelling of drop_glue_user_into_iter_impl_read_as_std_pinned: a writing
//@ mechanism: guard handed BY MOVE to a USER impl of `IntoIterator::into_iter`, which drops it, so
//@ mechanism: `G::drop` stores 5 into `c`: `let it = G(&mut c).into_iter(); proof_assert!(c@ == 0)`. The
//@ mechanism: substitution walk asks `call_handoff_roots` whether the call may run the glue, and that asked
//@ mechanism: the standard-library keep-list (`IntoIterator::into_iter` never drops its type arguments) of
//@ mechanism: the callee the call operand names, the trait's declaration in `core`, not the impl that runs;
//@ mechanism: so the call was no hand-off and `c` kept 0. The ensures-lane spelling is refused by an
//@ mechanism: unrelated fail-closed `false`, which does not reach the assertion.
//@ accept-means: a `proof_assert!` is credited with a local's value from before drop glue, run inside a
//@ accept-means: user trait impl the keep-list takes for the standard library's, wrote it.
//@ WHY THE CONTRACT IS FALSE: `into_iter` drops the guard, whose `Drop` stores 5 into `c`, before the
//@ WHY THE CONTRACT IS FALSE: assertion.
//@ fixed-by: D-140: a trait method is looked up on the keep-list as the impl rustc resolves it to in the
//@ fixed-by: host's environment (`call_never_drops_type_args`); a local impl is never the standard library's.
//@ teeth: MEASURED on one binary with the lookup by the trait method disabled by an env knob (never
//@ teeth: committed): `proof_assert in creusot_test::method_pa verified`; with the resolved impl it is
//@ teeth: FAILED. The function is `unknown` either way on the fail-closed `false` above.
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
    #[ensures(true)]
    fn into_iter(self) -> std::iter::Empty<u32> {
        std::iter::empty()
    }
}

#[requires(true)]
pub fn method_pa() {
    let mut c = 0u32;
    let it = G(&mut c).into_iter();
    let _ = it;
    proof_assert!(c@ == 0);
}
