//@ expect: reject
//@ mechanism: the callee-precondition sibling of closure_index_through_option_map_uncharged. A
//@ mechanism: contract-free closure that calls a `#[requires]`-bearing function is handed to
//@ mechanism: `Iterator::map`. Creusot's extern spec for `map` requires
//@ mechanism: `forall<e, i2> self.produces(Seq::singleton(e), i2) && inv(e) ==> f.precondition((e,))`,
//@ mechanism: and the closure's precondition is its body's weakest precondition, `x@ != 0`, so the
//@ mechanism: call is refuted. trust-wp's builtin spec for `map` has an empty `requires`, the host
//@ mechanism: calls no `#[requires]`-bearing function itself and has no assert of its own, and a
//@ mechanism: closure is never a target of `fn_owes_abort_or_callee_precondition`. The
//@ mechanism: precondition is granted to `needs_nonzero`'s body and owed by nobody: the D-54
//@ mechanism: laundering, through a std combinator instead of a user generic hop.
//@ accept-means: a `#[requires]` is laundered away by routing the call through a contract-free
//@ accept-means: closure and `Iterator::map`: `hop(&[0])` divides by zero and the crate exits 0
//@ accept-means: with `hop` named in no verdict line.
//@ fixed-by: D-118. The closure escapes into `Iterator::map`, so it is a verification target under
//@ fixed-by: `requires true` and is refuted on `needs_nonzero`'s precondition; the same rule covers
//@ fixed-by: the other adapters and combinators (closure_callee_requires_through_iterator_adapters_uncharged,
//@ fixed-by: closure_index_through_option_combinators_uncharged).
//@ teeth: ACCEPTED, exit 0, `needs_nonzero verified` and `hop` unnamed, on the binary before
//@ teeth: D-95, after it, and at the parent of D-118. The same violated call with no closure in the
//@ teeth: way is refuted (contract_free_local_requires_uncharged). Compiled and run as a plain
//@ teeth: program, `hop(&[0])` panics with "attempt to divide by zero".
//@ also-verified: needs_nonzero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ != 0)]
#[ensures(result@ == 10 / x@)]
pub fn needs_nonzero(x: u32) -> u32 {
    10 / x
}

// `hop(&[0])` calls `needs_nonzero(0)`, outside its precondition.
pub fn hop(v: &[u32]) -> Option<u32> {
    v.iter().map(|&x| needs_nonzero(x)).next()
}
