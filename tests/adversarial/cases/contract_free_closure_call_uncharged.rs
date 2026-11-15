//@ expect: reject
//@ mechanism: a generic `Fn` hop takes `f.precondition(args)` as a CREDIT and is excused its
//@ mechanism: callee obligation, but at the call site a CONTRACT-FREE closure's `precondition`
//@ mechanism: discharges as trivially true instead of as its body's weakest precondition. The
//@ mechanism: obligation the body really owes — `needs_nonzero`'s `#[requires(x != 0)]` — is
//@ mechanism: emitted on no target at all: the closure body is a verification target of nothing
//@ mechanism: for a callee precondition, and the caller is charged nothing. Grant and obligation
//@ mechanism: are different code: the hop's credit is the uninterpreted `precondition` predicate,
//@ mechanism: the caller's discharge is a contract-free closure resolved to `true`.
//@ accept-means: an ACCEPT proves a `#[requires]` can be laundered away by routing the call
//@ accept-means: through a contract-free closure and a generic `Fn` bound — the precondition is
//@ accept-means: granted at the hop and owed by nobody, so every contracted function reachable
//@ accept-means: through a closure is callable outside its precondition with a clean verdict.
//@ fixed-by: D-54
//@ teeth: ACCEPTED on this tree and on the campaign build (exit 0, `3 verified, 0 failed,
//@ teeth: 0 errors`), while the same violated call with NO closure in the way is refuted and the
//@ teeth: same hop with its `f.precondition` credit REMOVED is refuted on `*f.precondition(0)` —
//@ teeth: so the obligation exists and only the credit hands it to a place that drops it. The
//@ teeth: contract is refutable by the body's single execution: compiled and run as a plain
//@ teeth: program it panics with `attempt to divide by zero`. Fn, FnMut and FnOnce all accept.
//@ also-verified: needs_nonzero, call_with_zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x != 0i32)]
#[ensures(result@ == 10i32@ / x@)]
pub fn needs_nonzero(x: i32) -> i32 {
    10i32 / x
}

#[requires(f.precondition((0i32,)))]
pub fn call_with_zero<F: Fn(i32) -> i32>(f: F) -> i32 {
    f(0i32)
}

// FALSE: `c` is contract-free, so `c.precondition((0,))` is its body's weakest
// precondition, `0 != 0`. This call is outside `needs_nonzero`'s precondition
// and divides by zero.
#[ensures(result@ == result@)]
pub fn boom() -> i32 {
    let c = |x: i32| needs_nonzero(x);
    call_with_zero(c)
}
