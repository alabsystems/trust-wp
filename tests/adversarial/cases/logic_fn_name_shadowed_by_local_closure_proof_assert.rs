//@ expect: reject
//@ mechanism: a LET-BOUND local shadows a logic function of the same name for every assertion
//@ mechanism: after it: rustc resolves `k(x)` in the proof_assert / invariant to the local
//@ mechanism: closure. The logic-identity resolver (logic/identity.rs resolve_call_name_unchecked)
//@ mechanism: withholds the module answer for a clause BINDER, a parameter, and (shadowed_by_body_item)
//@ mechanism: a body ITEM, but not for a body-local binding, so `k` is read as `a::k` and the
//@ mechanism: assertion is proved about a function it does not name. Creusot rejects the program
//@ mechanism: (a program closure called in logic); trust-wp must refuse, not prove.
//@ accept-means: the assertion's `k` was read as the module's logic fn although it names the
//@ accept-means: local closure.
//@ WHY THE CONTRACT IS FALSE: the closure returns 0 and `x != 0`, so `k(x) == x` is false.
//@ fixed-by: OPEN — committed RED. A call head that a body local binds must be refused in an
//@ fixed-by: assertion or invariant, as a binder or parameter of that name already is.
//@ teeth: ACCEPTED (exit 0, the proof_assert verified) both at the review base and at the head it
//@ teeth: reviewed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: i64) -> i64 { p }
}
use a::k;

#[requires(x != 0i64)]
pub fn f(x: i64) {
    let k = |_p: i64| 0i64;
    proof_assert!(k(x) == x);
}
