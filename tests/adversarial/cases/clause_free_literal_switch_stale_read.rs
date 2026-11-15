//@ expect: reject
//@ mechanism: D-142 reads a switch edge as dead when the walk charged it or a literal never selects
//@ mechanism: it. `b` is written through `r`, a write the primary walk does not see, so a reading of
//@ mechanism: `b` at its entry value `true` would make the failing arm of `assert!(b)` look dead.
//@ mechanism: The exactness gate (no address-taken local) and the discriminant's value stability
//@ mechanism: keep every edge of this body out of the dead set.
//@ accept-means: a clause-free body that panics on every call is credited `verified` because the
//@ accept-means: cap read a stale literal as proof that its panic arm is never taken.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims no execution panics; `*r = false`
//@ WHY THE CONTRACT IS FALSE: makes `assert!(b)` fail on every call of `hop`.
//@ verdict: unknown
//@ teeth: UNVERIFIED for the cap — the unstable switch already states its arm as the obligation
//@ teeth: `false`, so the body is withheld before the cap reads it; the case pins the shape.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop() {
    let mut b = true;
    let r = &mut b;
    *r = false;
    assert!(b);
}
