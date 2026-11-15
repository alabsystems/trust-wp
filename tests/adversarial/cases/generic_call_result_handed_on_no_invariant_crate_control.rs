//@ expect: verify
//@ mechanism: the twin of generic_call_result_handed_on_control in a crate with NO `Invariant`
//@ mechanism: impl: the same `id(t.clone())`. With no type invariant anywhere, no parameter
//@ mechanism: clause is built, so nothing is owed at the call and `g` verifies. The pair says the
//@ mechanism: FAILED verdict there is the type-parameter clause of D-141, not the clone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == t)]
pub fn id<T>(t: T) -> T {
    t
}

#[ensures(true)]
pub fn g<T: Clone>(t: &T) -> T {
    id(t.clone())
}
