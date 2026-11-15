//@ expect: verify
//@ xfail: `(*s).m()` of a snapshot `s` is refused (D-201): the resolver does not compute the
//@ xfail: `Deref` target Rust's method lookup starts at. Before D-201 it was read at
//@ xfail: `Snapshot<A>` as `<Snapshot<A> as Tr>::m` (true) and the contract refuted. The isolating
//@ xfail: twin of method_call_deref_snapshot_receiver_read_at_snapshot_type_granted.rs.
//@ mechanism: control: `(*s).m()` with `s: Snapshot<A>` is `A`'s inherent `m` (false), and `f` returns
//@ mechanism: false.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` with D-200 in force)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A;
impl A {
    #[logic(open)]
    pub fn m(self) -> bool {
        pearlite! { false }
    }
}

pub trait Tr {
    #[logic]
    fn m(self) -> bool;
}

impl Tr for Snapshot<A> {
    #[logic(open)]
    fn m(self) -> bool {
        pearlite! { true }
    }
}

#[ensures(result == (*s).m())]
pub fn f(s: Snapshot<A>) -> bool {
    let _ = s;
    false
}
