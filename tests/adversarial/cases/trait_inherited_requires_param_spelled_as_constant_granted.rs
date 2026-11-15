//@ expect: reject
//@ verdict: failed
//@ fn-failed: go
//@ also-verified: <A as t::Tr>::f
//@ mechanism: the precondition sibling of trait_inherited_clause_param_spelled_as_constant_granted.
//@ mechanism: The required method's `requires(K > 5)` names its parameter `K`, spelled like the
//@ mechanism: crate's one constant (10). A's impl assumes it renamed to `k > 5` and divides by `k`; a
//@ mechanism: generic caller owes it with `K` bound to its argument. Read as the constant at the call
//@ mechanism: site, `go` would discharge `10 > 5` and pass 0 into a body that divides by it.
//@ fixed-by: n/a (regression guard beside D-110's renaming and D-111's constant table)
//@ accept-means: `go` passes 0 where the contract requires more than 5, and A's body then divides by 0; A's impl is correct under its precondition, so `<A as t::Tr>::f` is a true credit.
//@ teeth: MEASURED before D-110: rejected as here (`go FAILED`), with A's impl refuted as well (its own reading of `K` was the constant). At D-110: `<A as t::Tr>::f verified ✓`, `go FAILED ✗`. The violated obligation is the call's `(0 > 5)`, the parameter bound to the argument. It has no verifying twin: a generic call to a trait method whose impl can panic is demoted by the panic lane (`panic paths unchecked`) whatever it passes; the renaming it rests on is isolated by trait_inherited_clause_param_spelled_as_constant_honoured_twin.rs.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(non_snake_case)]
extern crate creusot_std;
use creusot_std::prelude::*;

pub mod c {
    pub const K: i32 = 10;
}

pub mod t {
    use creusot_std::prelude::*;
    pub trait Tr {
        #[requires(K > 5i32)]
        fn f(&self, K: i32) -> i32;
    }
}

pub struct A;

impl t::Tr for A {
    fn f(&self, k: i32) -> i32 {
        100 / k
    }
}

pub fn go<T: t::Tr>(x: &T) -> i32 {
    x.f(0)
}
