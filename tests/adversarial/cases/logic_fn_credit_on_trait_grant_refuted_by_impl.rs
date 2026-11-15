//@ expect: reject
//@ mechanism: a trait default logic method `T2::w` is proved in the logic pass on the grant of a supertrait's logic method, `T1::v`'s `result >= 0`. The only impl then refutes that grant in the implementation discharge (D-110), which runs after the pass and withdrew the grant from later consumers, but `w`'s credit stood on it. It is now withdrawn with the grant, and `w`'s own axiom with it.
//@ accept-means: a logic function credited on a trait grant its implementation refutes.
//@ WHY IT IS FALSE: at `Self = i32`, `w(x) = v(x) = -1`.
//@ verdict: failed
//@ fn-failed: <i32 as T1>::v
//@ teeth: measured with the stale-credit withdrawal knocked out: `creusot_test::T2::w verified ✓` stands beside `<i32 as T1>::v FAILED ✗` and `T1::v postcondition withheld from callers`, TEETH LOST. The twin whose impl honours the grant keeps `w`'s credit and verifies at exit 0 with the fix (logic_fn_credit_on_trait_grant_honoured_control.rs).
//@ fixed-by: D-159 (the withdrawal runs at every round of the implementation discharge)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait T1 {
    #[logic]
    #[ensures(result >= 0)]
    fn v(self) -> Int;
}

pub trait T2: T1 + Sized {
    #[logic]
    #[ensures(result >= 0)]
    fn w(self) -> Int {
        self.v()
    }
}

impl T1 for i32 {
    #[logic(open)]
    fn v(self) -> Int {
        pearlite! { -1 }
    }
}

impl T2 for i32 {}
