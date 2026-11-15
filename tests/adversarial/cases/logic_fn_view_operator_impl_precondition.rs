//@ expect: reject
//@ mechanism: a precondition behind an operator: `s@` in a logic body is Creusot's `View::view(s)`, resolved to the crate's `impl View for S`, whose `view` requires `self.n > 0`. The parsed body keeps `s@` as a view NODE, not a call, so the callee-precondition walk never sees a callee and owes nothing; the type-check vehicle spells it `ViewTc::__trust_wp_tc_view`, whose blanket impl hides the impl that runs. Found probing sideways from D-120.
//@ accept-means: a logic function that views a value outside the precondition of the `View` impl that runs is credited `verified`.
//@ WHY IT IS FALSE: at `s.n == 0` the body evaluates `s@`, which calls `<S as View>::view(s)`, and that requires `self.n > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED, with D-120 open: `creusot_test::caller verified ✓` beside `<S as creusot_std::View>::view refinement unknown (no trait contract)`. The crate is rejected on the impl's refinement; the caller's credit is the false one. The control is logic_fn_view_operator_impl_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub n: Int,
}

impl View for S {
    type ViewTy = Int;

    #[logic]
    #[requires(self.n > 0)]
    fn view(self) -> Int {
        pearlite! { self.n }
    }
}

#[logic]
#[ensures(true)]
pub fn caller(s: S) -> Int {
    pearlite! { s@ }
}
