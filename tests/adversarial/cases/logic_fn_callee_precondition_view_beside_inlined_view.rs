//@ expect: reject
//@ mechanism: an operator whose callee owes a precondition, beside an inlined call whose body calls that callee by name. `s@` is `<S as View>::view(s)`, whose impl requires `self.n > 0`; the parsed body keeps `s@` as a view node, so D-136 refuses a body whose type-checked form holds more owing calls spelled `view` than the parsed body. `H::helper(t)` is an open associated logic function with no contract, which `extract_logic_fn_defs` replaces by its body, `t.view()`. The check counted that INLINED call as the counterpart of `s@`, and the walk owed `t.n > 0`, which the caller requires, and nothing of `s`. Found probing sideways from D-136's counting.
//@ accept-means: a logic function that views a value outside the precondition of the `View` impl that runs is credited `verified`, because an inlined callee's body views another value.
//@ WHY IT IS FALSE: at `s.n == 0` the body evaluates `s@`, which calls `<S as View>::view(s)`, and that requires `self.n > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED on the rustc-resolution walk that counts the inlined body: `creusot_test::caller verified ✓` for the method spelling `t.view()` and for `View::view(t)`. The crate is rejected on the impl's refinement; the caller's credit is the false one. Without the inlined call the same build refuses the caller (logic_fn_view_operator_impl_precondition.rs). The control is logic_fn_callee_precondition_view_beside_inlined_view_control.rs.
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

pub struct H;

impl H {
    #[logic(open)]
    pub fn helper(t: S) -> Int {
        t.view()
    }
}

#[logic]
#[requires(t.n > 0)]
#[ensures(true)]
pub fn caller(s: S, t: S) -> Int {
    pearlite! { s@ + H::helper(t) }
}
