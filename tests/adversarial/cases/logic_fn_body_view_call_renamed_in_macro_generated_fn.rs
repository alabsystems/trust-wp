//@ expect: reject
//@ mechanism: the macro spelling of logic_fn_body_view_call_renamed: a `macro_rules!` item writes a logic function whose body is `view(y)`, under `use crate::succ as view;` at the crate root. rustc resolves the call to `succ`; the contract parser reads the spelling `view(e)` as the view builtin, so the ensures lane proved `result == y` of a body that is `y + 1`. The generated body is settled like a written one, so it is misread and refused (D-136). Found probing sideways from D-120.
//@ accept-means: a macro-generated logic function whose body calls a function renamed onto the spelling `view` is credited with the builtin view's postcondition, and the crate exits 0.
//@ WHY IT IS FALSE: `caller(y)` is `succ(y)`, which is `y + 1`, never `y`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_body_view_call_renamed_in_macro_generated_fn_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn succ(x: Int) -> Int {
    x + 1
}

use crate::succ as view;

macro_rules! mk {
    ($name:ident) => {
        #[logic]
        #[ensures(result == y)]
        pub fn $name(y: Int) -> Int {
            view(y)
        }
    };
}

mk!(caller);
