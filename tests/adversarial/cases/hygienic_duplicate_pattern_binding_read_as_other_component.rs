//@ expect: reject
//@ verdict: error
//@ refused-with: spelled `a`, apart only by hygiene
//@ mechanism: a `macro_rules!` item's tuple parameter pattern binds two names spelled `a`, apart only
//@ mechanism: by hygiene: the caller-supplied `$a` (component 0) and the macro's own `a` (component
//@ mechanism: 1), which the body returns. D-177 states each binding as its projection
//@ mechanism: (`param_pattern_bindings`), keyed by spelling, so the clause's `a` is substituted by
//@ mechanism: whichever projection is collected last: here component 1, which the body returns. The
//@ mechanism: clause names `$a`, component 0. Found probing sideways from D-177.
//@ accept-means: a pattern binding was read as another binding of the same spelling.
//@ WHY THE CONTRACT IS FALSE: `f((1, 2))` returns 2 and claims `$a`, which is 1.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ teeth: LIVE at the head D-181 was reviewed at: ACCEPTED, exit 0, `f verified`. The same macro with
//@ teeth: the pattern written `(a, $a)` (so the last collected projection is the clause's own) is
//@ teeth: FAILED, so the reading follows the collection order, not the clause. Both the same at the
//@ teeth: campaign tip the branch that carries D-177 merged, before D-177.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

macro_rules! mk {
    ($a:ident) => {
        #[ensures(result == $a)]
        pub fn f(($a, a): (u32, u32)) -> u32 {
            a
        }
    };
}

mk!(a);
