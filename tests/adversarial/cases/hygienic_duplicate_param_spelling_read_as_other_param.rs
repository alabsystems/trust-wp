//@ expect: reject
//@ verdict: error
//@ refused-with: spelled `x`, apart only by hygiene
//@ also-verified: f_def_site
//@ mechanism: a `macro_rules!` item has two parameters spelled `x`, apart only by hygiene: the
//@ mechanism: macro's own `x` and the caller-supplied `$x`. Rust keeps them distinct, so the body's
//@ mechanism: `x` is the first. trust-wp names parameters by spelling, so the clause text's `x` is
//@ mechanism: one of two parameters at once: the owner's lane reads it as the first, and a call binds
//@ mechanism: clause names to arguments by name with the later name winning, so a caller reads it as
//@ mechanism: the second. `f_call_site`'s clause names `$x`, the second, and is proved of a body that
//@ mechanism: returns the first; `f_def_site`'s clause names the first, which is true, and `g` is
//@ mechanism: granted it at the second argument. Found probing sideways from D-177's positional names.
//@ accept-means: a clause was read at a parameter other than the one it names, or the owner and its
//@ accept-means: callers read one clause name at two different parameters.
//@ WHY THE CONTRACT IS FALSE: `f_call_site(1, 2)` returns 1 and claims `$x`, the second argument, 2;
//@ WHY THE CONTRACT IS FALSE: `g` returns `f_def_site(1, 2)`, which is 1, and claims 2.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ teeth: LIVE at the head D-181 was reviewed at: ACCEPTED, exit 0, `f_call_site`, `f_def_site` and
//@ teeth: `g` verified, and each host alone the same. ACCEPTED, exit 0, at the campaign tip the
//@ teeth: branch that carries D-177 merged too.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

macro_rules! clause_names_call_site {
    ($x:ident) => {
        #[ensures(result == $x)]
        pub fn f_call_site(x: u32, $x: u32) -> u32 {
            x
        }
    };
}

macro_rules! clause_names_def_site {
    ($x:ident) => {
        #[ensures(result == x)]
        pub fn f_def_site(x: u32, $x: u32) -> u32 {
            x
        }
    };
}

clause_names_call_site!(x);
clause_names_def_site!(x);

#[ensures(result == 2u32)]
pub fn g() -> u32 {
    f_def_site(1u32, 2u32)
}
