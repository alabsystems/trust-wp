//@ expect: reject
//@ mechanism: a clause no type check reads (the function returns `impl Sized`) is read by syntax
//@ mechanism: alone, and syntax makes an `@` operand an `Int`. A `View` whose `ViewTy` is a machine
//@ mechanism: integer makes `w@ + 1u32` the oracle's `UInt32$BW$.add`, which wraps (D-135 item 3).
//@ accept-means: an `@` operand of a clause no type check reads was read as an `Int` where its view
//@ accept-means: type is a machine integer.
//@ WHY THE CONTRACT IS FALSE: w = W(u32::MAX): w@ + 1u32 wraps to 0, below w@.
//@ teeth: rejected `unknown` when written (a sort-coercion bridge leaves the user view
//@ teeth: unconstrained), so the case pins the shape and its teeth are UNVERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W(pub u32);

impl View for W {
    type ViewTy = u32;

    #[logic]
    fn view(self) -> u32 {
        self.0
    }
}

#[ensures(w@ + 1u32 > w@)]
pub fn view_ty_u32(w: W) -> impl Sized {
    0u8
}
