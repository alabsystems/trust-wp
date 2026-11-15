//@ expect: verify
//@ mechanism: the true control of structpat_let_destructure_in_tuple_ctor_reorder: `g` returns
//@ mechanism: the field the inner binding names. Also guards the tuple-style outer read, which
//@ mechanism: stays positional on purpose (unnamed fields: written position is declared position).
//@ accept-means: n/a (control).
//@ teeth: MEASURED on the merged tip 4e4613be: failed, exit 1 — the other half of the pair.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }
pub struct W(pub S);

#[requires({ let W(S { a: aa, b: _bb }) = w; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(w: W) -> u32 { w.0.a }
