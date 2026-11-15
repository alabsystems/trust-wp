//@ expect: verify
//@ xfail: the price of `String::reserve`'s requirement (D-121): it bounds the char view's length,
//@ xfail: and ay panics declaring `String`'s view `len` ("registered without a unique core
//@ xfail: declaration identity"), so every `String::reserve` call is an ay-panic error, even one
//@ xfail: that reserves nothing. trust-wp reports the panic as an error, so no call is credited.
//@ mechanism: a `String::reserve(0)` on any string, which never panics. An XPASS here means the
//@ mechanism: `String` view length encodes again; a `reserve` of an unbounded amount must then
//@ mechanism: still be refused (`FAILED` on the requirement), not credited.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — MEASURED `f verified ✓`, exit 0, with `String::reserve`'s requirement removed,
//@ teeth: where `reserve(n)` for an unbounded `n` was ACCEPTED too; with it, an ay-panic error.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(s: &mut String) {
    s.reserve(0)
}
