//@ expect: reject
//@ mechanism: `255u8 + 1u8 > 255u8` in the postcondition of a function returning `impl Sized`,
//@ mechanism: whose clause no type check reads (D-232's untyped reading). That reading takes an
//@ mechanism: operator on two literals as `Int` arithmetic ("Pearlite's literals are `Int`",
//@ mechanism: contract_parser::machine_arith::binary_is_int_syntax), but the parser drops a literal's
//@ mechanism: suffix and only an UNSUFFIXED literal is `Int` in the pinned oracle (creusot-std-proc
//@ mechanism: pretyping lowers it to `View::view(lit as i128)`); `255u8` keeps its type, so the sum
//@ mechanism: is creusot-std's `UInt8$BW$.add`, which wraps (D-135 item 3).
//@ accept-means: an operator on two machine-suffixed literals in a clause no type check reads was
//@ accept-means: read as mathematical integer arithmetic.
//@ WHY THE CONTRACT IS FALSE: the wrapping sum of 255u8 and 1u8 is 0, which is not above 255.
//@ fixed-by: OPEN: committed RED. In the untyped reading a pair of literals is `Int` only when
//@ fixed-by: neither carries a machine-integer suffix; a suffixed literal is a value of its suffix's
//@ fixed-by: type, so an operator on one reads at that type or is refused.
//@ teeth: ACCEPTED at exit 0 when written, as on the campaign base; the typed spelling of the same
//@ teeth: clause (a function returning no `impl` type) is refuted. Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(255u8 + 1u8 > 255u8)]
pub fn suffixed_literal_sum(x: u8) -> impl Sized {
    x
}
