//@ expect: reject
//@ mechanism: bitwise `!a <= a` over `u32` (the oracle's `bw_not` is 2^32 - 1 - a, not -a - 1) --
//@ mechanism: an arithmetic operator on machine-integer operands in spec text. D-135 item 3: in the
//@ mechanism: pinned oracle it means creusot-std's logic impl, the type's bit-vector operation,
//@ mechanism: which WRAPS (`u32 + u32` is `creusot.int.UInt32$BW$.add`); a reading of it as
//@ mechanism: mathematical integer arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 0: `!a` is u32::MAX.
//@ refused-with: the oracle's `!` on `u32` is its bit-vector operation
//@ teeth: rejected `failed` when written, for another reason: trust-wp-core reads `!` on an
//@ teeth: integer operand as boolean negation (counterexample `a = false`). The case pins the
//@ teeth: shape; its teeth are UNVERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(!a <= a)]
pub fn not_le_operand(a: u32) {}
