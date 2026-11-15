//@ expect: reject
//@ mechanism: a method of an impl of a clause-free trait carries no clause and its trait declares
//@ mechanism: none, yet it is verified as a contracted body (against the declaration, then its
//@ mechanism: refinement), so the clause-free cap never applies to it. Its `assert!` charge is then
//@ mechanism: proved by the encoder's 64-bit complement (u8_bitnot_read_at_64_bits.rs): `!0u8` reads
//@ mechanism: as `2^64 - 1`, not `255`. The same body as an inherent method, or as the trait's
//@ mechanism: default body, is capped (`unknown`). The shift (`x << 1` at `128`), NaN (`x == x` on an
//@ mechanism: `f64`) and `u128` `&` spellings measured ACCEPTED the same way.
//@ fixed-by: D-242: the driver lowers a machine bit operation as the operation AT ITS TYPE
//@ fixed-by: (`__trust_wp_int_bitop_u8(!x)`), so `!0u8` is `255` and the panic is found. A fix that
//@ fixed-by: caps a body because its source carries no clause would not have reached this method.
//@ accept-means: `<S as Tr>::m` panics at `x = 0` and is reported `verified`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `S.m(0)` panics: `!0u8 == 255`.
//@ teeth: ACCEPTED (`<S as Tr>::m verified`), with and without D-142's proved dead edges: a
//@ teeth: refinement-checked impl method is never capped.
//@ teeth: ACCEPTED on trust-wp 7726ea81 (the parent of D-242); `<S as Tr>::m FAILED` with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub trait Tr {
    fn m(&self, x: u8);
}

pub struct S;

impl Tr for S {
    fn m(&self, x: u8) {
        if x == 0 {
            assert!(!x != 255);
        }
    }
}
