//@ expect: reject
//@ mechanism: recursive_variant_reads_local_before_borrow_write's family, three more writes the
//@ mechanism: recursive-call walk (`extract_recursive_calls_from_block`) did not see: a loan held below the
//@ mechanism: top of a by-value argument (`poke(H(&mut m))`, `H` with no `Drop`, the verified `poke`
//@ mechanism: storing 5 through it), a store into a FIELD of a local (`p.0 = 5`, which the walk skipped,
//@ mechanism: keeping `p` at `(0, 0)`), and a by-value PARAMETER lent to a callee (`bump(&mut n)` then
//@ mechanism: `f(n - 1)`, read as the entry `n` minus one). Each recursive call was checked against the
//@ mechanism: value from before the write.
//@ accept-means: a recursive function that does not terminate is credited `verified ✓ (termination)` under
//@ accept-means: `#[check(terminates)]`.
//@ WHY THE CONTRACT IS FALSE: `rec_struct_loan(1)` and `rec_field_write(1)` call themselves with 5 forever;
//@ WHY THE CONTRACT IS FALSE: `rec_param_borrow(n)` bumps `n` and calls itself with `n` again.
//@ fixed-by: D-140: the recursive-call walk forgets every lent local after a call handed an argument it
//@ fixed-by: may write through, and unbinds a local written through a projection or by a value it cannot
//@ fixed-by: translate.
//@ teeth: MEASURED on one binary with the walk's forgetting and unbinding disabled by env knobs (never
//@ teeth: committed): `rec_struct_loan` and `rec_field_write` ACCEPTED, exit 0, `verified ✓ (termination)`;
//@ teeth: `rec_param_borrow` printed `verified ✓ (termination)` beside an `unknown` from its body lane. With
//@ teeth: them, each is FAILED (`variant decrease`).
//@ also-verified: poke, bump
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct H<'a>(pub &'a mut u32);

#[check(terminates)]
#[ensures(true)]
pub fn poke(h: H<'_>) {
    *h.0 = 5;
}

#[check(terminates)]
#[variant(n@)]
pub fn rec_struct_loan(n: u32) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    poke(H(&mut m));
    rec_struct_loan(m);
}

#[check(terminates)]
#[variant(n@)]
pub fn rec_field_write(n: u32) {
    if n == 0 {
        return;
    }
    let mut p = (0u32, 0u32);
    p.0 = 5;
    rec_field_write(p.0);
}

#[check(terminates)]
#[requires((*x)@ < 1000)]
#[ensures((^x)@ == (*x)@ + 1)]
pub fn bump(x: &mut u32) {
    *x += 1;
}

#[check(terminates)]
#[requires(n@ < 1000)]
#[variant(n@)]
pub fn rec_param_borrow(mut n: u32) {
    if n == 0 {
        return;
    }
    bump(&mut n);
    rec_param_borrow(n - 1);
}
