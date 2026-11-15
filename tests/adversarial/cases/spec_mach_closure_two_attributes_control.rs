//@ expect: verify
//@ mechanism: control for spec_mach_closure_two_attributes_add_gt_operand: a closure contract of
//@ mechanism: two attributes over `i32` arithmetic. The type-check vehicle reads a closure only when
//@ mechanism: the attribute's item is the bare closure, so a second attribute leaves both clauses
//@ mechanism: with no type check, and D-232 reads a clause no type check reads by syntax alone.
//@ WHY THE CONTRACT IS TRUE: x < 100, so x + 1 does not wrap and the body returns it.
//@ xfail: the clause `result == x + 1i32` gets no type check, and its `+` on `i32` is refused
//@ xfail: (D-232); a single attribute is read at its type.
//@ xfail-verdict: unknown
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(stmt_expr_attributes, proc_macro_hygiene)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn two_attributes() {
    let c = #[requires(x < 100i32)]
    #[ensures(result == x + 1i32)]
    |x: i32| -> i32 { x + 1 };
    let _ = c(1i32);
}
