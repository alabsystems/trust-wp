//@ expect: verify
//@ xfail: a callee's `requires` clause is PARSED at the call site, where a named field
//@ xfail: access is still `__trust_wp_field_<name>`. The pass that rewrites that to the
//@ xfail: positional accessor MIR extraction produced reads one flat name->index table
//@ xfail: built from the CALLER's own signature, so a field name the caller's signature
//@ xfail: does not contain is never rewritten and the obligation is stated over an
//@ xfail: accessor nothing in the VC constrains. Its twin
//@ xfail: call_site_named_field_mapped_control differs only in putting the struct in the
//@ xfail: caller's signature, and verifies. Retire this directive when the callee's clause
//@ xfail: is rewritten in the CALLEE's field environment, where it was authored.
//@ mechanism: nothing here is a type invariant: this is the plain `#[requires]` lane, and
//@ mechanism: it is the reason a caller-constructed aggregate refuses in the invariant lane
//@ mechanism: too. Measured with the smallest shape that shows it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub a: i32,
    pub b: i32,
}

#[requires(s.a@ == 4)]
#[ensures(result@ == 4)]
pub fn f(s: S) -> i32 {
    s.a
}

#[ensures(result@ == 4)]
pub fn caller() -> i32 {
    f(S { a: 4, b: 6 })
}
