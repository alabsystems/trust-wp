//@ expect: verify
//@ mechanism: control for raw_ptr_thin_cast_in_clause_not_its_operand and the shapes of
//@ mechanism: should_succeed/lang/cast_ptr.rs: a clause's cast that keeps the pointee (`*const T`
//@ mechanism: to `*mut T`, `T: ?Sized`) is the identity, and a body's metadata-dropping cast and the
//@ mechanism: clause that describes it are read as the same `thin` of the same operand.
//@ teeth: control; before clause casts were read, both clauses were parse errors
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn round_trip<T: ?Sized>(p: *const T) {
    proof_assert!(p == (p as *mut T) as *const T)
}

#[ensures(result == p as *const T)]
pub fn thin<T>(p: *const [T]) -> *const T {
    p as *const T
}

#[requires(p == q)]
#[ensures(p as *const u8 == q as *const u8)]
pub fn congruent(p: *const [u8], q: *const [u8]) {}
