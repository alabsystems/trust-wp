//@ expect: verify
//@ xfail: price of the fix for raw_ptr_clause_cast_to_str_shadowed_by_block_alias.rs: a clause cast
//@ xfail: whose written target is `str` is refused, because the classifier reads the text and an
//@ xfail: item in scope may make `str` name a sized type. Reading it needs rustc's resolution.
//@ mechanism: twin of raw_ptr_clause_cast_to_str_shadowed_by_block_alias.rs without the alias:
//@ mechanism: `*const [u8] as *const str` keeps the address and the length, so the casts of two
//@ mechanism: different slice pointers are different, and the contract is true.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn outer() {
    #[requires(p1 != p2)]
    #[ensures((p1 as *const str) != (p2 as *const str))]
    pub fn thin_differs(p1: *const [u8], p2: *const [u8]) {
        let _ = (p1, p2);
    }

    let _ = thin_differs;
}
