//@ expect: verify
//@ mechanism: control for raw_ptr_clause_sized_to_fat_cast_read_as_identity: between two fat pointees
//@ mechanism: (`str` to `[u8]`) the length is kept, so the body's cast and the clause's are the
//@ mechanism: identity, read by one classifier.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == p as *const [u8])]
pub fn bytes(p: *const str) -> *const [u8] {
    p as *const [u8]
}
