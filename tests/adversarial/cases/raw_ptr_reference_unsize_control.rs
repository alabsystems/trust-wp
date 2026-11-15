//@ expect: verify
//@ mechanism: control for raw_ptr_unsize_array_lengths_read_as_identity: a reference's unsizing keeps
//@ mechanism: its value (the value model), so the raw-pointer reading does not reach `&[T; N]` to
//@ mechanism: `&[T]`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == a@)]
pub fn as_slice(a: &[u8; 4]) -> &[u8] {
    a
}
