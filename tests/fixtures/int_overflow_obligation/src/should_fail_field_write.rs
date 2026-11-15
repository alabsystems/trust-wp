// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED (projected write): a field written after the aggregate was built must
//! be read at its written value, never the aggregate's initial field.

use trust_wp::ensures;

#[ensures(true)]
pub fn through_field(y: u8) -> u8 {
    let mut s: (u8, u8) = (0, 0);
    s.0 = y;
    s.0 + 1
}

fn main() {}
