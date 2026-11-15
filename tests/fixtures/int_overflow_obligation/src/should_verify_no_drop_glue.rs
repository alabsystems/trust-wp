// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twin of should_fail_dropper: a local without drop glue.

struct NoDrop(u8);

pub fn no_drop_glue(x: u8) -> u8 {
    let d = NoDrop(x);
    d.0 / 1
}

fn main() {}
