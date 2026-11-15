// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twin of closure_add: the closure body's own `x + 1` is guarded by
//! `x < 200`, so its arithmetic goal is proved on the closure's own body. The
//! enclosing fn is contract-free and does no arithmetic itself, so the
//! closure body is the only target.
//!
//! (Closure parameters carry no machine-int range fact yet, so an unguarded
//! `x / 2 + 1` is still rejected: a completeness gap, never an accept.)

pub fn closure_guarded_ok() -> u8 {
    let f = |x: u8| if x < 200 { x + 1 } else { x };
    f(255)
}

fn main() {}
