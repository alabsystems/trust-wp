//@ expect: verify
//@ mechanism: control for D-142 — the should_succeed row match_int's shape: a literal scrutinee
//@ mechanism: selects the `0..10` arm, the range tests on it are literal, and the `assert!(false)`
//@ mechanism: arms sit behind the edges those literals never select.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unreachable_patterns)]

extern crate creusot_std;

pub fn hop() {
    match 1 {
        0..10 => assert!(true),
        5 | 6 => assert!(false),
        _ => assert!(false),
    }
}
