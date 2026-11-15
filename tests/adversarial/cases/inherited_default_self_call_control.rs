//@ expect: verify
//@ mechanism: `Self::f()` inside `impl Foo for ()`, which does not define `f`: Rust selects the trait's default body at `()`, and a default that calls nothing is that body at every `Self`, so the call is the declaration's definition (termination/call_in_contract.rs's shape, with a value that can be wrong)
//@ teeth: over-refusal control — measured `logic function call `Self::f` names one of several definitions` and a scope-dependent refinement error before the inherited-default rule; `<() as Foo>::get verified ✓` at exit 0 after it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic(open)]
    fn f() -> Int {
        1
    }
    fn get(&self) -> i32;
}

impl Foo for () {
    #[ensures(result@ == Self::f())]
    fn get(&self) -> i32 {
        1
    }
}
