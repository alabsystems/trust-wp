// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(proc_macro_hygiene)]
#![allow(unexpected_cfgs)]

//! Regression fixture for #1180.
//!
//! Exercises proof_assert verification where:
//! - preconditions contain `exists<...> postcondition_mut(...)` assumptions
//! - call obligations contain `forall<...> postcondition_mut(...) ==> precondition(...)`
//!
//! Quantifiers are introduced via contract attributes (supported by trust-wp's
//! contract parser), while the proof_assert itself stays a Rust expression.

use trust_wp::{ensures, proof_assert, requires, trusted};

#[trusted]
#[requires((*f).precondition(arg))]
#[ensures(exists<st, r> (*f).postcondition_mut(arg, st, r))]
fn call_with_existential<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) {
    let _ = f(arg);
}

#[requires(forall<st, r> (*f).postcondition_mut(arg, st, r) ==> st.precondition(arg))]
fn require_forall_obligation<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) {
    let _ = f;
    let _ = arg;
}

#[requires(seed > 0)]
fn proof_assert_closure_quantifier_enrichment(seed: i32) {
    let base = seed;
    // The closure captures `base` and carries a contract; its body must be
    // total on its own precondition (every arithmetic obligation is checked),
    // so it selects rather than adds — `arg + base` overflows `i32` for
    // `arg == i32::MAX`, which `arg > 0` admits.
    let mut closure = {
        #[requires(arg > 0)]
        #[ensures(result >= arg && result >= base)]
        |arg: i32| -> i32 {
            if arg > base {
                arg
            } else {
                base
            }
        }
    };

    call_with_existential(&mut closure, 2);
    require_forall_obligation(&mut closure, 2);
    proof_assert!(true);
}

fn main() {
    proof_assert_closure_quantifier_enrichment(40);
}
