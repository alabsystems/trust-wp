// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `snapshot!` should accept block-level syntax with
//! `let` bindings and semicolons, not just single expressions (#1331).
#![allow(unexpected_cfgs)]

use trust_wp_macros::snapshot;

extern crate self as trust_wp_std;

pub mod ghost {
    use core::marker::PhantomData;

    pub struct Snapshot<T: ?Sized>(PhantomData<T>);

    impl<T: ?Sized> Copy for Snapshot<T> {}
    impl<T: ?Sized> Clone for Snapshot<T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T> Snapshot<T> {
        pub fn capture(_value: &T) -> Self {
            Snapshot(PhantomData)
        }

        pub fn new_phantom() -> Self {
            Snapshot(PhantomData)
        }
    }
}

/// Single expression — should still work as before.
fn snapshot_single_expr() {
    let x = 42i32;
    let _s: trust_wp_std::ghost::Snapshot<i32> = snapshot!(x);
}

/// Block with let binding and tail expression (#1331: 03_as_slice_of_cells.rs).
fn snapshot_let_binding() {
    let _s: trust_wp_std::ghost::Snapshot<i32> = snapshot! {
        let a = 1i32;
        a + 1
    };
}

/// Block with semicolon-terminated statement (#1331: 12_ghost_code.rs).
fn snapshot_statement_with_semicolon() {
    fn do_nothing(_x: i32) {}
    let _s: trust_wp_std::ghost::Snapshot<()> = snapshot! {
        do_nothing(42);
    };
}

/// Unit-returning blocks should still type-check when the snapshot result is
/// used as a bare statement with no type context (#2499).
fn snapshot_statement_without_type_context() {
    fn logi_drop<T>(_x: T) {}
    let mut x = Vec::<u32>::new();
    snapshot! {
        logi_drop(x);
    };
    x.push(1);
}

/// Unit-returning blocks may mention verifier-only names; non-trust-wp builds
/// must compile by erasing the block body. (#2299)
fn snapshot_statement_with_spec_only_name() {
    let _s: trust_wp_std::ghost::Snapshot<()> = snapshot! {
        let _ = such_that(|x: i32| x == 0);
    };
}

fn main() {
    snapshot_single_expr();
    snapshot_let_binding();
    snapshot_statement_with_semicolon();
    snapshot_statement_without_type_context();
    snapshot_statement_with_spec_only_name();
}
