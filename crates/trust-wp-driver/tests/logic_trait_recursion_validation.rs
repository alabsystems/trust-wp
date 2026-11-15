// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for logic trait-recursion validation (the Creusot
//! impl_arg and terminates-trio cases, each a false accept without it).
//!
//! Two lanes close the four holes:
//! - the illegal-recursive-trait bound check (Creusot
//!   validate/recursive_types.rs `add_trait`): a logic method of a trait whose
//!   bound graph cycles back to itself is rejected at the definition
//!   (impl_arg, trait_where, trait_where_supertrait);
//! - self-named self-dispatch threading in the termination callgraph:
//!   `self.f()` inside the logic fn named `f` is an identity self-call the
//!   walker must see even though the short name is ambiguous between the
//!   trait declaration and the impl (trait_impl_where).
//!
//! The should_pass_* fixtures prove legitimate trait-bounded logic functions
//! (Sized bounds, impl-Trait arguments on free fns, same-named field
//! dispatch) are not over-rejected.

use std::{
    fs,
    path::Path,
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time should be after unix epoch")
        .as_nanos();
    let target_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/logic_trait_recursion_tests")
        .join(format!("{bin}-{}-{unique}", std::process::id()));
    let output = nested_cargo("check")
        .current_dir(fixture_dir("logic_trait_recursion"))
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for logic trait recursion fixture");
    let _ = fs::remove_dir_all(&target_dir);
    output
}

fn assert_rejected_with(bin: &str, expected_fragments: &[&str]) {
    let output = run_fixture(bin);
    assert!(
        !output.status.success(),
        "expected {bin} to be rejected; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("logic recursion check failed"),
        "missing logic-recursion rejection channel for {bin}; stderr: {stderr}",
    );
    for fragment in expected_fragments {
        assert!(
            stderr.contains(fragment),
            "missing `{fragment}` in {bin} rejection; stderr: {stderr}",
        );
    }
}

fn assert_accepted(bin: &str) {
    let output = run_fixture(bin);
    assert!(
        output.status.success(),
        "expected {bin} to compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// RED (creusot recursive_types/impl_arg.rs): `Q` is a bound of `Q::f` via
/// the `x: impl Q` argument — an illegal recursive trait.
#[test]
#[timeout(120_000)]
fn logic_trait_recursion_rejects_impl_arg_dispatch() {
    assert_rejected_with(
        "should_fail_impl_arg",
        &[
            "illegal recursive trait",
            "`Q` is recursive through its bounds",
        ],
    );
}

/// RED (creusot terminates/trait_where.rs): `Tr` is a bound of `Tr::f` via
/// `where Self: Tr<Self>` — an illegal recursive trait.
#[test]
#[timeout(120_000)]
fn logic_trait_recursion_rejects_trait_where_bound() {
    assert_rejected_with(
        "should_fail_trait_where",
        &[
            "illegal recursive trait",
            "`Tr` is recursive through its bounds",
        ],
    );
}

/// RED (creusot terminates/trait_where_supertrait.rs): `P` is a bound of
/// `Q::f` and `Q` is a supertrait of `P` — the cycle closes through the
/// supertrait edge.
#[test]
#[timeout(120_000)]
fn logic_trait_recursion_rejects_supertrait_bound_cycle() {
    assert_rejected_with(
        "should_fail_trait_where_supertrait",
        &[
            "illegal recursive trait",
            "`Q` is recursive through its bounds",
        ],
    );
}

/// RED (creusot terminates/trait_impl_where.rs): the trait is fine; the impl
/// method's `self.f()` is an identity self-call the callgraph must thread
/// despite the ambiguous short name.
#[test]
#[timeout(120_000)]
fn logic_trait_recursion_rejects_impl_where_identity_self_call() {
    assert_rejected_with(
        "should_fail_trait_impl_where",
        &["unconditional self-recursion without #[variant(...)]"],
    );
}

/// GREEN: `where Self: Sized` on a logic trait method is not a cycle.
#[test]
#[timeout(120_000)]
fn logic_trait_recursion_allows_sized_bound() {
    assert_accepted("should_pass_sized_bound");
}

/// GREEN: `impl Trait` argument on a FREE logic fn is not a trait-bound cycle.
#[test]
#[timeout(120_000)]
fn logic_trait_recursion_allows_trait_bounded_free_fn_arg() {
    assert_accepted("should_pass_trait_bounded_arg");
}

/// GREEN: same-named dispatch through a FIELD receiver (View/DeepModel-style
/// structural descent) must not be flagged as self-dispatch.
#[test]
#[timeout(120_000)]
fn logic_trait_recursion_allows_same_named_field_dispatch() {
    assert_accepted("should_pass_field_dispatch");
}
