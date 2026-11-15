// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the standalone trait refinement pass (WP-07).
//!
//! The adversarial fixtures are impls whose contract does not refine their
//! trait method's contract; each must be rejected with a refinement verdict,
//! never accepted silently.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(format!(
        "../../target/trait_refinement_fail_open_tests_verify_{bin}"
    ));
    nested_cargo("check")
        .current_dir(fixture_dir("trait_refinement_fail_open"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        // Hermetic: verify only the fixture crate, never its dependencies.
        .env("CARGO_TRUST_WP", "1")
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for trait refinement fixture")
}

/// `impl_path` scopes the assertions to the fixture's impl: dependency crates
/// (trust-wp-std) are verified in the same `cargo check` and print their own
/// refinement verdicts.
fn assert_rejected_by_refinement(bin: &str, impl_path: &str, check: &str) {
    let output = run_fixture(bin);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "{bin}: a non-refining impl must be rejected; stderr: {stderr}"
    );
    assert!(
        stderr.contains(&format!("trust-wp: {impl_path} trait refinement FAILED")),
        "{bin}: missing refinement verdict for {impl_path}; stderr: {stderr}"
    );
    assert!(
        stderr.contains(check),
        "{bin}: refinement must fail on `{check}`; stderr: {stderr}"
    );
    assert!(
        !stderr.contains(&format!("trust-wp: {impl_path} refinement verified")),
        "{bin}: must not credit the refinement of {impl_path}; stderr: {stderr}"
    );
}

#[test]
#[timeout(300_000)]
fn contractless_trait_method_impl_requires_is_rejected() {
    assert_rejected_by_refinement(
        "should_fail_contractless_trait_requires",
        "<S as Tr>::m",
        "trait precondition implies impl precondition",
    );
}

#[test]
#[timeout(300_000)]
fn weaker_impl_ensures_is_rejected() {
    assert_rejected_by_refinement(
        "should_fail_weaker_ensures",
        "<S as Tr>::m",
        "impl postcondition implies trait postcondition",
    );
}

#[test]
#[timeout(300_000)]
fn external_trait_impl_requires_is_rejected() {
    assert_rejected_by_refinement(
        "should_fail_external_trait_requires",
        "<S as std::clone::Clone>::clone",
        "trait precondition implies impl precondition",
    );
}

#[test]
#[timeout(300_000)]
fn refining_impls_verify() {
    let output = run_fixture("should_pass_refinements");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "refining impls must verify; stderr: {stderr}"
    );
    for path in ["<A as Same>::m", "<B as Refine>::m", "<C as Open>::m"] {
        assert!(
            stderr.contains(&format!("trust-wp: {path} refinement verified")),
            "missing refinement verdict for {path}; stderr: {stderr}"
        );
    }
}

#[test]
#[timeout(300_000)]
fn binder_capture_on_contractless_trait_is_rejected() {
    assert_rejected_by_refinement(
        "should_fail_binder_capture_contractless",
        "<S as Tr>::m",
        "trait precondition implies impl precondition",
    );
}

#[test]
#[timeout(300_000)]
fn binder_capture_on_declared_trait_contract_is_rejected() {
    assert_rejected_by_refinement(
        "should_fail_binder_capture_declared",
        "<S as Tr>::m",
        "trait precondition implies impl precondition",
    );
}

/// Refuse (error, no credit) a refinement whose clauses name something the
/// clause text alone cannot resolve: the trait's and the impl's clause are
/// written in different scopes and may denote different items.
fn assert_refused_scope_dependent(bin: &str, name: &str) {
    assert_refinement_refused(bin, &format!("names {name}, which cannot be resolved"));
}

/// The refinement of `<i::S as t::Tr>::m` is refused with `refusal` in its
/// report, the crate is rejected, and the impl is credited nothing.
fn assert_refinement_refused(bin: &str, refusal: &str) {
    let impl_path = "<i::S as t::Tr>::m";
    let output = run_fixture(bin);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "{bin}: scope-dependent refinement must not pass; stderr: {stderr}"
    );
    assert!(
        stderr.contains(&format!("trust-wp: {impl_path} trait refinement error: ")),
        "{bin}: missing refinement refusal; stderr: {stderr}"
    );
    assert!(
        stderr.contains(refusal),
        "{bin}: refusal must say `{refusal}`; stderr: {stderr}"
    );
    assert!(
        !stderr.contains(&format!("trust-wp: {impl_path} refinement verified")),
        "{bin}: must not credit the refinement; stderr: {stderr}"
    );
}

#[test]
#[timeout(300_000)]
fn logic_fn_name_resolved_in_different_scopes_is_refused() {
    assert_refused_scope_dependent("should_fail_logic_fn_scope", "call `k(..)`");
}

/// Refuse (error, no credit) a crate whose clause calls a logic function by
/// a name other than the one rustc resolved it to (D-136 item 5). The
/// refusal comes before discovery, so no refinement is examined: the
/// scope-dependent refinement refusal above is never reached, and nothing in
/// the crate is credited.
fn assert_refused_as_misread_spec_call(bin: &str, spelled_as: &[(&str, &str)]) {
    let output = run_fixture(bin);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "{bin}: a clause calling an aliased logic fn must not pass; stderr: {stderr}"
    );
    for (spelled, resolved) in spelled_as {
        assert!(
            stderr.contains(&format!(
                "a call spelled `{spelled}` in a specification that rustc resolves to `{resolved}`"
            )),
            "{bin}: missing the refusal of `{spelled}` read as `{resolved}`; stderr: {stderr}"
        );
    }
    for item in ["<i::S as t::Tr>::m refinement verified", "through verified"] {
        assert!(
            !stderr.contains(&format!("trust-wp: {item}")),
            "{bin}: a refused crate credits nothing; stderr: {stderr}"
        );
    }
}

#[test]
#[timeout(300_000)]
fn logic_fn_import_alias_is_refused() {
    assert_refused_as_misread_spec_call("should_fail_logic_fn_import_alias", &[("k", "a::z")]);
}

#[test]
#[timeout(300_000)]
fn logic_fn_alias_on_both_sides_is_refused() {
    assert_refused_as_misread_spec_call(
        "should_fail_logic_fn_alias_both",
        &[("j", "a::k"), ("j", "b::k")],
    );
}

#[test]
#[timeout(300_000)]
fn constant_resolved_in_different_scopes_is_refused() {
    assert_refused_scope_dependent("should_fail_const_scope", "identifier `K`");
}

#[test]
#[timeout(300_000)]
fn constant_scope_with_trait_caller_is_refused() {
    assert_refused_scope_dependent("should_fail_const_scope_caller", "identifier `K`");
}

#[test]
#[timeout(300_000)]
fn alias_binder_annotation_is_refused() {
    // D-205: `Wd` is an alias of a machine integer, so every clause of the
    // crate that spells it as a type is refused where it is parsed, before
    // the refinement's scope check reads it.
    assert_refinement_refused(
        "should_fail_alias_binder",
        "spells `Wd`, which this crate binds to a type holding a machine integer",
    );
}

#[test]
#[timeout(300_000)]
fn tuple_binder_annotation_is_refused() {
    // D-205, as for `alias_binder_annotation_is_refused`: the tuple holds `Wd`.
    assert_refinement_refused(
        "should_fail_tuple_binder",
        "spells `Wd`, which this crate binds to a type holding a machine integer",
    );
}

#[test]
#[timeout(300_000)]
fn erased_primitive_cast_is_refused() {
    assert_refused_scope_dependent("should_fail_cast_erased", "cast `as u8`");
}

#[test]
#[timeout(300_000)]
fn erased_literal_suffix_is_refused() {
    assert_refused_scope_dependent("should_fail_literal_suffix", "literal type suffix `u8`");
}

/// A cast whose target is an alias of a machine integer is refused where the
/// clause is parsed (D-205), before any scope check.
#[test]
#[timeout(300_000)]
fn alias_cast_is_refused() {
    assert_refinement_refused(
        "should_fail_alias_cast",
        "spells `Wd`, which this crate binds to a type holding a machine integer",
    );
}

#[test]
#[timeout(300_000)]
fn shadowed_int_binder_is_refused() {
    // D-202: a crate that gives `Int` another meaning anywhere loses every
    // clause that spells it as a type, so the clause is refused where it is
    // parsed, before the refinement's scope check reads it.
    assert_refinement_refused(
        "should_fail_shadowed_int_binder",
        "`Int` spells `Int`, which this crate declares or imports with another meaning",
    );
}

#[test]
#[timeout(300_000)]
fn renamed_parameter_refinements_verify() {
    let output = run_fixture("should_pass_renamed_refinements");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "refining impls with renamed parameters must verify; stderr: {stderr}"
    );
    for path in [
        "<A as Same>::m",
        "<B as Refine>::m",
        "<C as Quant>::m",
        "<D as Swap>::m",
    ] {
        assert!(
            stderr.contains(&format!("trust-wp: {path} refinement verified")),
            "missing refinement verdict for {path}; stderr: {stderr}"
        );
    }
}

#[test]
#[timeout(300_000)]
fn underscore_parameter_name_collision_on_declared_trait_is_rejected() {
    assert_rejected_by_refinement(
        "should_fail_underscore_arg_collision_declared",
        "<S as Tr>::m",
        "impl postcondition implies trait postcondition",
    );
}

#[test]
#[timeout(300_000)]
fn underscore_parameter_name_collision_on_contractless_trait_is_rejected() {
    assert_rejected_by_refinement(
        "should_fail_underscore_arg_collision",
        "<S as Tr>::m",
        "trait precondition implies impl precondition",
    );
}

/// Refuse (error, no credit) a refinement whose parameters cannot be matched
/// one-to-one by position.
fn assert_refused_param_naming(bin: &str, reason: &str) {
    let impl_path = "<S as Tr>::m";
    let output = run_fixture(bin);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "{bin}: must not pass; stderr: {stderr}"
    );
    assert!(
        stderr.contains(&format!(
            "trust-wp: {impl_path} trait refinement error: parameters cannot be matched by \
             position: {reason}"
        )),
        "{bin}: missing parameter-naming refusal `{reason}`; stderr: {stderr}"
    );
    assert!(
        !stderr.contains(&format!("trust-wp: {impl_path} refinement verified")),
        "{bin}: must not credit the refinement; stderr: {stderr}"
    );
}

#[test]
#[timeout(300_000)]
fn trait_parameter_named_result_is_refused() {
    assert_refused_param_naming(
        "should_fail_trait_param_named_result",
        "trait parameter `result` conflicts with the reserved `result` identifier",
    );
}

#[test]
#[timeout(300_000)]
fn impl_parameter_named_result_is_refused() {
    assert_refused_param_naming(
        "should_fail_impl_param_named_result",
        "impl parameter `result` conflicts with the reserved `result` identifier",
    );
}

#[test]
#[timeout(300_000)]
fn call_site_binding_of_colliding_underscore_name_is_rejected() {
    let output = run_fixture("should_fail_call_site_arg_collision");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "`through` returns 1, never 2, and must be rejected; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: through FAILED"),
        "missing failure verdict for `through`; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("trust-wp: through verified"),
        "must not credit `through`; stderr: {stderr}"
    );
}

#[test]
#[timeout(300_000)]
fn positional_parameter_refinements_verify() {
    let output = run_fixture("should_pass_positional_refinements");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "refining impls must verify under positional renaming; stderr: {stderr}"
    );
    for path in ["<U as Under>::m", "<R as Recv>::m", "<X as Cross>::m"] {
        assert!(
            stderr.contains(&format!("trust-wp: {path} refinement verified")),
            "missing refinement verdict for {path}; stderr: {stderr}"
        );
    }
}
