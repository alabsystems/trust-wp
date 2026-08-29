// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn find_contract_functions_marks_doc_trusted_trait_default_trusted() {
    let probe = probe_trait_default_detection(trait_default_with_doc_trusted_fixture_source());
    assert!(
        probe.discovered_assoc_methods.contains("trusted_default"),
        "trusted default method should be discovered"
    );
    assert!(
        probe.trusted_assoc_methods.contains("trusted_default"),
        "doc-trusted marker should set contract.trusted for trait defaults"
    );
}

#[test]
fn get_all_attrs_preserves_proc_macro_trusted_marker_on_trait_defaults() {
    let probe = probe_trait_default_detection_with_args(
        trait_default_with_macro_trusted_fixture_source(),
        &proc_macro_probe_args(),
    );
    let attr_values = probe
        .assoc_method_attr_values
        .get("trusted_default")
        .expect("trusted_default should expose proc-macro attrs via rustc");
    assert!(
        attr_values
            .iter()
            .any(|value| value.starts_with("trust-wp:trusted:")),
        "tcx.get_all_attrs() should preserve the proc-macro trusted marker: {attr_values:?}"
    );
}

#[test]
fn find_contract_functions_marks_proc_macro_trusted_trait_default_trusted() {
    let probe = probe_trait_default_detection_with_args(
        trait_default_with_macro_trusted_fixture_source(),
        &proc_macro_probe_args(),
    );
    assert!(
        probe.discovered_assoc_methods.contains("trusted_default"),
        "trusted default method should be discovered"
    );
    assert!(
        probe.trusted_assoc_methods.contains("trusted_default"),
        "proc-macro trusted marker should set contract.trusted for trait defaults"
    );
}

#[test]
fn find_contract_functions_ignores_trusted_proof_assert_closure_marker() {
    let probe = probe_contract_discovery_with_args(
        trusted_proof_assert_fixture_source(),
        &trust_wp_probe_args(),
    );
    assert!(
        probe
            .discovered_paths
            .iter()
            .any(|path| path.ends_with("assume")),
        "containing function should still be discovered: {:?}",
        probe.discovered_paths
    );
    assert!(
        !probe
            .discovered_paths
            .iter()
            .any(|path| path.contains("assume::{closure#")),
        "trusted proof_assert closure should not be discovered as a contract item: {:?}",
        probe.discovered_paths
    );
}

#[test]
fn find_contract_functions_ignores_inactive_cfg_attr_trusted_marker() {
    let probe =
        probe_trait_default_detection(trait_default_with_inactive_cfg_attr_fixture_source());
    assert!(
        probe.discovered_assoc_methods.contains("maybe_trusted"),
        "bodyful trait default should still be discovered"
    );
    assert!(
        !probe.trusted_assoc_methods.contains("maybe_trusted"),
        "inactive cfg_attr must not mark trait defaults trusted"
    );
}

#[test]
fn get_all_attrs_exposes_inner_doc_marker_on_trait_default_body() {
    let probe = probe_trait_default_detection(trait_default_with_inner_doc_marker_fixture_source());
    let attr_values = probe
        .assoc_method_attr_values
        .get("maybe_trusted")
        .expect("inner-doc fixture should expose attrs via rustc");
    assert!(
        attr_values
            .iter()
            .any(|value| value.starts_with("trust-wp:trusted:")),
        "tcx.get_all_attrs() should surface the inner doc marker: {attr_values:?}"
    );
}

#[test]
fn find_contract_functions_ignores_inner_doc_trusted_marker() {
    let probe = probe_trait_default_detection(trait_default_with_inner_doc_marker_fixture_source());
    assert!(
        probe.discovered_assoc_methods.contains("maybe_trusted"),
        "bodyful trait default should still be discovered"
    );
    assert!(
        !probe.trusted_assoc_methods.contains("maybe_trusted"),
        "inner doc markers must not mark trait defaults trusted"
    );
}

#[test]
fn find_contract_functions_ignores_doc_text_trusted_mentions() {
    let probe = probe_trait_default_detection(trait_default_with_doc_text_mention_fixture_source());
    assert!(
        probe.discovered_assoc_methods.contains("maybe_trusted"),
        "bodyful trait default should still be discovered"
    );
    assert!(
        !probe.trusted_assoc_methods.contains("maybe_trusted"),
        "doc strings mentioning #[trusted] must not mark trait defaults trusted"
    );
}
