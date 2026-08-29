// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn is_bodyful_trait_method_distinguishes_provided_vs_bodyless_defaults() {
    let probe = probe_trait_default_detection(trait_default_fixture_source());

    assert_eq!(
        probe.with_body_is_bodyful,
        Some(true),
        "provided trait default method must be bodyful"
    );
    assert_eq!(
        probe.without_body_is_bodyful,
        Some(false),
        "bodyless trait method declaration must not be bodyful"
    );
}

#[test]
fn find_contract_functions_includes_only_bodyful_trait_default_method() {
    let probe = probe_trait_default_detection(trait_default_fixture_source());
    let has_with_body = probe.discovered_assoc_methods.contains("with_body");
    let has_without_body = probe.discovered_assoc_methods.contains("without_body");

    assert!(
        has_with_body,
        "bodyful trait default method should be discovered for verification: discovered={:?}",
        probe.discovered_assoc_methods
    );
    assert!(
        !has_without_body,
        "bodyless trait declaration should not be discovered without contracts: discovered={:?}",
        probe.discovered_assoc_methods
    );
}
