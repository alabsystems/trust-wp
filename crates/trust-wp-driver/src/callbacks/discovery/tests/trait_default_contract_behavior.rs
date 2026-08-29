// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

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

/// Regression test for #2205: bodyless trait methods with contracts must NOT
/// appear in the verification contracts list. Their contracts are handled by
/// `find_trait_contracts` for call-site inheritance. Including them caused
/// `body_owned_by` ICEs when the pipeline tried to access non-existent MIR.
#[test]
fn find_contract_functions_excludes_bodyless_trait_method_with_contracts() {
    let source = r#"
pub trait Contracted {
    #[doc(hidden)]
    #[doc = "trust-wp:ensures:result == true"]
    fn bodyless_with_contract(&self) -> bool;

    #[doc(hidden)]
    #[doc = "trust-wp:ensures:result > 0"]
    fn bodyful_with_contract(&self) -> i32 {
        1
    }
}
"#;
    let probe = probe_trait_default_detection(source);
    assert!(
        !probe
            .discovered_assoc_methods
            .contains("bodyless_with_contract"),
        "bodyless trait method with contracts must be excluded (#2205): discovered={:?}",
        probe.discovered_assoc_methods
    );
    assert!(
        probe
            .discovered_assoc_methods
            .contains("bodyful_with_contract"),
        "bodyful trait method with contracts should still be discovered: discovered={:?}",
        probe.discovered_assoc_methods
    );
}
