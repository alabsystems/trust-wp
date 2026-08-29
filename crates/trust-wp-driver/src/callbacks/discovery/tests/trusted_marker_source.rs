// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn trusted_attr_source_detects_plain_marker() {
    let src = r#"#[trusted] fn f() {}"#;
    assert!(has_attr_without_args_from_source(src, "trusted"));
}

#[test]
fn trusted_attr_source_detects_qualified_marker() {
    let src = r#"#[trust_wp::trusted] fn f() {}"#;
    assert!(has_attr_without_args_from_source(src, "trusted"));
}

#[test]
fn trusted_attr_source_rejects_argumented_form() {
    let src = r#"#[trusted(extra)] fn f() {}"#;
    assert!(!has_attr_without_args_from_source(src, "trusted"));
}

#[test]
fn trusted_attr_source_ignores_comment_mentions() {
    let src = "/// docs mention #[trusted]\nfn f() {}";
    assert!(!has_attr_without_args_from_source(src, "trusted"));
}

#[test]
fn trusted_attr_source_ignores_non_header_mentions() {
    let src = "fn f() { let _s = \"#[trusted]\"; }";
    assert!(!has_attr_without_args_from_source(src, "trusted"));
}

#[test]
fn trusted_doc_marker_source_detects_header_marker() {
    let src = r#"#[doc(hidden)] #[doc = "trust-wp:trusted:"] fn f() {}"#;
    assert!(has_doc_marker_in_header_source(src, "trust-wp:trusted:"));
}

#[test]
fn trusted_doc_marker_source_ignores_body_mentions() {
    let src = r#"fn f() { let _s = "trust-wp:trusted:"; }"#;
    assert!(!has_doc_marker_in_header_source(src, "trust-wp:trusted:"));
}
