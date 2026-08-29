// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::lookup_std_spec;

#[test]
fn lookup_option_ok_or_else_spec_present_for_core_and_std() {
    let spec_core = lookup_std_spec("core::option::Option::ok_or_else")
        .expect("invariant: core::option::Option::ok_or_else spec must exist");
    let spec_std = lookup_std_spec("std::option::Option::ok_or_else")
        .expect("invariant: std::option::Option::ok_or_else spec must exist");

    assert!(spec_core.requires.is_empty());
    // Implication-style postconditions with tester/selector methods (#2675)
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_ok()")));
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.unwrap_err() == err()")));
    assert_eq!(spec_core.ensures, spec_std.ensures);
}
