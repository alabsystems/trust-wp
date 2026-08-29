// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_option_unwrap() {
    let spec = lookup_std_spec("core::option::Option::<i32>::unwrap").unwrap();
    assert!(
        spec.requires.iter().any(|r| r.contains("None")),
        "Option::unwrap requires must reference None: {:?}",
        spec.requires
    );
    assert!(
        spec.ensures.iter().any(|e| e.contains("Some(result)")),
        "Option::unwrap ensures must reference Some(result): {:?}",
        spec.ensures
    );
}
#[test]
fn test_lookup_unknown() {
    assert!(lookup_std_spec("some::unknown::Function").is_none());
}
#[test]
fn test_lookup_option_is_some() {
    let spec_core = lookup_std_spec("core::option::Option::is_some").unwrap();
    let spec_std = lookup_std_spec("std::option::Option::is_some").unwrap();
    assert!(spec_core.requires.is_empty());
    assert!(
        spec_core.ensures.iter().any(|e| e.contains("None")),
        "Option::is_some ensures must reference None: {:?}",
        spec_core.ensures
    );
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_option_unwrap_or() {
    let spec = lookup_std_spec("core::option::Option::<i32>::unwrap_or").unwrap();
    assert!(spec.requires.is_empty());
    assert!(
        spec.ensures.iter().any(|e| e.contains("match")),
        "Option::unwrap_or ensures must use match: {:?}",
        spec.ensures
    );
    assert!(
        spec.ensures.iter().any(|e| e.contains("default")),
        "Option::unwrap_or ensures must reference default: {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_option_is_none() {
    // Tests negation variant of is_some (#94)
    let spec_core = lookup_std_spec("core::option::Option::is_none").unwrap();
    let spec_std = lookup_std_spec("std::option::Option::is_none").unwrap();
    assert!(spec_core.requires.is_empty());
    assert!(spec_core.ensures.iter().any(|e| e.contains("None")));
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_option_map() {
    let spec = lookup_std_spec("core::option::Option::map").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Some(v) => result == Some(f(v))", "Option::map");
    assert_ensures_contains(&spec, "None => result == None", "Option::map");
}

#[test]
fn test_lookup_option_and_then() {
    let spec = lookup_std_spec("std::option::Option::and_then").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Some(v) => result == f(v)", "Option::and_then");
    assert_ensures_contains(&spec, "None => result == None", "Option::and_then");
}

#[test]
fn test_lookup_option_take() {
    let spec = lookup_std_spec("core::option::Option::take").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self) == None", "Option::take");
    assert_ensures_contains(&spec, "result == old(*self)", "Option::take");
}

#[test]
fn test_lookup_option_replace() {
    let spec = lookup_std_spec("std::option::Option::replace").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self) == Some(value)", "Option::replace");
    assert_ensures_contains(&spec, "result == old(*self)", "Option::replace");
}

#[test]
fn test_lookup_option_expect() {
    let spec_core = lookup_std_spec("core::option::Option::expect").unwrap();
    let spec_std = lookup_std_spec("std::option::Option::expect").unwrap();
    // Precondition: *self != None (distinguishes from unwrap_or_else which has no requires)
    assert!(spec_core.requires.iter().any(|r| r.contains("None")));
    // Postcondition: Some(result) == *self (distinguishes from Result::expect which uses Ok)
    assert!(spec_core.ensures.iter().any(|e| e.contains("Some(result)")));
    assert_eq!(spec_core.requires, spec_std.requires);
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_option_unwrap_or_else() {
    let spec_core = lookup_std_spec("core::option::Option::unwrap_or_else").unwrap();
    let spec_std = lookup_std_spec("std::option::Option::unwrap_or_else").unwrap();
    assert!(spec_core.requires.is_empty());
    // Implication-style: is_some => result == unwrap, is_none => result == f() (#1296)
    assert_eq!(spec_core.ensures.len(), 2);
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("self.unwrap()")));
    assert!(spec_core.ensures.iter().any(|e| e.contains("f()")));
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_option_as_ref() {
    let spec_core = lookup_std_spec("core::option::Option::as_ref").unwrap();
    let spec_std = lookup_std_spec("std::option::Option::as_ref").unwrap();
    assert!(spec_core.requires.is_empty());
    // Implication-style: preserves is_some/is_none status and inner value (#1296)
    assert_eq!(spec_core.ensures.len(), 3);
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_some()")));
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_none()")));
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_option_as_mut() {
    let spec_core = lookup_std_spec("core::option::Option::as_mut").unwrap();
    let spec_std = lookup_std_spec("std::option::Option::as_mut").unwrap();
    assert!(spec_core.requires.is_empty());
    // Implication-style: preserves is_some/is_none status and inner value (#1296)
    assert_eq!(spec_core.ensures.len(), 3);
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_some()")));
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_none()")));
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_option_ok_or() {
    let spec_core = lookup_std_spec("core::option::Option::ok_or").unwrap();
    let spec_std = lookup_std_spec("std::option::Option::ok_or").unwrap();
    assert!(spec_core.requires.is_empty());
    // Implication-style postconditions with tester/selector methods (#2675)
    assert_ensures_contains(&spec_core, "result.is_ok()", "Option::ok_or");
    assert_ensures_contains(&spec_core, "result.unwrap_err() == err", "Option::ok_or");
    assert_eq!(spec_core.ensures, spec_std.ensures);
    // param_names must be parsed from `params: self, err` line
    assert_eq!(
        spec_core.param_names.as_deref(),
        Some(["self", "err"].map(String::from).as_slice()),
        "ok_or spec must provide param_names for positional-to-named substitution"
    );
}
