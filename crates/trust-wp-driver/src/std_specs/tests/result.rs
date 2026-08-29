// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_result_is_ok() {
    let spec = lookup_std_spec("core::result::Result::<T, E>::is_ok").unwrap();
    assert!(spec.requires.is_empty());
    assert!(
        spec.ensures.iter().any(|e| e.contains("Ok")),
        "Result::is_ok ensures must reference Ok: {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_result_unwrap_requires() {
    let spec = lookup_std_spec("core::result::Result::<T, E>::unwrap").unwrap();
    assert!(
        spec.requires.iter().any(|r| r.contains("Ok")),
        "Result::unwrap requires must reference Ok: {:?}",
        spec.requires
    );
    assert!(
        spec.ensures.iter().any(|e| e.contains("Ok(result)")),
        "Result::unwrap ensures must reference Ok(result): {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_result_is_err() {
    // Tests negation variant of is_ok (#94)
    let spec_core = lookup_std_spec("core::result::Result::is_err").unwrap();
    let spec_std = lookup_std_spec("std::result::Result::is_err").unwrap();
    assert!(spec_core.requires.is_empty());
    assert_ensures_contains(&spec_core, "Err(_) => true", "Result::is_err");
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_result_unwrap_err() {
    // Tests error extraction variant of unwrap (#94)
    let spec = lookup_std_spec("core::result::Result::<T, E>::unwrap_err").unwrap();
    assert_requires_contains(&spec, "Err(_) => true", "Result::unwrap_err");
    assert_ensures_contains(&spec, "Err(result) == *self", "Result::unwrap_err");
}

#[test]
fn test_lookup_result_unwrap_or() {
    let spec = lookup_std_spec("core::result::Result::unwrap_or").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Err(_) => result == default", "Result::unwrap_or");
}

#[test]
fn test_lookup_result_map() {
    let spec = lookup_std_spec("core::result::Result::map").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Ok(v) => result == Ok(f(v))", "Result::map");
}

#[test]
fn test_lookup_result_map_err() {
    let spec = lookup_std_spec("std::result::Result::map_err").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Err(e) => result == Err(f(e))", "Result::map_err");
}

#[test]
fn test_lookup_result_and_then() {
    let spec = lookup_std_spec("core::result::Result::and_then").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Ok(v) => result == f(v)", "Result::and_then");
    assert_ensures_contains(&spec, "Err(e) => result == Err(e)", "Result::and_then");
}

#[test]
fn test_lookup_result_ok() {
    let spec = lookup_std_spec("std::result::Result::ok").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Ok(v) => result == Some(v)", "Result::ok");
}

#[test]
fn test_lookup_result_err() {
    let spec = lookup_std_spec("core::result::Result::err").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Err(e) => result == Some(e)", "Result::err");
}

#[test]
fn test_lookup_result_expect() {
    let spec_core = lookup_std_spec("core::result::Result::expect").unwrap();
    let spec_std = lookup_std_spec("std::result::Result::expect").unwrap();
    // Precondition: match *self { Ok(_) => true, ... } (distinguishes from Option::expect's None check)
    assert!(spec_core.requires.iter().any(|r| r.contains("Ok(")));
    // Postcondition: Ok(result) == *self (distinguishes from Option::expect's Some)
    assert!(spec_core.ensures.iter().any(|e| e.contains("Ok(result)")));
    assert_eq!(spec_core.requires, spec_std.requires);
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_result_unwrap_or_else() {
    let spec_core = lookup_std_spec("core::result::Result::unwrap_or_else").unwrap();
    let spec_std = lookup_std_spec("std::result::Result::unwrap_or_else").unwrap();
    assert!(spec_core.requires.is_empty());
    // Distinguishing: Ok(v) and Err(e) => f(e) (not Option's Some/None or as_ref's Ok(v))
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("Ok(v) => result == v")));
    assert!(spec_core.ensures.iter().any(|e| e.contains("f(e)")));
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_result_as_ref() {
    let spec_core = lookup_std_spec("core::result::Result::as_ref").unwrap();
    let spec_std = lookup_std_spec("std::result::Result::as_ref").unwrap();
    assert!(spec_core.requires.is_empty());
    // Implication-style: preserves is_ok/is_err status and inner values (#1296)
    assert_eq!(spec_core.ensures.len(), 4);
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_ok()")));
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_err()")));
    assert_eq!(spec_core.ensures, spec_std.ensures);
}

#[test]
fn test_lookup_result_as_mut() {
    let spec_core = lookup_std_spec("core::result::Result::as_mut").unwrap();
    let spec_std = lookup_std_spec("std::result::Result::as_mut").unwrap();
    assert!(spec_core.requires.is_empty());
    // Implication-style: preserves is_ok/is_err status and inner values (#1296)
    assert_eq!(spec_core.ensures.len(), 4);
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_ok()")));
    assert!(spec_core
        .ensures
        .iter()
        .any(|e| e.contains("result.is_err()")));
    assert_eq!(spec_core.ensures, spec_std.ensures);
}
