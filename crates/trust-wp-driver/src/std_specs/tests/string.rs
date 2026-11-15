// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_string_new() {
    let spec = lookup_std_spec("alloc::string::String::new").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@.len() == 0", "String::new");
}

#[test]
fn test_lookup_string_len() {
    let spec = lookup_std_spec("std::string::String::len").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self@.len()", "String::len");
    assert_ensures_contains(
        &spec,
        "self@.index_logic(0).to_utf8().len()",
        "String::len singleton UTF-8 byte length",
    );
    assert!(
        spec.ensures.iter().all(|e| parse_spec(e).is_some()),
        "String::len ensures should parse: {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_string_is_empty() {
    let spec = lookup_std_spec("alloc::string::String::is_empty").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == (self.len() == 0)", "String::is_empty");
}

#[test]
fn test_lookup_string_push_str() {
    let spec = lookup_std_spec("std::string::String::push_str").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "(^self)@.len() == self@.len() + string@.len()",
        "String::push_str",
    );
}

#[test]
fn test_lookup_string_push() {
    let spec = lookup_std_spec("alloc::string::String::push").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self)@ == self@.push_back(ch)", "String::push");
}

#[test]
fn test_lookup_string_capacity() {
    let spec = lookup_std_spec("std::string::String::capacity").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result@ >= self.len()", "String::capacity");
}

#[test]
fn test_lookup_string_clear() {
    let spec = lookup_std_spec("alloc::string::String::clear").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self).len() == 0", "String::clear");
}

#[test]
fn test_lookup_str_len() {
    let spec = lookup_std_spec("str::len").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result >= 0", "str::len");
    assert_ensures_contains(
        &spec,
        "self@.index_logic(0).to_utf8().len()",
        "str::len singleton UTF-8 byte length",
    );
    assert!(
        spec.ensures.iter().all(|e| parse_spec(e).is_some()),
        "str::len ensures should parse: {:?}",
        spec.ensures
    );
}

#[test]
fn test_lookup_str_is_empty() {
    let spec = lookup_std_spec("str::is_empty").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == (self.len() == 0)", "str::is_empty");
}

#[test]
fn test_lookup_str_split_at() {
    let spec = lookup_std_spec("core::str::split_at").unwrap();
    // The byte index must be a char boundary the char view can name: 0, or
    // the end of a one-char string. A char-count bound names none.
    assert_eq!(
        spec.requires,
        ["mid@ == 0 || (self@.len() == 1 && mid@ == self@.index_logic(0).to_utf8().len())"],
        "str::split_at requires a nameable char boundary"
    );
    assert_ensures_contains(
        &spec,
        "self@.len() == 1 && mid@ == self@.index_logic(0).to_utf8().len() ==> result.0@ == self@",
        "str::split_at singleton UTF-8 full-prefix result",
    );
    assert_ensures_contains(
        &spec,
        "self@.len() == 1 && mid@ == self@.index_logic(0).to_utf8().len() ==> result.1@ == Seq::empty()",
        "str::split_at singleton UTF-8 empty suffix",
    );
    assert!(
        spec.requires.iter().all(|r| parse_spec(r).is_some())
            && spec.ensures.iter().all(|e| parse_spec(e).is_some()),
        "str::split_at clauses should parse: {:?} {:?}",
        spec.requires,
        spec.ensures
    );
}
