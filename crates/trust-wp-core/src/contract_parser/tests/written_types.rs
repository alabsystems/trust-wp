// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The parser drops most written types from the AST; `parse_contract_written_types`
//! must report every one of them so consumers can refuse what the AST cannot show.
//! A cast is the exception: it is lowered to Rust's `as` (see `casts.rs`) or
//! refused, and recorded all the same.

use super::*;

fn written(input: &str) -> Vec<(WrittenTypeSite, Option<String>)> {
    parse_contract_written_types(input)
        .expect("clause parses")
        .into_iter()
        .map(|w| (w.site, w.text))
        .collect()
}

fn one(site: WrittenTypeSite, text: &str) -> Vec<(WrittenTypeSite, Option<String>)> {
    vec![(site, Some(text.to_string()))]
}

#[test]
fn casts_and_ascriptions_are_recorded() {
    assert_eq!(written("(x as u8)@ == 0"), one(WrittenTypeSite::Cast, "u8"));
    // A cast to a type the parser cannot model is refused, not erased.
    assert!(parse_contract_written_types("(x as Wd)@ == 0").is_err());
    assert_eq!(
        written("(x : crate::t::Wd)@ == 0"),
        one(WrittenTypeSite::Ascription, "crate::t::Wd")
    );
    // The cast is not its operand.
    assert_ne!(
        parse_contract("(x as u8)@ == 0").unwrap(),
        parse_contract("x@ == 0").unwrap()
    );
}

#[test]
fn binder_annotations_are_recorded_with_their_text() {
    assert_eq!(
        written("forall<v: Wd> v@ < 256"),
        one(WrittenTypeSite::QuantifierBinder, "Wd")
    );
    assert_eq!(
        written("forall<p: (Wd, bool)> p.0@ < 256"),
        one(WrittenTypeSite::QuantifierBinder, "(Wd, bool)")
    );
    assert_eq!(
        written("exists<v: *const Wd> v == v"),
        one(WrittenTypeSite::QuantifierBinder, "*const Wd")
    );
    assert_eq!(
        written("exists<a: Int, b> a == b"),
        vec![
            (WrittenTypeSite::QuantifierBinder, Some("Int".to_string())),
            (WrittenTypeSite::QuantifierBinder, None),
        ]
    );
}

#[test]
fn closure_and_let_annotations_are_recorded() {
    assert_eq!(
        written("(|v: Wd| v@ < 256) == (|v: Wd| v@ < 256)"),
        vec![
            (WrittenTypeSite::ClosureParam, Some("Wd".to_string())),
            (WrittenTypeSite::ClosureParam, Some("Wd".to_string())),
        ]
    );
    assert_eq!(
        written("(|v| v) == (|(a, b)| a)"),
        vec![
            (WrittenTypeSite::ClosureParam, None),
            (WrittenTypeSite::ClosureParam, None),
        ]
    );
    assert_eq!(
        written("{ let y: Wd = x; y@ < 256 }"),
        one(WrittenTypeSite::LetBinding, "Wd")
    );
}

#[test]
fn literal_suffixes_are_recorded_although_the_ast_keeps_only_the_value() {
    assert_eq!(
        written("255u8 + 1u8 == 0u8"),
        vec![
            (WrittenTypeSite::LiteralSuffix, Some("u8".to_string())),
            (WrittenTypeSite::LiteralSuffix, Some("u8".to_string())),
            (WrittenTypeSite::LiteralSuffix, Some("u8".to_string())),
        ]
    );
    assert_eq!(
        parse_contract("255u8 + 1u8 == 0u8").unwrap(),
        parse_contract("255u16 + 1u16 == 0u16").unwrap()
    );
    assert_eq!(
        written("x == 0x1Fusize"),
        one(WrittenTypeSite::LiteralSuffix, "usize")
    );
    assert_eq!(
        written("x@ == 3int"),
        one(WrittenTypeSite::LiteralSuffix, "int")
    );
    assert_eq!(
        written("y == 2.5f64"),
        one(WrittenTypeSite::LiteralSuffix, "f64")
    );
    assert_eq!(written("x@ == 3 && y == 2.5 && t.0 == 1"), vec![]);
}

#[test]
fn clauses_without_written_types_record_nothing() {
    assert_eq!(written("x@ + 1 < 256 && result == x"), vec![]);
    assert_eq!(written("match x { (a, _) => a == 1, _ => false }"), vec![]);
}

#[test]
fn written_type_errors_match_spanned_parse_errors() {
    for input in ["x as", "forall<v: > true", "x +"] {
        assert_eq!(
            parse_contract_written_types(input).is_err(),
            parse_contract_spanned(input).is_err(),
            "{input}"
        );
    }
}
