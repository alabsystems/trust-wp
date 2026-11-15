// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The guard on the one code path that places a field (D-31).

use super::*;

/// Strip line comments and then ALL whitespace, so the counts below cannot be
/// evaded by a spelling.
///
/// A guard that greps the literal `"Self {"` is walked straight past by
/// `Self{` — no space — and inflated by a doc comment mentioning the same
/// token. Both are one keystroke away from a guard that passes while the
/// thing it guards is gone.
fn code_without_whitespace(source: &str) -> String {
    source
        .lines()
        .map(|line| match line.find("//") {
            Some(idx) => &line[..idx],
            None => line,
        })
        .collect::<String>()
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect()
}

/// The whole point of `contract_rewrite::placement` is that there is ONE way
/// to obtain a placement carrying an index, and it needs a declaration.
///
/// Privacy already enforces that outside the module: `FieldPlacement`'s fields
/// are private, so nothing in `named_fields` can assemble one from a flat
/// field-name map or from source order. What privacy cannot enforce is a
/// second constructor added INSIDE the kernel — the natural shape of a
/// regression here is a small helper that "just" handles a case the lookup
/// missed, and that helper is a guess.
///
/// So the kernel's own construction sites are counted here. If this test
/// fails, a second `Self` literal was added to `placement.rs`: read it, decide
/// whether it can place a field somewhere no declaration put it, and only
/// then update the count.
#[test]
fn placement_kernel_has_exactly_one_placing_constructor() {
    let kernel = code_without_whitespace(include_str!("../placement.rs"));

    // A `Self` struct literal, not a `-> Self` return type. Whitespace and
    // comments are already gone, so `Self{`, `Self  {` and `Self\n{` all count
    // the same and a doc comment naming the token counts for nothing.
    let constructions = kernel.matches("Self{").count() - kernel.matches("->Self{").count();
    assert_eq!(
        constructions, 1,
        "placement.rs must construct a FieldPlacement in exactly ONE place: \
         `from_declaration`, which takes a declaration. Found {constructions}."
    );

    // A `FieldPlacement { .. }` spelled out in full would bypass that
    // constructor; the only two in the file are the `struct` and the `impl`.
    let named = kernel.matches("FieldPlacement{").count()
        - kernel.matches("structFieldPlacement{").count()
        - kernel.matches("implFieldPlacement{").count();
    assert_eq!(
        named, 0,
        "a `FieldPlacement {{ .. }}` literal in placement.rs is a construction \
         site that bypasses the one constructor"
    );
}

/// The guard must not be satisfiable by removing the space.
#[test]
fn the_kernel_guard_reads_through_spelling_and_comments() {
    let spaced = code_without_whitespace("let x = Self { a: 1 };");
    let tight = code_without_whitespace("let x = Self{ a: 1 };");
    let newline = code_without_whitespace("let x = Self\n{ a: 1 };");
    for (label, text) in [("spaced", spaced), ("tight", tight), ("newline", newline)] {
        assert_eq!(
            text.matches("Self{").count(),
            1,
            "the {label} spelling must count as one construction"
        );
    }
    let commented = code_without_whitespace("// a Self { .. } in prose\nlet y = 1;");
    assert_eq!(
        commented.matches("Self{").count(),
        0,
        "a comment mentioning the token must count for nothing"
    );
}

/// A variant pattern whose constructor has no entry refuses rather than
/// consulting the flat map
/// (`tests/adversarial/cases/s82v3_selfmod_path_reorder.rs`).
///
/// `self::E::C` is a spelling the constructor table's path rules do not
/// produce, so the entry is missing. Were the flat name->index map to answer
/// instead, it would answer from a decoy STRUCT in the same signature that
/// happens to declare `a` and `b` the other way round. An ENUM contributes
/// nothing to that map (`build_struct_field_map` returns early on
/// `!adt_def.is_struct()`), so the flat map cannot be right about a variant's
/// fields even by accident: it is the wrong oracle for this question in every
/// case.
///
/// The placement indices `[0, 1]` it would produce ARE a permutation of
/// `0..2`, so a guard that catches a foreign type answering cannot fire
/// either.
#[test]
fn a_variant_pattern_is_never_placed_from_the_flat_field_map() {
    // What a decoy `struct D { a: u32, b: u32 }` in the signature teaches the
    // flat map.
    let mut field_map = HashMap::new();
    field_map.insert("a".to_string(), 0);
    field_map.insert("b".to_string(), 1);

    let pattern = Pattern::Constructor {
        name: "self::E::C{a,b}".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("aa".to_string()),
            Pattern::Binding("bb".to_string()),
        ]))),
    };
    let why = rewrite_named_struct_pattern(&pattern, flat_tables(&field_map))
        .expect_err("a constructor with no declaration must refuse, not consult the flat map");
    assert!(
        why.contains("no declaration for that name was found"),
        "{why}"
    );

    // The same on the literal path.
    let args = vec![PureExpr::Int(5), PureExpr::Int(7)];
    let why = reorder_named_fields_to_positional(
        "self::E::C",
        &["a", "b"],
        &args,
        flat_tables(&field_map),
    )
    .expect_err("a struct literal with no declaration must refuse too");
    assert!(
        why.contains("no declaration for that name was found"),
        "{why}"
    );
}

/// The other tempting no-lookup branch: with no entry and exactly one named
/// field and no `..`, return index 0 with no lookup at all, arguing that a
/// complete brace pattern binds every field. That argument holds only if the
/// constructor really declares one field — which is precisely what has not
/// been looked up. Spelled `self::E::C` against a two-field `E::C`, index 0
/// is the OTHER field.
#[test]
fn a_one_field_pattern_with_no_declaration_is_refused() {
    let field_map = HashMap::new();

    let pattern = Pattern::Constructor {
        name: "self::E::C{a}".to_string(),
        inner: Some(Box::new(Pattern::Binding("aa".to_string()))),
    };
    let why = rewrite_named_struct_pattern(&pattern, flat_tables(&field_map))
        .expect_err("one named field is still a field that has to be placed");
    assert!(
        why.contains("no declaration for that name was found"),
        "{why}"
    );
}

/// A spelling rustc RESOLVED is what makes a spelling this file cannot
/// CONSTRUCT placeable at all — and it is added to the candidates, not
/// preferred over them (D-31).
///
/// Preferring it would recover the proofs a crate-wide namesake refuses, and
/// that is exactly why it is not done: the clauses merged into one contract do
/// not all come from the two places the harvest reaches, so "resolved
/// somewhere in this function's clauses" is not "resolved for THIS
/// occurrence". Adding candidates can only move the outcome toward a refusal.
#[test]
fn a_resolved_constructor_is_a_candidate_not_an_override() {
    let mut candidates = CtorCandidates::default();
    // A namesake elsewhere in the crate answers to the same spelling.
    candidates.record_declared(DeclaredFields::from_names_for_test(&["a", "b"]));
    // rustc resolved the spelling in a type-checked clause: `{b, a}`.
    candidates.record_resolved(DeclaredFields::from_names_for_test(&["b", "a"]));
    assert_eq!(
        candidates.lists().len(),
        2,
        "the resolved answer joins the candidates, it does not replace them"
    );

    // The same declaration twice is one candidate, whichever way it arrived.
    candidates.record_declared(DeclaredFields::from_names_for_test(&["b", "a"]));
    assert_eq!(candidates.lists().len(), 2);
}

/// A spelling with one resolved constructor and no namesake places its
/// pattern at the DECLARED indices — the `self::E::C` / `super::E::C` shape,
/// where path construction alone yields no entry and only rustc's resolution
/// can supply one (`tests/adversarial/cases/s82v3_selfmod_path_reorder.rs`,
/// `s82v3_super_path_reorder.rs`).
#[test]
fn a_resolved_spelling_places_its_pattern_at_the_declared_indices() {
    let field_map = HashMap::new();
    let mut ctors = CtorFieldOrder::new();
    ctors
        .entry("self::E::C".to_string())
        .or_default()
        .record_resolved(DeclaredFields::from_names_for_test(&["b", "a"]));

    let pattern = Pattern::Constructor {
        name: "self::E::C{a,b}".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("aa".to_string()),
            Pattern::Binding("bb".to_string()),
        ]))),
    };
    let result = rewrite_named_struct_pattern(&pattern, ctor_tables(&field_map, &ctors))
        .expect("the resolved declaration places it");
    assert_eq!(
        result,
        Pattern::Constructor {
            name: "self::E::C".to_string(),
            // Declared `{b, a}`: the pattern's `a` is index 1, `b` index 0.
            inner: Some(Box::new(Pattern::Tuple(vec![
                Pattern::Binding("bb".to_string()),
                Pattern::Binding("aa".to_string()),
            ]))),
        }
    );
}

/// And a namesake that places the same fields differently still refuses, even
/// with a resolved candidate present.
#[test]
fn a_disagreeing_namesake_still_refuses_a_resolved_spelling() {
    let field_map = HashMap::new();
    let mut ctors = CtorFieldOrder::new();
    let entry = ctors.entry("C".to_string()).or_default();
    entry.record_resolved(DeclaredFields::from_names_for_test(&["b", "a"]));
    entry.record_declared(DeclaredFields::from_names_for_test(&["a", "b"]));

    let pattern = Pattern::Constructor {
        name: "C{a,b}".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("aa".to_string()),
            Pattern::Binding("bb".to_string()),
        ]))),
    };
    let why = rewrite_named_struct_pattern(&pattern, ctor_tables(&field_map, &ctors))
        .expect_err("two constructors placing these fields differently must refuse");
    assert!(why.contains("place these"), "{why}");
}
