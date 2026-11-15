// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Named struct constructor reordering tests (#1819) ---

/// Regression #1819: struct literal with reversed field order must reorder.
/// `Point { y: 1, x: 0 }` declared `{ x, y }` → `Point(0, 1)`.
///
/// The placement comes from `Point`'s DECLARATION, never from the flat
/// name->index map, which is built from whatever structs a signature mentions
/// and answers for a namesake field of an unrelated type (D-31).
#[test]
fn reorders_named_struct_literal_to_canonical() {
    let field_map = HashMap::new();
    let ctors = ctors_for("Point", &["x", "y"]);

    // Parser output: LogicFnCall { name: "Point{y,x}", args: [1, 0] }
    let expr = PureExpr::LogicFnCall {
        name: "Point{y,x}".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(0)],
    };
    let result = rewrite_named_field_access_expr(&expr, ctor_tables(&field_map, &ctors))
        .expect("resolvable");
    // After rewrite: LogicFnCall { name: "Point", args: [0, 1] }
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "Point".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(1)],
        }
    );
}

/// Regression #1819: struct literal in canonical order produces same result.
#[test]
fn reorders_named_struct_literal_already_canonical() {
    let field_map = HashMap::new();
    let ctors = ctors_for("Point", &["x", "y"]);

    let expr = PureExpr::LogicFnCall {
        name: "Point{x,y}".to_string(),
        args: vec![PureExpr::Int(0), PureExpr::Int(1)],
    };
    let result = rewrite_named_field_access_expr(&expr, ctor_tables(&field_map, &ctors))
        .expect("resolvable");
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "Point".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(1)],
        }
    );
}

/// An unresolvable field name is REFUSED, never placed in source order.
///
/// A source-order fallback is a false accept: a guess that places one field
/// where another is declared types a binding as the wrong field, and the
/// verifier then discharges an obligation about a `u32` with another field's
/// logic function (D-31;
/// `tests/adversarial/cases/s82_structpat_unresolvable_ctor_refused.rs`).
#[test]
fn reorder_named_fields_unknown_field_is_refused() {
    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    // "z" is in no table at all.

    let field_names = ["z", "x"];
    let args = vec![PureExpr::Int(99), PureExpr::Int(0)];
    let result =
        reorder_named_fields_to_positional("Point", &field_names, &args, flat_tables(&field_map));
    let why = result.expect_err("an unresolvable field name must refuse");
    assert!(why.contains("Point"), "{why}");
    assert!(why.contains("declaration order"), "{why}");
}

/// A declared constructor resolves a field name the flat map never saw.
///
/// `E::C` is an ENUM VARIANT, so `build_struct_field_map` contributes nothing
/// for it (it returns early on `!adt_def.is_struct()`); the constructor table
/// is what makes the reorder possible instead of a refusal.
#[test]
fn reorder_named_fields_resolves_from_the_constructor_table() {
    let field_map = HashMap::new();
    let ctors = ctors_for("E::C", &["a", "b"]);

    let field_names = ["b", "a"];
    let args = vec![PureExpr::Int(7), PureExpr::Int(5)];
    let result = reorder_named_fields_to_positional(
        "E::C",
        &field_names,
        &args,
        ctor_tables(&field_map, &ctors),
    )
    .expect("the declared order resolves");
    assert_eq!(result, vec![PureExpr::Int(5), PureExpr::Int(7)]);
}

/// Two constructors answering to one spelling that PLACE the fields
/// differently cannot be resolved, so they are refused.
#[test]
fn reorder_named_fields_disagreeing_candidates_are_refused() {
    let field_map = HashMap::new();
    let ctors = ctors_with_candidates("C", &[&["a", "b"], &["b", "a"]]);

    let field_names = ["b", "a"];
    let args = vec![PureExpr::Int(7), PureExpr::Int(5)];
    let why = reorder_named_fields_to_positional(
        "C",
        &field_names,
        &args,
        ctor_tables(&field_map, &ctors),
    )
    .expect_err("disagreeing candidates must refuse");
    assert!(why.contains("place these"), "{why}");
}

/// Two constructors answering to one spelling that AGREE on where these
/// fields sit resolve fine — the refusal is for real disagreement, not for a
/// merely shared name.
#[test]
fn reorder_named_fields_agreeing_candidates_resolve() {
    let field_map = HashMap::new();
    let ctors = ctors_with_candidates("C", &[&["a", "b"], &["a", "b", "c"]]);

    // Only the two-field candidate can be a complete brace pattern here.
    let field_names = ["b", "a"];
    let args = vec![PureExpr::Int(7), PureExpr::Int(5)];
    let result = reorder_named_fields_to_positional(
        "C",
        &field_names,
        &args,
        ctor_tables(&field_map, &ctors),
    )
    .expect("the surviving candidate resolves");
    assert_eq!(result, vec![PureExpr::Int(5), PureExpr::Int(7)]);
}

/// A struct literal whose value count does not match its field-name
/// count is refused rather than passed through in source order.
#[test]
fn reorder_named_fields_mismatched_length_is_refused() {
    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);

    let field_names = ["x"];
    let args = vec![PureExpr::Int(0), PureExpr::Int(1)]; // 2 args, 1 name
    let why =
        reorder_named_fields_to_positional("Point", &field_names, &args, flat_tables(&field_map))
            .expect_err("an arity mismatch must refuse");
    assert!(why.contains("number of values"), "{why}");
}

/// A `..` rest pattern is expanded to the constructor's full arity with
/// `Wildcard` in every position it did not name.
///
/// The field list must survive the parser when `..` is present: without it
/// the driver would place the first NAMED field at index 0, and
/// `E::C { b: bb, .. }` would bind `bb` to the field declared FIRST
/// (`tests/adversarial/cases/s82_structpat_reorder_rest.rs`).
#[test]
fn rest_pattern_places_its_named_field_and_pads_the_rest() {
    let field_map = HashMap::new();
    let ctors = ctors_for("E::C", &["a", "b"]);

    let pattern = Pattern::Constructor {
        name: "E::C{b,..}".to_string(),
        inner: Some(Box::new(Pattern::Binding("bb".to_string()))),
    };
    let result = rewrite_named_struct_pattern(&pattern, ctor_tables(&field_map, &ctors))
        .expect("the declared order resolves");
    assert_eq!(
        result,
        Pattern::Constructor {
            name: "E::C".to_string(),
            inner: Some(Box::new(Pattern::Tuple(vec![
                Pattern::Wildcard,
                Pattern::Binding("bb".to_string()),
            ]))),
        }
    );
}

/// A `..` rest pattern over a constructor with no declaration found is
/// refused — a rest pattern binds an unknown subset of an unknown arity.
#[test]
fn rest_pattern_without_a_declaration_is_refused() {
    let mut field_map = HashMap::new();
    field_map.insert("b".to_string(), 1);

    let pattern = Pattern::Constructor {
        name: "Unknown{b,..}".to_string(),
        inner: Some(Box::new(Pattern::Binding("bb".to_string()))),
    };
    let why = rewrite_named_struct_pattern(&pattern, flat_tables(&field_map))
        .expect_err("a rest pattern with no declared arity must refuse");
    assert!(why.contains("rest pattern"), "{why}");
}

/// Regression #1819: struct pattern with reversed fields must reorder.
#[test]
fn reorders_named_struct_pattern_to_canonical() {
    use trust_wp_core::formula::Pattern;

    let field_map = HashMap::new();
    let ctors = ctors_for("Point", &["x", "y"]);

    // Parser output: Constructor { name: "Point{y,x}", inner: Tuple([Binding("y"), Binding("x")]) }
    let pattern = Pattern::Constructor {
        name: "Point{y,x}".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("y".to_string()),
            Pattern::Binding("x".to_string()),
        ]))),
    };
    let result = rewrite_named_struct_pattern(&pattern, ctor_tables(&field_map, &ctors))
        .expect("resolvable");
    // After rewrite: Constructor { name: "Point", inner: Tuple([Binding("x"), Binding("y")]) }
    assert_eq!(
        result,
        Pattern::Constructor {
            name: "Point".to_string(),
            inner: Some(Box::new(Pattern::Tuple(vec![
                Pattern::Binding("x".to_string()),
                Pattern::Binding("y".to_string()),
            ]))),
        }
    );
}

#[test]
fn rewrite_named_field_access_rewrites_match_patterns_and_bodies_together() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    // The flat map answers the field ACCESS half (`__trust_wp_field_y`); the
    // declaration answers the PATTERN half. Two questions, two tables.
    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);
    let ctors = ctors_for("Point", &["x", "y"]);

    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("p".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Point{y,x}".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("y".to_string()),
                    Pattern::Binding("x".to_string()),
                ]))),
            },
            body: PureExpr::LogicFnCall {
                name: "__trust_wp_field_y".to_string(),
                args: vec![PureExpr::Var("p".to_string(), None)],
            },
        }],
    };

    let result = rewrite_named_field_access_expr(&expr, ctor_tables(&field_map, &ctors))
        .expect("resolvable");
    assert_eq!(
        result,
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("p".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Point".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x".to_string()),
                        Pattern::Binding("y".to_string()),
                    ]))),
                },
                body: PureExpr::LogicFnCall {
                    name: "__trust_wp_tuple_get_1".to_string(),
                    args: vec![PureExpr::Var("p".to_string(), None)],
                },
            }],
        }
    );
}

#[test]
fn rewrite_named_field_access_rewrites_match_quantifier_triggers_and_patterns() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);
    let ctors = ctors_for("Point", &["x", "y"]);

    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("p".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Point{y,x}".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("y".to_string()),
                    Pattern::Binding("x".to_string()),
                ]))),
            },
            body: PureExpr::Forall {
                var: "i".to_string(),
                var_sort: Some(ExprSort::Int),
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::LogicFnCall {
                        name: "__trust_wp_field_y".to_string(),
                        args: vec![PureExpr::Var("p".to_string(), None)],
                    }),
                    BinOp::Ge,
                    Arc::new(PureExpr::Var("i".to_string(), None)),
                )),
                triggers: vec![vec![PureExpr::LogicFnCall {
                    name: "__trust_wp_field_x".to_string(),
                    args: vec![PureExpr::Var("p".to_string(), None)],
                }]],
            },
        }],
    };

    let result = rewrite_named_field_access_expr(&expr, ctor_tables(&field_map, &ctors))
        .expect("resolvable");
    assert_eq!(
        result,
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("p".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Point".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x".to_string()),
                        Pattern::Binding("y".to_string()),
                    ]))),
                },
                body: PureExpr::Forall {
                    var: "i".to_string(),
                    var_sort: Some(ExprSort::Int),
                    body: Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::LogicFnCall {
                            name: "__trust_wp_tuple_get_1".to_string(),
                            args: vec![PureExpr::Var("p".to_string(), None)],
                        }),
                        BinOp::Ge,
                        Arc::new(PureExpr::Var("i".to_string(), None)),
                    )),
                    triggers: vec![vec![PureExpr::LogicFnCall {
                        name: "__trust_wp_tuple_get_0".to_string(),
                        args: vec![PureExpr::Var("p".to_string(), None)],
                    }]],
                },
            }],
        }
    );
}

/// Regression #1819: single-field struct pattern is not wrapped in Tuple.
#[test]
fn reorders_single_field_struct_pattern() {
    use trust_wp_core::formula::Pattern;

    let field_map = HashMap::new();
    let ctors = ctors_for("Wrapper", &["val"]);

    let pattern = Pattern::Constructor {
        name: "Wrapper{val}".to_string(),
        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
    };
    let result = rewrite_named_struct_pattern(&pattern, ctor_tables(&field_map, &ctors))
        .expect("resolvable");
    assert_eq!(
        result,
        Pattern::Constructor {
            name: "Wrapper".to_string(),
            inner: Some(Box::new(Pattern::Binding("v".to_string()))),
        }
    );
}

/// Regression #1819: three-field reorder with non-trivial permutation.
#[test]
fn reorders_three_field_struct_literal() {
    let field_map = HashMap::new();
    let ctors = ctors_for("Triple", &["a", "b", "c"]);

    // User writes: Triple { c: 2, a: 0, b: 1 }
    let expr = PureExpr::LogicFnCall {
        name: "Triple{c,a,b}".to_string(),
        args: vec![PureExpr::Int(2), PureExpr::Int(0), PureExpr::Int(1)],
    };
    let result = rewrite_named_field_access_expr(&expr, ctor_tables(&field_map, &ctors))
        .expect("resolvable");
    // Canonical order: Triple(0, 1, 2)
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "Triple".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(1), PureExpr::Int(2)],
        }
    );
}

/// The candidate table is BOUNDED, and a bound that DROPS is a fallback
/// branch — the one thing `place_named_fields` documents it does not have
/// (D-31).
///
/// Eight decoy constructors answer to `C` before the real one is offered, so
/// the ninth list (`{b, a}` — the constructor this pattern actually means) does
/// not fit. Every survivor that could be a complete two-field brace pattern
/// agrees on `{a, b}`, so a table that merely dropped the ninth would resolve
/// the pattern happily against a decoy and place `a` at index 0 — the very
/// mis-typing the placement refusals exist to stop. A cap that records its
/// own truncation refuses instead
/// (`tests/adversarial/cases/s82v2_ctor_candidate_cap.rs`).
#[test]
fn a_capped_candidate_set_is_refused_not_resolved_against_a_survivor() {
    let field_map = HashMap::new();
    let ctors = ctors_with_candidates(
        "C",
        &[
            // Eight DISTINCT decoy field lists — the cap's worth.
            &["a", "b"],
            &["a", "b", "c"],
            &["a", "b", "c", "d"],
            &["a", "b", "c", "d", "e"],
            &["a", "b", "c", "d", "e", "f"],
            &["a", "b", "c", "d", "e", "f", "g"],
            &["a", "b", "c", "d", "e", "f", "g", "h"],
            &["a", "b", "c", "d", "e", "f", "g", "h", "i"],
            // The REAL constructor, offered ninth.
            &["b", "a"],
        ],
    );

    let field_names = ["a", "b"];
    let args = vec![PureExpr::Int(5), PureExpr::Int(7)];
    let why = reorder_named_fields_to_positional(
        "C",
        &field_names,
        &args,
        ctor_tables(&field_map, &ctors),
    )
    .expect_err("a capped candidate set cannot place anything");
    assert!(why.contains("than the candidate table keeps"), "{why}");

    // The same refusal on the PATTERN path, the shape
    // `tests/adversarial/cases/s82v2_ctor_candidate_cap.rs` exercises.
    let pattern = Pattern::Constructor {
        name: "C{a,b}".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("aa".to_string()),
            Pattern::Binding("bb".to_string()),
        ]))),
    };
    let why = rewrite_named_struct_pattern(&pattern, ctor_tables(&field_map, &ctors))
        .expect_err("a capped candidate set cannot place a pattern either");
    assert!(why.contains("than the candidate table keeps"), "{why}");
}

/// The bookkeeping the refusal above rests on. Eight distinct
/// lists fit; the ninth does not and is RECORDED as turned away rather than
/// forgotten. A duplicate never counts against the cap.
#[test]
fn candidate_recording_marks_truncation_instead_of_dropping_silently() {
    let mut candidates = CtorCandidates::default();
    for n in 2..=9usize {
        let fields: Vec<String> = (0..n)
            .map(|i| ((b'a' + i as u8) as char).to_string())
            .collect();
        let borrowed: Vec<&str> = fields.iter().map(String::as_str).collect();
        candidates.record_declared(DeclaredFields::from_names_for_test(&borrowed));
    }
    assert_eq!(candidates.lists().len(), 8, "eight distinct lists fit");
    assert!(!candidates.is_capped(), "eight is not over the cap");

    // A duplicate of one already held is not a new candidate.
    candidates.record_declared(DeclaredFields::from_names_for_test(&["a", "b"]));
    assert_eq!(candidates.lists().len(), 8);
    assert!(
        !candidates.is_capped(),
        "a duplicate does not cap the entry"
    );

    // A ninth DISTINCT list does not fit, and says so.
    candidates.record_declared(DeclaredFields::from_names_for_test(&["b", "a"]));
    assert_eq!(candidates.lists().len(), 8, "the cap still holds");
    assert!(
        candidates.is_capped(),
        "the turned-away candidate must be recorded, not dropped"
    );
}
