// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exhaustiveness checks for native match ITE encoding.

use std::borrow::Cow;

use ay_dpll::api::{DatatypeSort, Sort};
use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use super::{short_constructor_name, AYEncoder, SwitchTarget};
use crate::encoder::sort_context::{
    expr_sort_to_ay_sort, extract_inner_var_annotation, resolve_adt_family_alias,
    resolve_nameable_expr, resolve_registered_non_int_sort, DerivedKind,
};

/// Sentinel "constructor" name for `Pattern::Literal(Bool(true))` when used
/// inside tuple-position exhaustiveness checks. Distinct from any valid Rust
/// identifier so it cannot collide with a real constructor.
const BOOL_TRUE_SENTINEL: &str = "__bool_true__";
/// Sentinel "constructor" name for `Pattern::Literal(Bool(false))`.
const BOOL_FALSE_SENTINEL: &str = "__bool_false__";

impl AYEncoder {
    pub(super) fn match_datatype(
        &self,
        scrutinee: &PureExpr,
        arms: &[MatchArm],
        prefix: Option<DerivedKind>,
    ) -> Option<DatatypeSort> {
        // Accept both Var and Deref(Var) scrutinees. Deref(Var("self")) is the
        // common pattern for `match *self { ... }` in method implementations
        // (e.g., `is_ok`, `is_err`). Without this, the match doesn't trigger
        // native datatype declaration, forcing the UF axiom fallback and
        // preventing constructor equality elimination in postcondition
        // quantifiers. (#1752)
        //
        // Also accept Deref(LogicFnCall) for patterns like `match *None() { ... }`
        // where the scrutinee is a concrete constructor call wrapped in a deref.
        // This arises in postcondition substitution when `self` is replaced by a
        // concrete value (e.g., `ok_or` matching on `*self` after substituting
        // `self = None()`). Without this, datatype inference fails and proof_assert
        // obligations for option/result methods become Unknown. (#2670)
        // Also accept a bare tuple-getter call scrutinee
        // (`__trust_wp_tuple_get_I(t)`, possibly under Old/Deref/Final/View).
        // The open-logic-fn inliner rewrites `sum(get_1(t))` into
        // `Match { scrutinee: get_1(t), arms: <sum's body> }`, so recursive
        // unfolding facts in requires-phase scopes match directly ON the
        // opaque projection. Rejecting that shape here dropped the arms'
        // datatype context entirely: the getter placeholder then minted with
        // the Int default (no callee for the 87b48b9 argument-position
        // preseed — the callee was rewritten away — and no declared tuple
        // ctor yet for the ctor-domain derivation), which degraded every
        // pattern test to the non-datatype tester fallback and seeded the
        // stale Int getter family behind the take_some_rest base-recheck
        // premise corruption. The arms are the authority here; the existing
        // `registered_match_datatype` logic still requires them to resolve a
        // unique declared datatype. (#getters2)
        let is_tuple_getter_scrutinee = self.peel_tuple_getter_call(scrutinee).is_some();
        if !matches!(scrutinee, PureExpr::Var(_, _) | PureExpr::Deref(_))
            && !is_tuple_getter_scrutinee
        {
            return None;
        }
        if let PureExpr::Deref(inner) = scrutinee {
            if !is_tuple_getter_scrutinee
                && !matches!(
                    inner.as_ref(),
                    PureExpr::Var(_, _) | PureExpr::LogicFnCall { .. }
                )
            {
                return None;
            }
        }

        if let Some(datatype) = self.registered_match_datatype(scrutinee, arms, prefix) {
            return Some(datatype);
        }

        SwitchTarget::from_arms(arms).map(|st| self.canonical_match_datatype(st.datatype()))
    }

    fn canonical_match_datatype(&self, datatype: DatatypeSort) -> DatatypeSort {
        if let Some(registered) = self.get_datatype_decl(&datatype.name) {
            return registered.clone();
        }

        if let Some(alias) = resolve_adt_family_alias(&datatype.name) {
            if let Some(registered) = self.get_datatype_decl(&alias) {
                return registered.clone();
            }
        }

        datatype
    }

    fn registered_match_datatype(
        &self,
        scrutinee: &PureExpr,
        arms: &[MatchArm],
        prefix: Option<DerivedKind>,
    ) -> Option<DatatypeSort> {
        if !arms
            .iter()
            .any(|arm| Self::constructor_pattern_name(&arm.pattern).is_some())
        {
            return None;
        }

        if let Some(datatype) = self.authoritative_match_datatype(scrutinee, prefix) {
            if Self::datatype_matches_arms(&datatype, arms) {
                return Some(datatype);
            }
        }

        let mut matches = self
            .datatypes_iter()
            .filter(|dt| Self::datatype_matches_arms(dt, arms));
        let first = matches.next()?.clone();
        if matches.next().is_some() {
            return None;
        }
        Some(first)
    }

    fn authoritative_match_datatype(
        &self,
        scrutinee: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Option<DatatypeSort> {
        if let Some(annotation) = extract_inner_var_annotation(scrutinee) {
            let annotation_sort = expr_sort_to_ay_sort(annotation);
            if let Some(datatype) = self.datatype_from_registered_sort(&annotation_sort) {
                return Some(datatype);
            }
        }

        resolve_nameable_expr(scrutinee, prefix)
            .and_then(|name| resolve_registered_non_int_sort(self, &name))
            .and_then(|sort| self.datatype_from_registered_sort(&sort))
    }

    fn datatype_from_registered_sort(&self, sort: &Sort) -> Option<DatatypeSort> {
        match sort {
            Sort::Datatype(dt) => Some(dt.clone()),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
            _ => None,
        }
    }

    pub(super) fn datatype_matches_arms(datatype: &DatatypeSort, arms: &[MatchArm]) -> bool {
        arms.iter().all(|arm| match &arm.pattern {
            Pattern::Constructor { name, .. } => {
                let pattern_name = short_constructor_name(name);
                datatype
                    .constructors
                    .iter()
                    // #prophecy-slots (Fix B M1/M2): specialized carrier
                    // families spell their constructors `{family}__Some` /
                    // `{family}__None`, whose SHORT name is the whole
                    // spelling — a raw short-name comparison therefore never
                    // matches the logical `Some`/`None` an arm pattern
                    // carries, the family loses the match-datatype election
                    // to `OptionInt`, and the payload is extracted through
                    // the Int-ranged UF accessor (prophecy slot dropped).
                    // Additive: the alias-aware comparator is consulted only
                    // when the historical short-name test fails.
                    .any(|ctor| {
                        short_constructor_name(&ctor.name) == pattern_name
                            || super::datatype_constructor_matches(
                                datatype,
                                &ctor.name,
                                pattern_name,
                            )
                    })
            }
            Pattern::Alias { pattern, .. } => Self::datatype_pattern_matches(datatype, pattern),
            Pattern::Wildcard | Pattern::Binding(_) => true,
            _ => false,
        })
    }

    fn datatype_pattern_matches(datatype: &DatatypeSort, pattern: &Pattern) -> bool {
        match pattern {
            Pattern::Constructor { name, .. } => {
                let pattern_name = short_constructor_name(name);
                datatype
                    .constructors
                    .iter()
                    // #prophecy-slots (Fix B M1/M2): specialized carrier
                    // families spell their constructors `{family}__Some` /
                    // `{family}__None`, whose SHORT name is the whole
                    // spelling — a raw short-name comparison therefore never
                    // matches the logical `Some`/`None` an arm pattern
                    // carries, the family loses the match-datatype election
                    // to `OptionInt`, and the payload is extracted through
                    // the Int-ranged UF accessor (prophecy slot dropped).
                    // Additive: the alias-aware comparator is consulted only
                    // when the historical short-name test fails.
                    .any(|ctor| {
                        short_constructor_name(&ctor.name) == pattern_name
                            || super::datatype_constructor_matches(
                                datatype,
                                &ctor.name,
                                pattern_name,
                            )
                    })
            }
            Pattern::Alias { pattern, .. } => Self::datatype_pattern_matches(datatype, pattern),
            Pattern::Wildcard | Pattern::Binding(_) => true,
            _ => false,
        }
    }

    /// Check whether a pattern is a catch-all that matches any value (#1641).
    ///
    /// Catch-all patterns: `Wildcard`, `Binding(_)`, and `Tuple` where every
    /// sub-pattern is itself a catch-all (e.g., `(a, _)` or `(_, _, c)`).
    pub(super) fn is_catch_all_pattern(pattern: &Pattern) -> bool {
        match pattern {
            Pattern::Wildcard | Pattern::Binding(_) => true,
            Pattern::Alias { pattern, .. } => Self::is_catch_all_pattern(pattern),
            Pattern::Tuple(elements) => elements.iter().all(Self::is_catch_all_pattern),
            Pattern::Literal(_) | Pattern::Constructor { .. } => false,
            // Pattern is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
            _ => false,
        }
    }

    /// Check whether a match with all-constructor arms is exhaustive (#1641).
    ///
    /// Returns `true` when every constructor of the target datatype appears
    /// as a pattern in at least one arm. This makes the ITE default sound
    /// even without a wildcard: the datatype theory guarantees the scrutinee
    /// must match one of the declared constructors.
    ///
    /// When `datatype` is `Some`, checks directly against the declared
    /// constructors. When `datatype` is `None` (e.g., non-Var scrutinee),
    /// infers exhaustiveness from the arm patterns: known two-constructor
    /// types (Option: Some+None, Result: Ok+Err) are recognized as exhaustive.
    ///
    /// Also handles tuple-pattern matches (#1703): when all arms use `Tuple`
    /// patterns, infers per-position constructor sets and verifies that every
    /// combination in the cross product is matched by at least one arm.
    ///
    /// Phase 3 (B2): also recognizes additional small-finite-type patterns:
    /// matches against the unit type `()` (single inhabitant) and bool
    /// literal positions inside tuple patterns (two-element finite type).
    /// These extensions only add new "exhaustive" cases; they never reclassify
    /// non-exhaustive arm sets as exhaustive.
    pub(super) fn is_constructor_exhaustive(
        arms: &[MatchArm],
        datatype: Option<&DatatypeSort>,
    ) -> bool {
        if let Some(result) = Self::check_flat_constructor_exhaustive(arms, datatype) {
            return result;
        }

        if Self::check_bool_literal_exhaustive(arms) {
            return true;
        }

        if Self::check_unit_pattern_exhaustive(arms) {
            return true;
        }

        Self::check_tuple_exhaustive(arms)
    }

    /// Check exhaustiveness for boolean-literal-pattern matches.
    ///
    /// A match like `match cond { false_val => ..., true_val => ... }` is
    /// exhaustive over `bool`. Accept this whenever the arm patterns
    /// collectively cover both boolean literals. This keeps the ITE encoding
    /// sound for the boolean datatype even though `bool` is not declared as a
    /// `DatatypeSort` in the encoder (Creusot compat baseline: list_index_mut.rs).
    fn check_bool_literal_exhaustive(arms: &[MatchArm]) -> bool {
        let mut saw_true = false;
        let mut saw_false = false;
        for arm in arms {
            match Self::peel_alias_pattern(&arm.pattern) {
                Pattern::Wildcard | Pattern::Binding(_) => return true,
                Pattern::Literal(PureExpr::Bool(true)) => saw_true = true,
                Pattern::Literal(PureExpr::Bool(false)) => saw_false = true,
                _ => return false,
            }
        }
        saw_true && saw_false
    }

    fn peel_alias_pattern(pattern: &Pattern) -> &Pattern {
        let mut current = pattern;
        while let Pattern::Alias { pattern: inner, .. } = current {
            current = inner;
        }
        current
    }

    /// Check exhaustiveness for the unit type `()`.
    ///
    /// The unit type has exactly one inhabitant — the value `()`. A match
    /// whose arms are all empty-tuple patterns (`Pattern::Tuple(vec![])`),
    /// possibly mixed with catch-all arms, is exhaustive. Soundness rests on
    /// the fact that `()` has cardinality 1: any single matching arm covers
    /// the only possible scrutinee value. This parallels the bool-literal
    /// recognizer for two-valued types.
    fn check_unit_pattern_exhaustive(arms: &[MatchArm]) -> bool {
        let mut saw_unit = false;
        for arm in arms {
            match Self::peel_alias_pattern(&arm.pattern) {
                Pattern::Wildcard | Pattern::Binding(_) => return true,
                Pattern::Tuple(elements) if elements.is_empty() => saw_unit = true,
                _ => return false,
            }
        }
        saw_unit
    }

    /// Check flat (non-tuple) constructor exhaustiveness.
    /// Returns `Some(bool)` if the check applies, `None` if arms aren't flat constructors.
    fn check_flat_constructor_exhaustive(
        arms: &[MatchArm],
        datatype: Option<&DatatypeSort>,
    ) -> Option<bool> {
        let dt = if let Some(dt) = datatype {
            Cow::Borrowed(dt)
        } else if let Some(target) = SwitchTarget::from_arms(arms) {
            Cow::Owned(target.datatype())
        } else {
            return None;
        };

        let arm_ctors: Vec<&str> = arms
            .iter()
            .filter_map(|arm| Self::constructor_pattern_name(&arm.pattern))
            .map(short_constructor_name)
            .collect();
        if arm_ctors.is_empty() {
            return None;
        }

        Some(dt.constructors.iter().all(|ctor| {
            // #prophecy-slots (Fix B M1/M2): same alias-awareness as
            // `datatype_matches_arms` — a `{family}__Some` constructor is
            // covered by an arm whose pattern says `Some`. Without this the
            // specialized family reads as NON-exhaustive and the match is
            // rejected outright.
            arm_ctors.contains(&short_constructor_name(&ctor.name))
                || arm_ctors
                    .iter()
                    .any(|arm_ctor| super::datatype_constructor_matches(&dt, &ctor.name, arm_ctor))
        }))
    }

    /// Check exhaustiveness for tuple-pattern matches (#1703).
    ///
    /// Collects per-position constructor name sets from `Tuple` arms, computes
    /// the cross product (capped at 256 combinations to avoid blowup), and
    /// verifies that every combination is matched by at least one arm via
    /// wildcard/binding/constructor matching.
    ///
    /// Phase 3 (B2): also recognizes bool literal patterns at tuple positions
    /// as the two-element "small finite type" bool. A position is treated as
    /// covered iff both `true` and `false` literal arms appear (or a wildcard
    /// fills in). This keeps the encoding sound — the cross product still
    /// enumerates every combination explicitly.
    fn check_tuple_exhaustive(arms: &[MatchArm]) -> bool {
        let tuple_arms: Vec<&[Pattern]> = arms
            .iter()
            .filter_map(|arm| Self::tuple_pattern_elements(&arm.pattern))
            .collect();

        if tuple_arms.is_empty() {
            return false;
        }

        let arity = tuple_arms[0].len();
        if arity == 0 || tuple_arms.iter().any(|p| p.len() != arity) {
            return false;
        }

        let mut per_position_ctors: Vec<Vec<String>> = vec![vec![]; arity];
        // Track which positions have any bool literal pattern observed. When a
        // bool literal appears at a position, we force-add both bool sentinels
        // so the cross product enumerates both `true` and `false` — making the
        // soundness argument structural rather than depending on source-level
        // Rust exhaustiveness for the bool-extension cases.
        let mut bool_positions: Vec<bool> = vec![false; arity];
        for pats in &tuple_arms {
            for (i, pat) in pats.iter().enumerate() {
                if let Some(name) = Self::constructor_pattern_name(pat) {
                    let short = short_constructor_name(name).to_owned();
                    if !per_position_ctors[i].contains(&short) {
                        per_position_ctors[i].push(short);
                    }
                } else if Self::bool_literal_sentinel(pat).is_some() {
                    bool_positions[i] = true;
                }
            }
        }

        for (i, ctors) in per_position_ctors.iter_mut().enumerate() {
            if bool_positions[i] {
                // Force-add both bool sentinels so the cross product enumerates
                // every bool value at this position, regardless of which were
                // observed in the arms. This makes the check fail-closed (it
                // returns false unless both true and false are matched by some
                // arm at that position, possibly via a wildcard).
                if !ctors.iter().any(|c| c == BOOL_TRUE_SENTINEL) {
                    ctors.push(BOOL_TRUE_SENTINEL.to_owned());
                }
                if !ctors.iter().any(|c| c == BOOL_FALSE_SENTINEL) {
                    ctors.push(BOOL_FALSE_SENTINEL.to_owned());
                }
            }
            if ctors.is_empty() {
                ctors.push("__wildcard__".to_owned());
            }
        }

        Self::cross_product_covered(&per_position_ctors, &tuple_arms)
    }

    /// Return the bool-literal sentinel name for a bool literal pattern.
    ///
    /// Returns `Some(BOOL_TRUE_SENTINEL)` for `Pattern::Literal(Bool(true))`,
    /// `Some(BOOL_FALSE_SENTINEL)` for `Pattern::Literal(Bool(false))`, and
    /// `None` for any other pattern. Alias wrappers are peeled.
    fn bool_literal_sentinel(pattern: &Pattern) -> Option<&'static str> {
        match Self::peel_alias_pattern(pattern) {
            Pattern::Literal(PureExpr::Bool(true)) => Some(BOOL_TRUE_SENTINEL),
            Pattern::Literal(PureExpr::Bool(false)) => Some(BOOL_FALSE_SENTINEL),
            _ => None,
        }
    }

    /// Check that every combination in the cross product of per-position
    /// constructor sets is matched by at least one tuple arm.
    /// Returns `false` if the cross product exceeds 256 combinations.
    fn cross_product_covered(
        per_position_ctors: &[Vec<String>],
        tuple_arms: &[&[Pattern]],
    ) -> bool {
        let arity = per_position_ctors.len();
        let total_combos: usize = per_position_ctors.iter().map(Vec::len).product();
        if total_combos > 256 {
            return false;
        }

        let mut indices = vec![0usize; arity];
        for _ in 0..total_combos {
            let combo: Vec<&str> = (0..arity)
                .map(|pos| per_position_ctors[pos][indices[pos]].as_str())
                .collect();

            let matched = tuple_arms.iter().any(|pats| {
                pats.iter()
                    .zip(combo.iter())
                    .all(|(pat, ctor_name)| Self::pattern_matches_constructor(pat, ctor_name))
            });

            if !matched {
                return false;
            }

            let mut carry = true;
            for pos in (0..arity).rev() {
                if carry {
                    indices[pos] += 1;
                    if indices[pos] >= per_position_ctors[pos].len() {
                        indices[pos] = 0;
                    } else {
                        carry = false;
                    }
                }
            }
        }

        true
    }

    /// Check whether a single pattern matches a given constructor name.
    /// Wildcards and bindings match any constructor.
    ///
    /// Bool literal patterns match their corresponding sentinel
    /// (`BOOL_TRUE_SENTINEL` / `BOOL_FALSE_SENTINEL`) and nothing else.
    fn pattern_matches_constructor(pattern: &Pattern, ctor_name: &str) -> bool {
        match pattern {
            Pattern::Wildcard | Pattern::Binding(_) => true,
            Pattern::Constructor { name, .. } => short_constructor_name(name) == ctor_name,
            Pattern::Alias { pattern, .. } => Self::pattern_matches_constructor(pattern, ctor_name),
            Pattern::Literal(PureExpr::Bool(true)) => ctor_name == BOOL_TRUE_SENTINEL,
            Pattern::Literal(PureExpr::Bool(false)) => ctor_name == BOOL_FALSE_SENTINEL,
            Pattern::Tuple(_) | Pattern::Literal(_) => false,
            // Pattern is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
            _ => false,
        }
    }

    fn constructor_pattern_name(pattern: &Pattern) -> Option<&str> {
        match pattern {
            Pattern::Constructor { name, .. } => Some(name),
            Pattern::Alias { pattern, .. } => Self::constructor_pattern_name(pattern),
            _ => None,
        }
    }

    fn tuple_pattern_elements(pattern: &Pattern) -> Option<&[Pattern]> {
        match pattern {
            Pattern::Tuple(patterns) => Some(patterns.as_slice()),
            Pattern::Alias { pattern, .. } => Self::tuple_pattern_elements(pattern),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField};
    use trust_wp_core::formula::{MatchArm, PureExpr};

    use super::*;
    use crate::encoder::sort_context::register_adt_family_alias;

    fn registered_list_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "List".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Cons".to_string(),
                    fields: vec![
                        DatatypeField {
                            name: "list_cons_0".to_string(),
                            sort: Sort::Int,
                        },
                        DatatypeField {
                            name: "list_cons_1".to_string(),
                            sort: Sort::Uninterpreted("List".to_string()),
                        },
                    ],
                },
                DatatypeConstructor {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
            ],
        }
    }

    fn synthesized_list_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "Adt_Cons_Nil".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Cons".to_string(),
                    fields: vec![
                        DatatypeField {
                            name: "adt_cons_nil_cons_0".to_string(),
                            sort: Sort::Int,
                        },
                        DatatypeField {
                            name: "adt_cons_nil_cons_1".to_string(),
                            sort: Sort::Int,
                        },
                    ],
                },
                DatatypeConstructor {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
            ],
        }
    }

    fn qualified_constructor_list_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "List".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "List::Nil".to_string(),
                    fields: vec![],
                },
                DatatypeConstructor {
                    name: "List::Cons".to_string(),
                    fields: vec![
                        DatatypeField {
                            name: "list_cons_0".to_string(),
                            sort: Sort::Int,
                        },
                        DatatypeField {
                            name: "list_cons_1".to_string(),
                            sort: Sort::Uninterpreted("List".to_string()),
                        },
                    ],
                },
            ],
        }
    }

    #[test]
    fn exhaustive_match_accepts_qualified_registered_constructor_names() {
        let arms = vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Nil".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("head".to_string()),
                        Pattern::Binding("tail".to_string()),
                    ]))),
                },
                body: PureExpr::Var("head".to_string(), None),
            },
        ];

        assert!(
            AYEncoder::is_constructor_exhaustive(
                &arms,
                Some(&qualified_constructor_list_datatype())
            ),
            "qualified registered constructor names should compare by short constructor name"
        );
    }

    #[test]
    fn inferred_qualified_match_uses_registered_field_sorts_when_synthetic_alias_exists() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&registered_list_datatype());
        encoder.ensure_datatype_declared(&synthesized_list_datatype());
        register_adt_family_alias("Adt_Cons_Nil", "List");

        let arms = vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("head".to_string()),
                        Pattern::Binding("tail".to_string()),
                    ]))),
                },
                body: PureExpr::Var("tail".to_string(), None),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Nil".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
        ];

        let datatype = encoder
            .match_datatype(&PureExpr::Var("self".to_string(), None), &arms, None)
            .expect("List match should infer a datatype");
        let cons = datatype
            .constructors
            .iter()
            .find(|ctor| ctor.name == "Cons")
            .expect("List datatype should contain Cons");

        assert_eq!(datatype.name, "List");
        assert_eq!(cons.fields[1].name, "list_cons_1");
        assert_eq!(cons.fields[1].sort, Sort::Uninterpreted("List".to_string()));
    }

    #[test]
    fn exhaustive_match_accepts_bool_literal_arms() {
        // `match cond { false => ..., true => ... }` is exhaustive over bool
        // even when no native DatatypeSort is declared for bool.
        let arms = vec![
            MatchArm {
                pattern: Pattern::Literal(PureExpr::Bool(false)),
                body: PureExpr::Int(0),
            },
            MatchArm {
                pattern: Pattern::Literal(PureExpr::Bool(true)),
                body: PureExpr::Int(1),
            },
        ];

        assert!(
            AYEncoder::is_constructor_exhaustive(&arms, None),
            "match over bool with both literal arms should be exhaustive"
        );

        // Reversed order should also be exhaustive.
        let arms_swapped = vec![
            MatchArm {
                pattern: Pattern::Literal(PureExpr::Bool(true)),
                body: PureExpr::Int(1),
            },
            MatchArm {
                pattern: Pattern::Literal(PureExpr::Bool(false)),
                body: PureExpr::Int(0),
            },
        ];
        assert!(
            AYEncoder::is_constructor_exhaustive(&arms_swapped, None),
            "match over bool should be exhaustive regardless of arm order"
        );
    }

    #[test]
    fn bool_match_missing_arm_is_not_exhaustive() {
        // Only `true`, no `false` arm: not exhaustive over bool.
        let arms = vec![MatchArm {
            pattern: Pattern::Literal(PureExpr::Bool(true)),
            body: PureExpr::Int(1),
        }];
        assert!(!AYEncoder::is_constructor_exhaustive(&arms, None));
    }

    // ---- Phase 3 (B2): small finite type tests ----

    #[test]
    fn exhaustive_match_accepts_unit_pattern() {
        // `match () { () => ... }` is exhaustive: the unit type has exactly
        // one inhabitant, so a single `()` arm covers all possible values.
        let arms = vec![MatchArm {
            pattern: Pattern::Tuple(vec![]),
            body: PureExpr::Int(0),
        }];
        assert!(
            AYEncoder::is_constructor_exhaustive(&arms, None),
            "match over () with a unit-tuple arm should be exhaustive"
        );
    }

    #[test]
    fn exhaustive_match_accepts_unit_pattern_with_alias() {
        // `match () { x @ () => ... }` is still a single unit-tuple arm.
        let arms = vec![MatchArm {
            pattern: Pattern::Alias {
                alias: "x".to_string(),
                pattern: Box::new(Pattern::Tuple(vec![])),
            },
            body: PureExpr::Int(0),
        }];
        assert!(
            AYEncoder::is_constructor_exhaustive(&arms, None),
            "aliased unit-tuple arm should still be recognized as exhaustive"
        );
    }

    #[test]
    fn unit_check_rejects_non_unit_tuple_arms() {
        // Empty arm list (zero `()` arms seen) must NOT be exhaustive.
        let arms: Vec<MatchArm> = vec![];
        assert!(
            !AYEncoder::check_unit_pattern_exhaustive(&arms),
            "empty arm list must not be classified as unit-exhaustive"
        );

        // A non-empty tuple arm does NOT make a unit-exhaustive case.
        let arms = vec![MatchArm {
            pattern: Pattern::Tuple(vec![Pattern::Wildcard]),
            body: PureExpr::Int(0),
        }];
        assert!(
            !AYEncoder::check_unit_pattern_exhaustive(&arms),
            "arity-1 tuple arm is not the unit type"
        );
    }

    #[test]
    fn exhaustive_match_accepts_bool_tuple_full_cross_product() {
        // match (a, b) { (true,true)=>0, (true,false)=>1, (false,true)=>2, (false,false)=>3 }
        let arms = vec![
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Literal(PureExpr::Bool(true)),
                ]),
                body: PureExpr::Int(0),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Literal(PureExpr::Bool(false)),
                ]),
                body: PureExpr::Int(1),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(false)),
                    Pattern::Literal(PureExpr::Bool(true)),
                ]),
                body: PureExpr::Int(2),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(false)),
                    Pattern::Literal(PureExpr::Bool(false)),
                ]),
                body: PureExpr::Int(3),
            },
        ];
        assert!(
            AYEncoder::is_constructor_exhaustive(&arms, None),
            "all four (bool, bool) combinations should be exhaustive"
        );
    }

    #[test]
    fn bool_tuple_with_wildcard_position_is_exhaustive() {
        // match (a, b) { (true, _) => 0, (false, _) => 1 } — exhaustive even
        // though position 1 has only wildcards.
        let arms = vec![
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Wildcard,
                ]),
                body: PureExpr::Int(0),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(false)),
                    Pattern::Wildcard,
                ]),
                body: PureExpr::Int(1),
            },
        ];
        assert!(
            AYEncoder::is_constructor_exhaustive(&arms, None),
            "bool first position covered + wildcard second position should be exhaustive"
        );
    }

    #[test]
    fn bool_tuple_missing_combination_is_not_exhaustive() {
        // match (a, b) { (true,true)=>0, (true,false)=>1, (false,true)=>2 }
        // Missing (false, false) — must NOT be classified as exhaustive.
        let arms = vec![
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Literal(PureExpr::Bool(true)),
                ]),
                body: PureExpr::Int(0),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Literal(PureExpr::Bool(false)),
                ]),
                body: PureExpr::Int(1),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(false)),
                    Pattern::Literal(PureExpr::Bool(true)),
                ]),
                body: PureExpr::Int(2),
            },
        ];
        assert!(
            !AYEncoder::is_constructor_exhaustive(&arms, None),
            "missing (false, false) combo should not be classified as exhaustive"
        );
    }

    #[test]
    fn bool_tuple_with_constructor_position_is_exhaustive() {
        // match (b, opt) { (true, Some(_))=>0, (true, None)=>1,
        //                  (false, Some(_))=>2, (false, None)=>3 }
        let arms = vec![
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Wildcard)),
                    },
                ]),
                body: PureExpr::Int(0),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                ]),
                body: PureExpr::Int(1),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(false)),
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Wildcard)),
                    },
                ]),
                body: PureExpr::Int(2),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(false)),
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                ]),
                body: PureExpr::Int(3),
            },
        ];
        assert!(
            AYEncoder::is_constructor_exhaustive(&arms, None),
            "(bool, Option) cross product fully covered should be exhaustive"
        );
    }

    #[test]
    fn bool_tuple_missing_only_one_bool_value_is_not_exhaustive() {
        // match (a, b) { (true, true) => 0, (true, false) => 1 }
        // The bool-literal extension forces enumeration of BOTH `true` and
        // `false` at every position where any bool literal is observed.
        // Position 0 only sees `true`, but the extension still adds the
        // `false` sentinel, so the cross product enumerates `(false, true)`
        // and `(false, false)` — neither of which has a matching arm. This
        // makes the extension fail-closed and gives a structural soundness
        // argument independent of Rust's source-level exhaustiveness check.
        let arms = vec![
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Literal(PureExpr::Bool(true)),
                ]),
                body: PureExpr::Int(0),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Literal(PureExpr::Bool(false)),
                ]),
                body: PureExpr::Int(1),
            },
        ];
        assert!(
            !AYEncoder::is_constructor_exhaustive(&arms, None),
            "missing all `false`-first combinations: the bool extension must \
             enumerate both bool values at position 0 and detect the gap"
        );
    }

    #[test]
    fn bool_tuple_only_one_bool_value_with_constructor_position_is_not_exhaustive() {
        // match (b, opt) { (true, Some(_)) => 0, (true, None) => 1 }
        // Position 0 observes only `true`; extension forces `false` too, but
        // no arm matches `false` at position 0 → not exhaustive.
        let arms = vec![
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Wildcard)),
                    },
                ]),
                body: PureExpr::Int(0),
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Literal(PureExpr::Bool(true)),
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                ]),
                body: PureExpr::Int(1),
            },
        ];
        assert!(
            !AYEncoder::is_constructor_exhaustive(&arms, None),
            "missing `false`-first arms should not be classified as exhaustive"
        );
    }

    /// A bare `__trust_wp_tuple_get_I(t)` scrutinee (what the open-logic-fn
    /// inliner leaves behind when it rewrites `sum(get_1(t))` into a `Match`
    /// over `sum`'s body) must resolve its datatype from the ARMS, and the
    /// preseed must then declare the getter placeholder at that sort instead
    /// of the `Int` default. (#getters2)
    #[test]
    fn tuple_getter_match_scrutinee_resolves_arm_datatype_and_preseeds_getter_sort() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&registered_list_datatype());
        let tuple2 = Sort::Uninterpreted("Tuple2".to_string());
        encoder
            .get_or_declare_var("t", tuple2.clone())
            .expect("declare Tuple2 receiver var");

        let scrutinee = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_1".to_string(),
            args: vec![PureExpr::Var("t".to_string(), None)],
        };
        let arms = vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("head".to_string()),
                        Pattern::Binding("tail".to_string()),
                    ]))),
                },
                body: PureExpr::Var("head".to_string(), None),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Nil".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
        ];

        let datatype = encoder
            .match_datatype(&scrutinee, &arms, None)
            .expect("tuple-getter scrutinee should infer the arms' datatype");
        assert_eq!(datatype.name, "List");

        encoder.preseed_tuple_getter_placeholder_for_match_scrutinee(
            &scrutinee,
            Some(&datatype),
            None,
        );

        let getter_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_1");
        let resolved = encoder
            .existing_placeholder_return_sort(&getter_smt, std::slice::from_ref(&tuple2))
            .expect("preseed should declare a getter placeholder over the Tuple2 carrier");
        assert_ne!(
            resolved,
            Sort::Int,
            "the getter must not keep the Int default once the arms name a datatype"
        );
        assert_eq!(
            resolved.as_term_sort(),
            Sort::Uninterpreted("List".to_string()).as_term_sort(),
            "the preseeded getter must carry the arms' List sort"
        );
    }
}
