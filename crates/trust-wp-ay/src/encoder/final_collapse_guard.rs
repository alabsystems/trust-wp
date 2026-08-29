// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort-aware fail-closed guard on the `Final`-collapse routes (Fix A of the
//! Final-collapse soundness audit, 2026-08-05).
//!
//! Collapsing `Final(x)` (`^x`) to the same carrier as `x`/`*x` is exact only
//! when the carrier's sort embeds no mutable reference: a pure value has no
//! temporal state, so its "final" value IS its value. For carriers that embed
//! a `&mut` (a match binder over an `Option<&mut T>` payload, an ADT field
//! holding `&mut`, a tuple with a `&mut` component), no prophecy slot exists
//! in the collapsed encoding and the collapse silently asserts the inversion
//! `^x == *x` — the load-bearing false lemma behind the adjudicated
//! take_first_mut false accept (memory/final-collapse-audit.md).
//!
//! This module provides the transitive `sort_embeds_mut_ref` predicate and
//! the single refusal helper. The predicate is FAIL-CLOSED: unknown or
//! unresolvable sorts (no annotation, undeclared datatypes, opaque tuples,
//! type parameters in carrier position) are treated as embedding — refusing an
//! exact collapse costs an honest Unknown; permitting an inexact one is a
//! false proof.
//!
//! Generic-ADT refinement (guardref): a decl field whose sort is an
//! UNSUBSTITUTED `ExprSort::TypeParam` is NOT embedding evidence. Decls are
//! built per verified `DefId` with that function's `substs` already applied,
//! so a `TypeParam` field only survives where the enclosing function is itself
//! generic over the parameter — a position with no prophecy carrier to invert.
//! Every concrete `&mut` instantiation lowers to a `Ref(_)` field in the
//! instantiating function's own decl and stays fail-closed there. Without this
//! refinement `partially_opaque::f<A, B>(x: S<A, B>)` refused on
//! `Datatype(m::S)` whose only fields are `TypeParam(A)`/`TypeParam(B)`.
//!
//! Decl-level mutability fidelity (#prophecy-slots, Fix B M1 — blueprint C1):
//! rustc-backed `AdtDecl` field sorts now PRESERVE mutability
//! (`ty_to_adt_decl_sort` maps `&mut T` to `ExprSort::MutRef` and `&T` to
//! `ExprSort::Ref`), so a decl-level `Ref` genuinely means a shared
//! reference and recurses into its referent exactly like an expression-level
//! annotation. Before C1 both mutabilities erased to `Ref` and every
//! reference-typed decl field had to count as embedding (the conservative
//! `AdtField => true` arm this commit retires).

use std::collections::HashSet;

use trust_wp_core::formula::{resolve_sort_name, ExprSort, PureExpr};

use super::{
    sort_context::sort_mapping::{canonical_sort, CanonicalSort},
    unsoundness, AYEncoder,
};
use crate::error::EncodingError;

/// Marker prefix of the dedicated mut-ref carrier record sort
/// (`__trust_wp_mutref::<inner>`), which round-trips through
/// `ExprSort::Datatype` interning when re-derived from an ay `Sort`.
const MUTREF_RECORD_SORT_PREFIX: &str = "__trust_wp_mutref::";

/// Whether the position being classified is an expression-level annotation
/// (which distinguishes `Ref` from `MutRef`) or a declared-ADT field sort
/// (where rustc-backed decls erase mutability, so every `Ref` is suspect).
#[derive(Clone, Copy, PartialEq, Eq)]
enum SortPosition {
    Annotation,
    AdtField,
}

impl AYEncoder {
    /// Transitive fail-closed check: does `sort` (possibly) embed a mutable
    /// reference?
    ///
    /// - `MutRef(_)` and the `__trust_wp_mutref::*` record sort: **true**.
    /// - Pure value sorts (`Int`, `Bool`, `Seq`, `Unit`, `FMap`, `Float`):
    ///   **false**.
    /// - `Ref(inner)`: recurse into the referent (both positions — decls
    ///   preserve mutability since C1, #prophecy-slots M1).
    /// - `Datatype(name)`: value-model canonical names (Seq/FMap/Mapping/Int
    ///   models) are **false**; otherwise look the name up in the rustc-backed
    ///   ADT decl registry and recurse into every constructor field sort. A name
    ///   with no registered decl is unresolvable: **true** (fail-closed).
    /// - `Tuple(_)`: component sorts are not carried by `ExprSort::Tuple`:
    ///   **true** (fail-closed).
    /// - `TypeParam(_)`: in carrier/annotation position the instantiation is
    ///   unknown: **true** (fail-closed). As a DECL FIELD it is an
    ///   unsubstituted ADT generic parameter in a generic function's own
    ///   registry — no prophecy carrier exists to invert: **false**
    ///   (guardref refinement; see the module docs).
    /// - Any future variant: **true** (fail-closed).
    ///
    /// Recursive ADTs are handled with a seen-set: revisiting a datatype
    /// yields no NEW embedding evidence, so the cycle edge contributes false.
    pub(crate) fn sort_embeds_mut_ref(&self, sort: &ExprSort) -> bool {
        let mut seen = HashSet::new();
        self.sort_embeds_mut_ref_inner(sort, SortPosition::Annotation, &mut seen)
    }

    fn sort_embeds_mut_ref_inner(
        &self,
        sort: &ExprSort,
        position: SortPosition,
        seen: &mut HashSet<u32>,
    ) -> bool {
        match sort {
            ExprSort::MutRef(_) => true,
            ExprSort::Int
            | ExprSort::Bool
            | ExprSort::Seq
            | ExprSort::Unit
            | ExprSort::FMap
            | ExprSort::Float => false,
            // `Ref` is genuinely shared (`&T`) at BOTH positions since C1
            // (#prophecy-slots M1): decl field sorts preserve mutability, so
            // an erased `&mut` can no longer hide under a decl-level `Ref`.
            // A shared reference to an embedding payload is still
            // conservatively embedding via the recursion (CELL_SET-shaped
            // R3-Ref inversions).
            ExprSort::Ref(inner) => self.sort_embeds_mut_ref_inner(inner, position, seen),
            ExprSort::Datatype(id) => {
                let name = resolve_sort_name(*id);
                if name.starts_with(MUTREF_RECORD_SORT_PREFIX) {
                    return true;
                }
                // Value-model canonical types (Vec/Seq -> Seq, HashMap ->
                // FMap, Rc/Arc/Box/Snapshot/... -> Int, Mapping) erase to
                // value semantics at this layer; any `&mut`-ness would be
                // carried by an enclosing MutRef annotation instead.
                match canonical_sort(&name) {
                    CanonicalSort::Seq
                    | CanonicalSort::FMap
                    | CanonicalSort::Mapping
                    | CanonicalSort::Int => return false,
                    CanonicalSort::Uninterpreted(_) => {}
                }
                if !seen.insert(*id) {
                    // Cycle: this datatype is already being examined; the
                    // back-edge itself adds no new embedding evidence.
                    return false;
                }
                match self.adt_decl_for_name(&name) {
                    Some(decl) => {
                        let decl = decl.clone();
                        decl.constructors.iter().any(|ctor| {
                            ctor.fields.iter().any(|field| {
                                self.sort_embeds_mut_ref_inner(
                                    &field.sort,
                                    SortPosition::AdtField,
                                    seen,
                                )
                            })
                        })
                    }
                    // Unresolvable datatype — fail-closed.
                    None => true,
                }
            }
            // ExprSort::Tuple(arity) carries no component sorts — fail-closed.
            ExprSort::Tuple(_) => true,
            ExprSort::TypeParam(_) => match position {
                // Annotation-level: the collapsed carrier ITSELF is of an
                // unknown instantiated type — fail-closed.
                SortPosition::Annotation => true,
                // Decl-field level: the field is an UNSUBSTITUTED generic
                // parameter of the ADT *in the currently-verified function's
                // own decl registry* (`build_adt_decls` is per-`DefId` and
                // substitutes `substs` into every field type, so a `TypeParam`
                // field can only arise where the enclosing function is itself
                // generic over that parameter).
                //
                // Sound because every CONCRETE `&mut` instantiation is still
                // fail-closed where it can actually bite: since C1
                // (#prophecy-slots M1) rustc lowers `S<&mut i32, B>` to a
                // decl whose field sort is `MutRef(Int)`
                // (`ty_to_adt_decl_sort` preserves mutability), which the
                // `MutRef` arm above treats as embedding. So the function
                // that owns the real prophecy carrier — the instantiating
                // caller, or the monomorphic definition — keeps refusing. In
                // the generic definition there is no prophecy slot to
                // invert: a `TypeParam`-sorted subterm is an opaque
                // uninterpreted value whose `resolve` is encoded as an
                // uninterpreted predicate, never as `^ == *`.
                // (partially_opaque::f, guardref)
                SortPosition::AdtField => false,
            },
            // ExprSort is #[non_exhaustive]; future variants — fail-closed.
            #[allow(unreachable_patterns)]
            _ => true,
        }
    }

    /// Guard predicate for the `Final`-collapse fast paths: `true` when the
    /// carrier annotation embeds (or cannot be proven not to embed) a mutable
    /// reference, so collapsing `^x` to the current-value carrier would be
    /// the prophecy inversion. A missing annotation is unknown — fail-closed.
    pub(crate) fn final_collapse_requires_prophecy(&self, ann: Option<&ExprSort>) -> bool {
        match ann {
            Some(sort) => self.sort_embeds_mut_ref(sort),
            None => true,
        }
    }

    /// The single fail-closed refusal outcome for a guarded `Final` collapse.
    ///
    /// Increments the demoting [`unsoundness::UnsoundnessCategory::FinalCollapseRefused`]
    /// counter (defense-in-depth: demotion fires even if an intermediate layer
    /// absorbs the error) and returns the `EncodingError` that the caller must
    /// propagate. Premise-side this lands in the existing assumption-drop /
    /// requires-error lane (honest Unknown/error); goal-side it is an honest
    /// obligation failure. It must NEVER be converted into a collapsed term.
    pub(crate) fn refuse_final_collapse(
        &self,
        var_name: &str,
        ann: Option<&ExprSort>,
    ) -> EncodingError {
        unsoundness::increment(unsoundness::UnsoundnessCategory::FinalCollapseRefused);
        let ann_desc = ann.map_or_else(|| "<unannotated>".to_string(), ToString::to_string);
        EncodingError::unsupported(format!(
            "final-collapse refused (fail-closed): `^{var_name}` on a carrier whose sort \
             ({ann_desc}) embeds (or may embed) a mutable reference has no prophecy slot \
             in the collapsed encoding; collapsing would assert the false equality \
             `^{var_name} == *{var_name}` (Final-collapse audit Fix A)"
        ))
    }

    /// Fail-closed refusal for a prophecy applied to a CONSTANT carrier
    /// (Fix A, constant-carrier arm — tract19).
    ///
    /// The sort-based guard above cannot see this shape: a literal's sort is
    /// `Int`/`Bool`/`Float`, all of which `sort_embeds_mut_ref` classifies as
    /// pure values, so the collapse was permitted and
    /// `encode_wrapper_rewrite`'s "wrappers are no-ops on literals" arm folded
    /// `^3` to `3`. That is the same `^x == *x` inversion, and it was a LIVE
    /// false accept (see the call site in `pure_encoding/wrapper.rs` for the
    /// eight-line reproducer).
    ///
    /// A constant records the borrowed place's value in the CURRENT state and
    /// carries no identity, so there is nothing for a prophecy to name. Refuse
    /// instead of collapsing; the counter fires for demotion as
    /// defense-in-depth, exactly as for the sort-based sibling.
    pub(crate) fn refuse_prophecy_over_constant(&self, carrier: &PureExpr) -> EncodingError {
        unsoundness::increment(unsoundness::UnsoundnessCategory::FinalCollapseRefused);
        EncodingError::unsupported(format!(
            "final-collapse refused (fail-closed): `^{carrier:?}` applies a prophecy to a \
             constant carrier, which records the borrowed place's CURRENT value and has no \
             prophecy slot; folding the wrapper away would assert the false equality \
             `^p == *p` (Final-collapse audit Fix A, constant-carrier arm)"
        ))
    }
}

/// Whether a `Final`-collapse carrier annotation denotes a value-model
/// CONTAINER that genuinely has post-state (`Seq` / `FMap` / `Mapping`).
///
/// These are the ghost containers (`Seq::new()`, `FMap`, `Mapping`) that
/// pearlite mutates through `&mut self` ghost methods (`push_front_ghost`,
/// `insert_ghost`, ...). Their `^s` is a real, distinct post-state value.
///
/// The distinction matters because the SAME carrier reaches the Phase-1b
/// `Final` collapse under two different `ExprSort` spellings:
///   * `ExprSort::Seq` / `ExprSort::FMap` — never matched the
///     `Datatype(_) | Ref(_)` arm, so they already kept a distinct final
///     variable (the documented intent, #2675/#2700);
///   * `ExprSort::Datatype(creusot_std::Seq)` — the spelling the driver
///     actually emits for a ghost `Seq` local once the `&mut` has been peeled
///     to the referent. This DID match the arm, and `sort_embeds_mut_ref`
///     short-circuits every value-model canonical name to `false`, so the
///     Fix A refusal never fired either. The collapse then asserted
///     `^s == s`, contradicting the mutation premise `^s == s.push_front(v)`
///     and manufacturing a contradictory (vacuous) base.
///
/// `true` here means "decline the fast-path collapse"; the general Phase-2
/// naming path mints the distinct `s_final` carrier at the same sort. That is
/// strictly WEAKER than collapsing — it removes an equality premise, it never
/// adds one — so it cannot turn an honest Unknown into a proof.
///
/// Deliberately NOT included:
/// * `CanonicalSort::Int` (Box/Rc/Arc/Snapshot/Ghost value-model wrappers) —
///   these are the pointer-transparent wrappers whose `Final` collapse the
///   Box-reborrow lane (Phase 1d, `bug/final_borrows`) relies on.
/// * `ExprSort::Ref(_)` — an annotation-level shared reference is an
///   immutable read; expression annotations distinguish `Ref` from `MutRef`,
///   so a genuinely mutable carrier arrives as `MutRef(_)` (already excluded
///   from this arm) or as the peeled referent handled above.
pub(crate) fn expr_sort_is_post_state_container(ann: &ExprSort) -> bool {
    match ann {
        ExprSort::Seq | ExprSort::FMap => true,
        ExprSort::Datatype(id) => matches!(
            canonical_sort(&resolve_sort_name(*id)),
            CanonicalSort::Seq | CanonicalSort::FMap | CanonicalSort::Mapping
        ),
        _ => false,
    }
}

/// Registry-free syntactic variant of the guard predicate for layers without
/// encoder access (the goal-side option-match shortcuts in
/// `verify/postcondition.rs`). Datatypes that are not value-model canonical
/// names cannot be resolved here — fail-closed `true`. Declining a shortcut
/// only costs the fast path: the general encoding path re-examines the same
/// expression with the full registry-aware guard.
pub(crate) fn expr_sort_may_embed_mut_ref_syntactic(ann: Option<&ExprSort>) -> bool {
    match ann {
        None => true,
        Some(sort) => match sort {
            ExprSort::MutRef(_) => true,
            ExprSort::Int
            | ExprSort::Bool
            | ExprSort::Seq
            | ExprSort::Unit
            | ExprSort::FMap
            | ExprSort::Float => false,
            ExprSort::Ref(inner) => expr_sort_may_embed_mut_ref_syntactic(Some(inner)),
            ExprSort::Datatype(id) => {
                let name = resolve_sort_name(*id);
                if name.starts_with(MUTREF_RECORD_SORT_PREFIX) {
                    return true;
                }
                !matches!(
                    canonical_sort(&name),
                    CanonicalSort::Seq
                        | CanonicalSort::FMap
                        | CanonicalSort::Mapping
                        | CanonicalSort::Int
                )
            }
            ExprSort::Tuple(_) | ExprSort::TypeParam(_) => true,
            #[allow(unreachable_patterns)]
            _ => true,
        },
    }
}

#[cfg(test)]
mod tests {
    use ntest::timeout;
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtDecls, AdtFieldDecl, AdtKind},
    };

    use super::*;

    fn encoder_with_decls(decls: AdtDecls) -> AYEncoder {
        let mut encoder = AYEncoder::new();
        encoder.register_adt_decls(&decls);
        encoder
    }

    fn struct_decl(name: &str, fields: Vec<AdtFieldDecl>) -> AdtDecl {
        AdtDecl::new(
            name.to_string(),
            name.to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                name.to_string(),
                name.to_string(),
                fields,
            )],
        )
    }

    #[test]
    #[timeout(10000)]
    fn mut_ref_and_pure_scalars_classify_directly() {
        let encoder = AYEncoder::new();
        assert!(encoder.sort_embeds_mut_ref(&ExprSort::MutRef(Box::new(ExprSort::Int))));
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Int));
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Bool));
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Seq));
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::FMap));
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Unit));
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Float));
        // Shared ref to a pure scalar stays collapsible.
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Ref(Box::new(ExprSort::Int))));
        // Shared ref WRAPPING a mut ref embeds transitively.
        assert!(
            encoder.sort_embeds_mut_ref(&ExprSort::Ref(Box::new(ExprSort::MutRef(Box::new(
                ExprSort::Int
            )))))
        );
    }

    #[test]
    #[timeout(10000)]
    fn unknowns_are_fail_closed() {
        let encoder = AYEncoder::new();
        // Undeclared datatype: unresolvable — embeds.
        assert!(
            encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("SomeUndeclaredAdt")))
        );
        // Tuples carry no component sorts — embeds.
        assert!(encoder.sort_embeds_mut_ref(&ExprSort::Tuple(2)));
        // A type parameter in CARRIER position has an unknown instantiation —
        // embeds (the guardref refinement relaxes decl FIELDS only).
        assert!(encoder.sort_embeds_mut_ref(&ExprSort::TypeParam(intern_sort_name("T"))));
        // ... including under a shared reference at annotation level.
        assert!(
            encoder.sort_embeds_mut_ref(&ExprSort::Ref(Box::new(ExprSort::TypeParam(
                intern_sort_name("T")
            ))))
        );
        // The dedicated mut-ref record sort name — embeds.
        assert!(
            encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name(
                "__trust_wp_mutref::int"
            )))
        );
        // Missing annotation — requires prophecy.
        assert!(encoder.final_collapse_requires_prophecy(None));
    }

    #[test]
    #[timeout(10000)]
    fn declared_pure_datatype_stays_collapsible() {
        let mut decls = AdtDecls::new();
        decls.insert(
            "PurePair".to_string(),
            struct_decl(
                "PurePair",
                vec![
                    AdtFieldDecl::new("a".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("b".to_string(), ExprSort::Bool),
                ],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("PurePair"))));
        assert!(
            !encoder.final_collapse_requires_prophecy(Some(&ExprSort::Datatype(intern_sort_name(
                "PurePair"
            ))))
        );
    }

    #[test]
    #[timeout(10000)]
    fn adt_embedded_mut_ref_is_transitive() {
        // Outer { inner: Inner }, Inner { r: &mut i32 } — embeds transitively.
        let mut decls = AdtDecls::new();
        decls.insert(
            "InnerHolder".to_string(),
            struct_decl(
                "InnerHolder",
                vec![AdtFieldDecl::new(
                    "r".to_string(),
                    ExprSort::MutRef(Box::new(ExprSort::Int)),
                )],
            ),
        );
        decls.insert(
            "OuterHolder".to_string(),
            struct_decl(
                "OuterHolder",
                vec![AdtFieldDecl::new(
                    "inner".to_string(),
                    ExprSort::Datatype(intern_sort_name("InnerHolder")),
                )],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(
            encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("OuterHolder"))),
            "ADT-embedded &mut must be found transitively"
        );
    }

    #[test]
    #[timeout(10000)]
    fn adt_decl_ref_field_recurses_since_c1() {
        // #prophecy-slots M1 (C1): decl field sorts preserve mutability, so a
        // decl-level `Ref` genuinely means `&T` and recurses. `&i32` is pure;
        // `&(&mut i32)` still embeds transitively.
        let mut decls = AdtDecls::new();
        decls.insert(
            "RefHolder".to_string(),
            struct_decl(
                "RefHolder",
                vec![AdtFieldDecl::new(
                    "r".to_string(),
                    ExprSort::Ref(Box::new(ExprSort::Int)),
                )],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(
            !encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("RefHolder"))),
            "a faithful decl-level shared-ref-to-pure field must stay collapsible"
        );

        let mut decls = AdtDecls::new();
        decls.insert(
            "RefMutHolder".to_string(),
            struct_decl(
                "RefMutHolder",
                vec![AdtFieldDecl::new(
                    "r".to_string(),
                    ExprSort::Ref(Box::new(ExprSort::MutRef(Box::new(ExprSort::Int)))),
                )],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(
            encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("RefMutHolder"))),
            "a shared ref WRAPPING a mut ref must still embed transitively"
        );
    }

    #[test]
    #[timeout(10000)]
    fn generic_adt_with_unsubstituted_params_stays_collapsible() {
        // `mod m { pub struct S<A, B> { pub a: A, b: B } }` as seen from the
        // GENERIC definition `f<A, B>(x: S<A, B>)`: rustc substitutes the
        // function's own params, so both fields stay `TypeParam`. No prophecy
        // carrier exists here — collapse stays exact. (partially_opaque::f)
        let mut decls = AdtDecls::new();
        decls.insert(
            "S".to_string(),
            struct_decl(
                "m::S",
                vec![
                    AdtFieldDecl::new("a".to_string(), ExprSort::TypeParam(intern_sort_name("A"))),
                    AdtFieldDecl::new("b".to_string(), ExprSort::TypeParam(intern_sort_name("B"))),
                ],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("m::S"))));
        assert!(!encoder
            .final_collapse_requires_prophecy(Some(&ExprSort::Datatype(intern_sort_name("m::S")))));
    }

    #[test]
    #[timeout(10000)]
    fn partly_substituted_generic_adt_stays_collapsible() {
        // As seen from `g<B>(x: &mut S<i32, B>)`: `a` is concretely `Int`,
        // `b` is still the unsubstituted `B`. Mutref-free either way.
        let mut decls = AdtDecls::new();
        decls.insert(
            "S".to_string(),
            struct_decl(
                "m::S",
                vec![
                    AdtFieldDecl::new("a".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("b".to_string(), ExprSort::TypeParam(intern_sort_name("B"))),
                ],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("m::S"))));
    }

    #[test]
    #[timeout(10000)]
    fn concrete_mut_ref_instantiation_of_a_generic_adt_still_refuses() {
        // The SAME `S<A, B>` instantiated at `S<&mut i32, B>`: since C1
        // (#prophecy-slots M1) rustc lowers the `&mut i32` field to
        // `MutRef(Int)` (mutability preserved at decl level), so the
        // instantiating function's registry keeps refusing. This is the
        // FA-side pin of the guardref refinement.
        let mut decls = AdtDecls::new();
        decls.insert(
            "S".to_string(),
            struct_decl(
                "m::S",
                vec![
                    AdtFieldDecl::new("a".to_string(), ExprSort::MutRef(Box::new(ExprSort::Int))),
                    AdtFieldDecl::new("b".to_string(), ExprSort::TypeParam(intern_sort_name("B"))),
                ],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("m::S"))));
    }

    #[test]
    #[timeout(10000)]
    fn generic_param_nested_under_an_adt_field_stays_collapsible() {
        // Outer { inner: Inner<T> }, Inner { v: T } — transitively pure.
        let mut decls = AdtDecls::new();
        decls.insert(
            "InnerGen".to_string(),
            struct_decl(
                "InnerGen",
                vec![AdtFieldDecl::new(
                    "v".to_string(),
                    ExprSort::TypeParam(intern_sort_name("T")),
                )],
            ),
        );
        decls.insert(
            "OuterGen".to_string(),
            struct_decl(
                "OuterGen",
                vec![AdtFieldDecl::new(
                    "inner".to_string(),
                    ExprSort::Datatype(intern_sort_name("InnerGen")),
                )],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("OuterGen"))));
        // ... but an undeclared nested datatype is still unresolvable.
        let mut decls = AdtDecls::new();
        decls.insert(
            "OuterGen".to_string(),
            struct_decl(
                "OuterGen",
                vec![AdtFieldDecl::new(
                    "inner".to_string(),
                    ExprSort::Datatype(intern_sort_name("NotDeclared")),
                )],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("OuterGen"))));
    }

    #[test]
    #[timeout(10000)]
    fn adt_tuple_field_stays_fail_closed() {
        // `ExprSort::Tuple` carries no component sorts — an unsubstituted
        // parameter relaxation must not leak into the tuple arm.
        let mut decls = AdtDecls::new();
        decls.insert(
            "TupleHolder".to_string(),
            struct_decl(
                "TupleHolder",
                vec![AdtFieldDecl::new("t".to_string(), ExprSort::Tuple(2))],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("TupleHolder"))));
    }

    #[test]
    #[timeout(10000)]
    fn recursive_pure_datatype_terminates_and_stays_collapsible() {
        // List { head: Int, tail: List } — recursive, no &mut anywhere.
        let mut decls = AdtDecls::new();
        decls.insert(
            "PureList".to_string(),
            struct_decl(
                "PureList",
                vec![
                    AdtFieldDecl::new("head".to_string(), ExprSort::Int),
                    AdtFieldDecl::new(
                        "tail".to_string(),
                        ExprSort::Datatype(intern_sort_name("PureList")),
                    ),
                ],
            ),
        );
        let encoder = encoder_with_decls(decls);
        assert!(!encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("PureList"))));
    }

    #[test]
    #[timeout(10000)]
    fn value_model_canonical_names_stay_collapsible() {
        let encoder = AYEncoder::new();
        for name in [
            "Vec", "Seq", "HashMap", "FMap", "Mapping", "Rc", "Arc", "Box", "Snapshot",
        ] {
            assert!(
                !encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name(name))),
                "value-model type {name} must not be treated as embedding"
            );
        }
    }

    #[test]
    #[timeout(10000)]
    fn syntactic_variant_matches_fail_closed_contract() {
        assert!(expr_sort_may_embed_mut_ref_syntactic(None));
        assert!(expr_sort_may_embed_mut_ref_syntactic(Some(
            &ExprSort::MutRef(Box::new(ExprSort::Int))
        )));
        assert!(!expr_sort_may_embed_mut_ref_syntactic(Some(&ExprSort::Int)));
        assert!(!expr_sort_may_embed_mut_ref_syntactic(Some(&ExprSort::Seq)));
        // No registry — datatypes are fail-closed unless value-model.
        assert!(expr_sort_may_embed_mut_ref_syntactic(Some(
            &ExprSort::Datatype(intern_sort_name("SomeUserAdt"))
        )));
        assert!(!expr_sort_may_embed_mut_ref_syntactic(Some(
            &ExprSort::Datatype(intern_sort_name("Vec"))
        )));
        assert!(expr_sort_may_embed_mut_ref_syntactic(Some(
            &ExprSort::Tuple(2)
        )));
    }

    #[test]
    #[timeout(10000)]
    fn refusal_increments_demoting_counter() {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        let encoder = AYEncoder::new();
        let err = encoder.refuse_final_collapse("r", None);
        assert!(matches!(err, EncodingError::Unsupported { .. }));
        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert_eq!(
            delta.get(&unsoundness::UnsoundnessCategory::FinalCollapseRefused),
            Some(&1),
            "refusal must fire the demoting FinalCollapseRefused counter"
        );
        assert!(
            unsoundness::UnsoundnessCategory::FinalCollapseRefused.is_demoting(),
            "FinalCollapseRefused must be demoting"
        );
        unsoundness::reset();
    }

    /// ★#124 pin: `Final` does not distribute into a method call's
    /// GROUND-CONSTANT arguments. An index/key was evaluated when the place
    /// was formed and has no temporal state — Creusot's projection rule is
    /// `^(s[i]) = (^s)[i]`. Wrapping a constant argument minted `^<literal>`
    /// (`(^x)[^2]`), which the constant-carrier guard refuses, turning e.g.
    /// `lang/logic_vcgen::f`'s instantiated `(^x)@ == 2` premise into a
    /// whole-function encoding error. The receiver still carries the wrapper,
    /// VARIABLE arguments keep the legacy full distribution (the closure
    /// lanes' matched `postcondition_mut(^f, ^result)` pairs depend on it),
    /// and a bare `^<literal>` in carrier position still refuses (the
    /// FA-side pin).
    #[test]
    #[timeout(10000)]
    fn final_over_method_call_wraps_receiver_not_constant_args() {
        use std::sync::Arc;
        unsoundness::reset();

        let mut encoder = AYEncoder::new();
        let call = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), Some(ExprSort::Seq))),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(2)],
        };
        let encoded = encoder.encode_pure(&PureExpr::Final(Arc::new(call)));
        assert!(
            encoded.is_ok(),
            "`^(s[2])` must encode as `(^s)[2]` — the index argument is a \
             current-state value, not a prophecy carrier; got {encoded:?}"
        );

        // The bare constant carrier still refuses — argument positions are
        // exempt from wrapping, never from the guard itself.
        assert!(
            matches!(
                encoder.encode_pure(&PureExpr::Final(Arc::new(PureExpr::Int(2)))),
                Err(EncodingError::Unsupported { .. })
            ),
            "`^2` in carrier position must keep refusing fail-closed"
        );
        unsoundness::reset();
    }

    /// tract19 — constant-carrier arm. `^<literal>` must refuse, `*<literal>`
    /// must still encode.
    ///
    /// The sort-based guard cannot reach this shape: a literal's sort is
    /// `Int`/`Bool`/`Float`, all of which `sort_embeds_mut_ref` classifies as
    /// pure values, so the collapse was permitted and
    /// `encode_wrapper_rewrite`'s "wrappers are no-ops on literals" arm folded
    /// `^3` to `3`. That was a LIVE false accept: with
    /// `#[ensures((^r)@ >= 0)] fn touch(r: &mut i32) { *r = 99; }`, the
    /// function
    /// `#[ensures(result@ == 3)] fn evil() -> i32 { let mut x = 3i32; let r = &mut x; touch(r); x }`
    /// verified with `decisions=0` although it returns 99 — the driver lowers
    /// `x` to `Final(Int(3))` and this arm folded the postcondition to
    /// `3 == 3`.
    #[test]
    #[timeout(10000)]
    fn prophecy_over_a_constant_carrier_refuses_but_deref_still_encodes() {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        let refused = encoder.encode_pure(&PureExpr::Final(std::sync::Arc::new(PureExpr::Int(3))));
        assert!(
            matches!(refused, Err(EncodingError::Unsupported { .. })),
            "`^3` must refuse fail-closed, got {refused:?}"
        );

        let after = unsoundness::snapshot();
        assert_eq!(
            unsoundness::delta(&before, &after)
                .get(&unsoundness::UnsoundnessCategory::FinalCollapseRefused),
            Some(&1),
            "the constant-carrier refusal must fire the demoting counter"
        );

        // `*3` IS faithful — the literal already is the referent's value.
        assert!(
            encoder
                .encode_pure(&PureExpr::Deref(std::sync::Arc::new(PureExpr::Int(3))))
                .is_ok(),
            "`*3` must keep collapsing — only the prophecy is unrepresentable"
        );
        unsoundness::reset();
    }
}
