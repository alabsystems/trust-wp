// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort-aware fail-closed guard on the `Final`-collapse routes (D-14; the
//! refusal messages name it "Final-collapse audit Fix A").
//!
//! Collapsing `Final(x)` (`^x`) to the same carrier as `x`/`*x` is exact only
//! when the carrier's sort embeds no mutable reference: a pure value has no
//! temporal state, so its "final" value IS its value. For carriers that embed
//! a `&mut` (a match binder over an `Option<&mut T>` payload, an ADT field
//! holding `&mut`, a tuple with a `&mut` component), no prophecy slot exists
//! in the collapsed encoding and the collapse silently asserts the inversion
//! `^x == *x` — the load-bearing false lemma behind the take_first_mut false
//! accept (D-14; `tests/adversarial/cases/a2_sibling_binder_fusion.rs`).
//!
//! This module provides the transitive `sort_embeds_mut_ref` predicate and
//! the single refusal helper. The predicate is FAIL-CLOSED: unknown or
//! unresolvable sorts (no annotation, undeclared datatypes, opaque tuples,
//! type parameters in carrier position) are treated as embedding — refusing an
//! exact collapse costs an honest Unknown; permitting an inexact one is a
//! false proof.
//!
//! Generic-ADT refinement: a decl field whose sort is an
//! UNSUBSTITUTED `ExprSort::TypeParam` is NOT embedding evidence. Decls are
//! built per verified `DefId` with that function's `substs` already applied,
//! so a `TypeParam` field only survives where the enclosing function is itself
//! generic over the parameter — a position with no prophecy carrier to invert.
//! Every concrete `&mut` instantiation lowers to a `Ref(_)` field in the
//! instantiating function's own decl and stays fail-closed there. Without this
//! refinement `partially_opaque::f<A, B>(x: S<A, B>)` would refuse on
//! `Datatype(m::S)`, whose only fields are `TypeParam(A)`/`TypeParam(B)`.
//! That refinement, and the value-model names' "no embedding", answer the
//! collapse question only. Whether a value holds a borrow at all, which
//! `resolve`'s by-value reading asks, is [`sort_holds_no_borrow`]: a question
//! of the sort's own shape, never of a declaration (D-126).
//!
//! Decl-level mutability fidelity: rustc-backed `AdtDecl` field sorts
//! PRESERVE mutability (`ty_to_adt_decl_sort` maps `&mut T` to
//! `ExprSort::MutRef` and `&T` to `ExprSort::Ref`), so a decl-level `Ref`
//! genuinely means a shared reference and recurses into its referent exactly
//! like an expression-level annotation. Were decl fields to erase mutability,
//! every reference-typed decl field would have to count as embedding.

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
/// or a declared-ADT field sort. Only the `TypeParam` arm distinguishes them:
/// an unsubstituted ADT generic parameter in a decl field has no prophecy
/// carrier to invert, while an annotation-level type parameter is an unknown
/// instantiation.
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
    /// - `Ref(inner)`: recurse into the referent (both positions — decl field
    ///   sorts preserve mutability).
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
    ///   (see the module docs).
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
            | ExprSort::Float(_) => false,
            // `Ref` is genuinely shared (`&T`) at BOTH positions: decl field
            // sorts preserve mutability, so a `&mut` cannot hide under a
            // decl-level `Ref`.
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
                    // The driver marks a declaration some value of which may
                    // hold a `&mut` its field sorts do not show: an
                    // `Option<&mut T>` field declared at the Option model's
                    // `Int`, or another instantiation or same-named ADT the
                    // one declaration answers for (D-126).
                    Some(decl) if decl.may_hold_a_borrow => true,
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
                // fail-closed where it can actually bite: rustc lowers
                // `S<&mut i32, B>` to a decl whose field sort is `MutRef(Int)`
                // (`ty_to_adt_decl_sort` preserves mutability), which the
                // `MutRef` arm above treats as embedding. So the function
                // that owns the real prophecy carrier — the instantiating
                // caller, or the monomorphic definition — keeps refusing. In
                // the generic definition there is no prophecy slot to
                // invert: a `TypeParam`-sorted subterm is an opaque
                // uninterpreted value whose `resolve` is encoded as an
                // uninterpreted predicate, never as `^ == *`.
                // (partially_opaque::f)
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

    /// Fail-closed refusal for a prophecy applied to a CONSTANT carrier (the
    /// constant-carrier arm of the guard).
    ///
    /// The sort-based guard above cannot see this shape: a literal's sort is
    /// `Int`/`Bool`/`Float`, all of which `sort_embeds_mut_ref` classifies as
    /// pure values, so without this arm the collapse is permitted and
    /// `encode_wrapper_rewrite`'s "wrappers are no-ops on literals" arm folds
    /// `^3` to `3`. That is the same `^x == *x` inversion — a false accept
    /// (the call site in `pure_encoding/wrapper.rs` carries the reproducer,
    /// as does `prophecy_over_a_constant_carrier_refuses_but_deref_still_encodes`
    /// below).
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

    /// Fail-closed refusal of `resolve(x)` of a variable that may hold a
    /// borrow and whose final value the lane does not name (D-126): neither
    /// the by-value `true` nor a fresh, unconstrained final is its reading.
    /// The counter fires for demotion, as for the collapse refusals.
    pub(crate) fn refuse_resolve_without_a_final(
        &self,
        var_name: &str,
        ann: Option<&ExprSort>,
    ) -> EncodingError {
        unsoundness::increment(unsoundness::UnsoundnessCategory::FinalCollapseRefused);
        let ann_desc = ann.map_or_else(|| "<unannotated>".to_string(), ToString::to_string);
        EncodingError::unsupported(format!(
            "resolve refused (fail-closed): `resolve({var_name})` of a value whose sort \
             ({ann_desc}) may hold a borrow, and whose final value this lane does not name: it \
             is neither the by-value `true` nor `*{var_name} == ^{var_name}` over a final value \
             the lane decides (D-126)"
        ))
    }

    /// Fail-closed refusal of `^e` of a field or tuple projection whose field
    /// may be a mutable reference: the final value of a borrow held through
    /// another is not the projection of the holder's final value (D-127).
    pub(crate) fn refuse_final_of_a_held_borrow(&self, projection: &PureExpr) -> EncodingError {
        unsoundness::increment(unsoundness::UnsoundnessCategory::FinalCollapseRefused);
        EncodingError::unsupported(format!(
            "final value refused (fail-closed): `^({projection})` of a field that may be a \
             mutable reference is the final value of the borrow it holds, which its holder \
             decides, not the field of the holder's final value (D-127)"
        ))
    }

    /// Fail-closed refusal of `resolve(e)` of an operand that is not a
    /// variable (a dereference, a field or tuple projection, a view, a
    /// constructor, a literal) and not a dereference of a value: its resolve
    /// is the operand's own at its own type, `true` of a value and `*e == ^e`
    /// of a borrow, and neither the resolve of the variable it is held
    /// through nor `*e == ^e` distributed into the operand is that reading
    /// (D-127). The counter fires for demotion, as for the collapse refusals.
    pub(crate) fn refuse_resolve_of_a_held_value(&self, arg: &PureExpr) -> EncodingError {
        unsoundness::increment(unsoundness::UnsoundnessCategory::FinalCollapseRefused);
        EncodingError::unsupported(format!(
            "resolve refused (fail-closed): `resolve({arg})` resolves a value held through \
             another or computed from one, at that value's own type (`true` of a value, `*e == \
             ^e` of a borrow it is); neither the resolve of what holds it nor `*e == ^e` \
             distributed into it is that reading (D-127)"
        ))
    }
}

/// Whether a value of `sort` certainly holds no borrow, so that its `resolve`
/// is the by-value `true` (#2683): a scalar, the unit, or a shared reference
/// to one. Decided by the sort's own shape, never through a declaration
/// (D-126). A `Datatype`'s declaration cannot answer: the builtin models
/// declare an `Option<&mut i32>` or `Result<&mut i32, _>` field at `Int`,
/// declarations are keyed by bare name and built once per function from the
/// first instantiation met (`S<i32>` answers for `S<&mut i32>`, `a::T` for
/// `b::T`), a value-model name (`Vec`, `Box`, `Snapshot`, ...) and `Seq`,
/// `FMap` and a tuple carry no element sort, and a type parameter may be
/// instantiated at a borrow. Each read as `true` verified a false claim that
/// a borrow the value holds is resolved.
pub(crate) fn sort_holds_no_borrow(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::Int | ExprSort::Bool | ExprSort::Unit | ExprSort::Float(_) => true,
        ExprSort::Ref(inner) => sort_holds_no_borrow(inner),
        _ => false,
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
///   * `ExprSort::Seq` / `ExprSort::FMap` — do not match the
///     `Datatype(_) | Ref(_)` arm, so they keep a distinct final variable
///     (the documented intent, #2675/#2700);
///   * `ExprSort::Datatype(creusot_std::Seq)` — the spelling the driver
///     actually emits for a ghost `Seq` local once the `&mut` has been peeled
///     to the referent. This DOES match the arm, and `sort_embeds_mut_ref`
///     short-circuits every value-model canonical name to `false`, so the
///     sort-based refusal does not fire either. Without this predicate the
///     collapse asserts `^s == s`, contradicting the mutation premise
///     `^s == s.push_front(v)` and manufacturing a contradictory (vacuous)
///     base.
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
            | ExprSort::Float(_) => false,
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

    /// `resolve`'s by-value reading asks the sort's own shape. A declaration
    /// answering for a `Datatype` read `W { o: Option<&mut i32> }` (its field
    /// declared at the builtin Option model's `Int`) as holding no borrow, and
    /// verified a false `resolve(w)` of a `w` whose borrow the body writes;
    /// the value-model names, `Seq`, `FMap`, a tuple and a type parameter
    /// carry no element sort to ask (D-126).
    #[test]
    #[timeout(10000)]
    fn only_a_sort_whose_shape_holds_no_borrow_is_a_value() {
        for value in [
            ExprSort::Int,
            ExprSort::Bool,
            ExprSort::Unit,
            ExprSort::Float(trust_wp_core::formula::FloatWidth::F32),
            ExprSort::Float(trust_wp_core::formula::FloatWidth::F64),
            ExprSort::Ref(Box::new(ExprSort::Int)),
            ExprSort::Ref(Box::new(ExprSort::Ref(Box::new(ExprSort::Bool)))),
        ] {
            assert!(sort_holds_no_borrow(&value), "{value} is a value");
        }
        let mut decls = AdtDecls::new();
        decls.insert(
            "W".to_string(),
            struct_decl("W", vec![AdtFieldDecl::new("o".to_string(), ExprSort::Int)]),
        );
        let encoder = encoder_with_decls(decls);
        let w = ExprSort::Datatype(intern_sort_name("W"));
        assert!(
            !encoder.sort_embeds_mut_ref(&w),
            "the collapse guard's own answer is unchanged"
        );
        for may_hold in [
            w.clone(),
            ExprSort::Ref(Box::new(w)),
            ExprSort::Seq,
            ExprSort::FMap,
            ExprSort::Tuple(2),
            ExprSort::TypeParam(intern_sort_name("T")),
            ExprSort::MutRef(Box::new(ExprSort::Int)),
            ExprSort::Ref(Box::new(ExprSort::MutRef(Box::new(ExprSort::Int)))),
            ExprSort::Datatype(intern_sort_name("SomeUndeclaredAdt")),
            ExprSort::Datatype(intern_sort_name("std::vec::Vec")),
            ExprSort::Datatype(intern_sort_name("Box")),
            ExprSort::Datatype(intern_sort_name("Snapshot")),
        ] {
            assert!(
                !sort_holds_no_borrow(&may_hold),
                "{may_hold} may hold a borrow"
            );
        }
    }

    /// A declaration the driver marked as possibly holding a `&mut` embeds
    /// one whatever its field sorts say. `W { o: Option<&mut i32> }` declares
    /// `o` at the Option model's `Int`; collapsing `^w` onto `w` read
    /// `resolve(w.o)` as `get0(w) == get0(w)`, verified of a body writing 5
    /// through the borrow. An enclosing declaration inherits the mark
    /// through its field (D-126).
    #[test]
    #[timeout(10000)]
    fn a_declaration_marked_as_holding_a_borrow_embeds_one() {
        let w = ExprSort::Datatype(intern_sort_name("W"));
        let mut decls = AdtDecls::new();
        decls.insert(
            "W".to_string(),
            struct_decl("W", vec![AdtFieldDecl::new("o".to_string(), ExprSort::Int)])
                .with_may_hold_a_borrow(true),
        );
        decls.insert(
            "Outer".to_string(),
            struct_decl("Outer", vec![AdtFieldDecl::new("w".to_string(), w.clone())]),
        );
        decls.insert(
            "V".to_string(),
            struct_decl("V", vec![AdtFieldDecl::new("o".to_string(), ExprSort::Int)]),
        );
        let encoder = encoder_with_decls(decls);
        assert!(encoder.sort_embeds_mut_ref(&w), "W holds a borrow");
        assert!(
            encoder.sort_embeds_mut_ref(&ExprSort::Ref(Box::new(w))),
            "&W reaches W's borrow"
        );
        assert!(
            encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("Outer"))),
            "Outer holds a W"
        );
        assert!(
            !encoder.sort_embeds_mut_ref(&ExprSort::Datatype(intern_sort_name("V"))),
            "an unmarked declaration of Int fields holds none"
        );
    }

    /// `^x.m` of `x: &mut M { m: &mut i32 }` is the final value of the borrow
    /// the field holds, which its holder decides; distributed into the getter
    /// it read `(^x).m`, the field the outer borrow is left with, and
    /// `proof_assert!(^x.m == *x.m)` of an untouched `x` held (D-127). The same
    /// projection of a field that is no mutable reference is the driver's
    /// image of a reborrow `&mut x.a`, and keeps Creusot's rule `^(x.a) ==
    /// (^x).a`.
    #[test]
    #[timeout(10000)]
    fn final_of_a_field_holding_a_borrow_through_a_reference_refuses() {
        use std::sync::Arc;

        use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

        let mut decls = AdtDecls::new();
        decls.insert(
            "M".to_string(),
            struct_decl(
                "M",
                vec![AdtFieldDecl::new(
                    "m".to_string(),
                    ExprSort::MutRef(Box::new(ExprSort::Int)),
                )],
            ),
        );
        decls.insert(
            "S".to_string(),
            struct_decl(
                "S",
                vec![
                    AdtFieldDecl::new("a".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("b".to_string(), ExprSort::Int),
                ],
            ),
        );
        let holder = |name: &str| {
            PureExpr::Var(
                "x".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name(name),
                )))),
            )
        };
        let final_of_field = |base: PureExpr| {
            PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![base],
            }))
        };
        let mut encoder = encoder_with_decls(decls.clone());
        for refused in [
            final_of_field(holder("M")),
            final_of_field(PureExpr::Deref(Arc::new(holder("M")))),
            final_of_field(PureExpr::Var(
                "t".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Tuple(2)))),
            )),
        ] {
            assert!(
                matches!(
                    encoder.encode_pure(&refused),
                    Err(EncodingError::Unsupported { .. })
                ),
                "{refused} was encoded"
            );
        }
        decls.insert(
            "SC".to_string(),
            struct_decl(
                "SC",
                vec![AdtFieldDecl::new(
                    "c".to_string(),
                    ExprSort::Ref(Box::new(ExprSort::Int)),
                )],
            ),
        );
        // A field that is no mutable reference (a scalar, or a `&Cell` a
        // body sets through) keeps the reborrow rule.
        for kept in ["S", "SC"] {
            let mut encoder = encoder_with_decls(decls.clone());
            let reborrow = final_of_field(holder(kept));
            assert!(
                encoder.encode_pure(&reborrow).is_ok(),
                "{reborrow} of a field that is no mutable reference must keep encoding"
            );
        }
    }

    /// `^x.s.m` of `x: &mut N { s: M { m: &mut i32 } }` is the final value of
    /// the borrow `m` holds, two projections deep. Phase 1f asked the
    /// annotation of the outer projection's base, which `x.s` does not carry,
    /// so the chain was never refused and Phase 3 distributed `^` down to
    /// `(^x).s.m`: `proof_assert!(^x.s.m == *x.s.m)` of an untouched `x` was
    /// proved (D-128). The walk types the chain from the declarations, and a
    /// chain it cannot type through a reference is refused; a scalar two
    /// fields deep keeps the reborrow rule `^(x.s.a) == (^x).s.a`.
    #[test]
    #[timeout(10000)]
    fn final_of_a_borrow_held_deeper_in_a_projection_chain_refuses() {
        use std::sync::Arc;

        use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

        let named = |name: &str, fields: Vec<(&str, ExprSort)>| {
            struct_decl(
                name,
                fields
                    .into_iter()
                    .map(|(field, sort)| AdtFieldDecl::new(field.to_string(), sort))
                    .collect(),
            )
        };
        let datatype = |name: &str| ExprSort::Datatype(intern_sort_name(name));
        let mut decls = AdtDecls::new();
        for decl in [
            named("M", vec![("m", ExprSort::MutRef(Box::new(ExprSort::Int)))]),
            named("N", vec![("s", datatype("M"))]),
            named("S", vec![("a", ExprSort::Int), ("b", ExprSort::Int)]),
            named("NS", vec![("s", datatype("S"))]),
            named("W", vec![("s", ExprSort::TypeParam(intern_sort_name("T")))]),
            named("U", vec![("s", datatype("Unregistered"))]),
            named("P", vec![("q", ExprSort::Tuple(2))]),
            named("R", vec![("r", ExprSort::MutRef(Box::new(datatype("M"))))]),
        ] {
            decls.insert(decl.adt_name.clone(), decl);
        }
        let holder = |name: &str| {
            PureExpr::Var(
                "x".to_string(),
                Some(ExprSort::MutRef(Box::new(datatype(name)))),
            )
        };
        let field = |index: usize, base: PureExpr| PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(index),
            args: vec![base],
        };
        let deref = |base: PureExpr| PureExpr::Deref(Arc::new(base));
        let final_of = |place: PureExpr| PureExpr::Final(Arc::new(place));
        for refused in [
            // `^x.s.m`, auto-deref and explicit.
            final_of(field(0, field(0, holder("N")))),
            final_of(field(0, field(0, deref(holder("N"))))),
            // An intermediate field the declarations do not type: a type
            // parameter, an unregistered datatype, a tuple.
            final_of(field(0, field(0, holder("W")))),
            final_of(field(0, field(0, holder("U")))),
            final_of(field(0, field(0, holder("P")))),
            // `^(*x.r).m`: a borrow held through an inner borrow.
            final_of(field(0, deref(field(0, holder("R"))))),
            // `^(**x).s.m` of `x: &mut Box<N>`, the `Box` erased from the sort.
            final_of(field(0, field(0, deref(deref(holder("N")))))),
        ] {
            let mut encoder = encoder_with_decls(decls.clone());
            assert!(
                matches!(
                    encoder.encode_pure(&refused),
                    Err(EncodingError::Unsupported { .. })
                ),
                "{refused} was encoded"
            );
        }
        for kept in [
            final_of(field(0, field(0, holder("NS")))),
            final_of(field(1, field(0, deref(holder("NS"))))),
        ] {
            let mut encoder = encoder_with_decls(decls.clone());
            assert!(
                encoder.encode_pure(&kept).is_ok(),
                "{kept} reaches a scalar and must keep encoding"
            );
        }
    }

    /// `^` of a field that may be a borrow, whose holder is the parameter's
    /// FINAL value (`^(^x).m`), an `if` or `match` choosing the holder
    /// (`^(if c { x } else { x }).m`), or an element of a sequence reached
    /// through a reference (`^x[0]`, `^x[0].m`): `projection_place_sort`
    /// answered "no sort, not through a reference" for each holder, so
    /// Phase 1f refused none and Phase 3 read `(^x).m` and `(^x)[0]`, the
    /// places the OUTER borrow is left with. An untouched `x` proved each
    /// (D-129). A scalar field of the same holders keeps the reborrow rule.
    #[test]
    #[timeout(10000)]
    fn final_of_a_borrow_under_a_final_a_branch_or_an_element_refuses() {
        use std::sync::Arc;

        use trust_wp_core::formula::{
            internal::tuple_lowering::tuple_field_logic_fn_name, MatchArm, Pattern,
        };

        let datatype = |name: &str| ExprSort::Datatype(intern_sort_name(name));
        let mut decls = AdtDecls::new();
        for decl in [
            struct_decl(
                "M",
                vec![AdtFieldDecl::new(
                    "m".to_string(),
                    ExprSort::MutRef(Box::new(ExprSort::Int)),
                )],
            ),
            struct_decl("S", vec![AdtFieldDecl::new("a".to_string(), ExprSort::Int)]),
            struct_decl("V", Vec::new()),
        ] {
            decls.insert(decl.adt_name.clone(), decl);
        }
        let param =
            |sort: ExprSort| PureExpr::Var("x".to_string(), Some(ExprSort::MutRef(Box::new(sort))));
        let field = |base: PureExpr| PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![base],
        };
        let element = |receiver: PureExpr| PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0)],
        };
        let final_of = |place: PureExpr| PureExpr::Final(Arc::new(place));
        let deref = |place: PureExpr| PureExpr::Deref(Arc::new(place));
        let cond = || PureExpr::Var("c".to_string(), Some(ExprSort::Bool));
        let ite = |branch: PureExpr| {
            PureExpr::Ite(Arc::new(cond()), Arc::new(branch.clone()), Arc::new(branch))
        };
        let matched = |branch: PureExpr| PureExpr::Match {
            scrutinee: Arc::new(cond()),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(PureExpr::Bool(true)),
                    body: branch.clone(),
                },
                MatchArm {
                    pattern: Pattern::Literal(PureExpr::Bool(false)),
                    body: branch,
                },
            ],
        };
        for refused in [
            final_of(field(final_of(param(datatype("M"))))),
            final_of(field(ite(param(datatype("M"))))),
            final_of(field(matched(param(datatype("M"))))),
            final_of(field(ite(deref(param(datatype("M")))))),
            final_of(field(ite(final_of(param(datatype("M")))))),
            final_of(element(param(datatype("V")))),
            final_of(element(deref(param(datatype("V"))))),
            final_of(field(element(param(datatype("V"))))),
            final_of(element(param(ExprSort::Seq))),
            final_of(field(element(param(ExprSort::Seq)))),
        ] {
            let mut encoder = encoder_with_decls(decls.clone());
            assert!(
                matches!(
                    encoder.encode_pure(&refused),
                    Err(EncodingError::Unsupported { .. })
                ),
                "{refused} was encoded"
            );
        }
        for kept in [
            final_of(field(ite(param(datatype("S"))))),
            final_of(field(deref(param(datatype("S"))))),
        ] {
            let mut encoder = encoder_with_decls(decls.clone());
            assert!(
                encoder.encode_pure(&kept).is_ok(),
                "{kept} reaches a scalar and must keep encoding"
            );
        }
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
        assert!(
            !encoder.sort_embeds_mut_ref(&ExprSort::Float(trust_wp_core::formula::FloatWidth::F64))
        );
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
        // embeds (the generic-ADT refinement relaxes decl FIELDS only).
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
        // Decl field sorts preserve mutability, so a decl-level `Ref`
        // genuinely means `&T` and recurses. `&i32` is pure;
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
        // The SAME `S<A, B>` instantiated at `S<&mut i32, B>`: rustc lowers
        // the `&mut i32` field to `MutRef(Int)` (mutability preserved at decl
        // level), so the instantiating function's registry keeps refusing.
        // This is the false-accept-side pin of the generic-ADT refinement.
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
    /// `^(s[i]) = (^s)[i]`. Wrapping a constant argument would mint
    /// `^<literal>` (`(^x)[^2]`), which the constant-carrier guard refuses,
    /// turning e.g. `lang/logic_vcgen::f`'s instantiated `(^x)@ == 2` premise
    /// into a whole-function encoding error. The receiver still carries the
    /// wrapper, VARIABLE arguments keep the full distribution (the closure
    /// lanes' matched `postcondition_mut(^f, ^result)` pairs depend on it),
    /// and a bare `^<literal>` in carrier position still refuses (the
    /// false-accept-side pin).
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

    /// Constant-carrier arm: `^<literal>` must refuse, `*<literal>` must still
    /// encode.
    ///
    /// The sort-based guard cannot reach this shape: a literal's sort is
    /// `Int`/`Bool`/`Float`, all of which `sort_embeds_mut_ref` classifies as
    /// pure values, so without the refusal the collapse is permitted and
    /// `encode_wrapper_rewrite`'s "wrappers are no-ops on literals" arm folds
    /// `^3` to `3`. That is a false accept: with
    /// `#[ensures((^r)@ >= 0)] fn touch(r: &mut i32) { *r = 99; }`, the
    /// function
    /// `#[ensures(result@ == 3)] fn evil() -> i32 { let mut x = 3i32; let r = &mut x; touch(r); x }`
    /// verifies with `decisions=0` although it returns 99 — the driver lowers
    /// `x` to `Final(Int(3))` and the fold turns the postcondition into
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
