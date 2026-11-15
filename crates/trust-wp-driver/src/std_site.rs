// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Std-spec terms that only a call site can resolve.
//!
//! An allocation-sizing std function panics when the requested size in BYTES
//! exceeds `isize::MAX`, so its precondition needs the byte size of an element
//! type the spec only names by its generic parameter (`T` of
//! `Vec::<T>::with_capacity`). The spec writes that size as a marker,
//! `__trust_wp_std_site_size_of_T()` (`_K_V` for the tuple `(K, V)`, and
//! `align_of_` for the alignment), and the call site rewrites it to the byte
//! count of the type THIS call instantiates.
//!
//! Only a fully concrete type is resolved. A type that still mentions a
//! generic parameter of the caller keeps its marker, and so does
//! `__trust_wp_std_site_unmodelled_panic()`, the clause of a function whose
//! panic the spec cannot state. The encoder refuses every marker it sees, so a
//! call whose precondition could not be written down is never discharged.
//!
//! One path can name impls that panic differently: `<Instant as Sub>::sub` is
//! both `Instant - Instant`, which saturates, and `Instant - Duration`, which
//! panics on a bound the platform clock sets.
//! `__trust_wp_std_site_unmodelled_panic_unless_same_<P>_<Q>()` becomes `true`
//! where the call instantiates `P` and `Q` with one type, and stays a refused
//! marker everywhere else. Where the second impl's panic CAN be stated, the
//! spec asks the question itself: `__trust_wp_std_site_same_<P>_<Q>()` becomes
//! `true` or `false` at every call that instantiates both, so
//! `same_Self_Rhs() || self@ >= rhs@` owes the subtraction's bound exactly where
//! `Rhs` is not `Self`.
//!
//! `Iterator::count` and `Iterator::position` keep a running `usize` under the
//! caller's overflow checks, so they panic on an iterator longer than
//! `usize::MAX`. `__trust_wp_std_site_unmodelled_panic_unless_length_fits_<P>()`
//! becomes `true` where the call instantiates `P` with an iterator whose
//! length is a `usize` by construction, and stays a refused marker everywhere
//! else. `Vec::drain` panics on a range out of order or past the length, which
//! no clause can read off a `RangeBounds`; the full range `..` is the one range
//! that never panics, and `__trust_wp_std_site_unmodelled_panic_unless_full_range_<P>()`
//! becomes `true` where `P` is `RangeFull`.
//!
//! `Perm::disjoint_lemma` holds two permissions over containers of type `P`,
//! which are distinct only where a container has an identity of its own: a
//! trust-wp-std cell or atomic, or a raw pointer to a value of non-zero size.
//! Two zero-sized values share an address (`Box::new(())` allocates nothing).
//! `__trust_wp_std_site_distinct_containers_<P>()` becomes `true` there and
//! `false` everywhere else, a caller's generic parameter included.

use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use trust_wp_core::formula::internal::builtins::STD_SITE_MARKER_PREFIX;
use trust_wp_driver::StdSpec;

use crate::provenance::CallSite;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LayoutQuery {
    Size,
    Align,
}

/// A marker the call site may be able to answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SiteQuery<'a> {
    /// The byte size or alignment of the named parameters (their tuple when
    /// there are several).
    Layout(LayoutQuery, &'a [&'a str]),
    /// Whether the two named parameters are instantiated with one type,
    /// answered only when they are.
    SameType(&'a str, &'a str),
    /// Whether the two named parameters are instantiated with one type,
    /// answered either way.
    SameTypeTest(&'a str, &'a str),
    /// Whether the named parameter is instantiated with an iterator that
    /// yields at most `usize::MAX` items.
    LengthFits(&'a str),
    /// Whether the named parameter is instantiated with `RangeFull`.
    FullRange(&'a str),
    /// Whether two permissions over containers of the named parameter's type
    /// guard two distinct containers, answered either way.
    DistinctContainers(&'a str),
}

/// What a resolved marker is rewritten to.
#[derive(Clone, Debug, PartialEq, Eq)]
enum SiteAnswer {
    Bytes(u64),
    /// The panic this marker stands for cannot happen at this call.
    NoPanic,
    /// The truth value of a question about the call's generic arguments.
    Holds(bool),
}

/// `spec` with every marker this call site can resolve rewritten (a layout to
/// its byte count, a refusal the call rules out to `true`, a same-type test to
/// its truth value). Without a call site nothing is resolved.
pub(crate) fn instantiate_std_site_markers<'tcx>(
    tcx: TyCtxt<'tcx>,
    site: Option<CallSite<'tcx>>,
    spec: StdSpec,
) -> StdSpec {
    let mentions = |clause: &String| clause.contains(STD_SITE_MARKER_PREFIX);
    if !spec
        .requires
        .iter()
        .chain(spec.ensures.iter())
        .any(mentions)
    {
        return spec;
    }
    let mut resolve = |query: SiteQuery<'_>| {
        let site = site?;
        match query {
            SiteQuery::Layout(layout, params) => {
                let (size, align) = concrete_layout(tcx, site, params)?;
                Some(SiteAnswer::Bytes(match layout {
                    LayoutQuery::Size => size,
                    LayoutQuery::Align => align,
                }))
            }
            SiteQuery::SameType(left, right) => {
                let left = instantiated_param(tcx, site, left)?;
                let right = instantiated_param(tcx, site, right)?;
                (left == right).then_some(SiteAnswer::NoPanic)
            }
            // `false` is only ever the weaker answer for a spec that reads this
            // test as `same() || <bound>`: types that compare unequal (a generic
            // parameter of the caller, or regions) owe the bound, which is true
            // of the same-type impl too.
            SiteQuery::SameTypeTest(left, right) => {
                let left = instantiated_param(tcx, site, left)?;
                let right = instantiated_param(tcx, site, right)?;
                Some(SiteAnswer::Holds(left == right))
            }
            SiteQuery::LengthFits(param) => {
                let iterator = instantiated_param(tcx, site, param)?;
                iterator_length_fits_usize(tcx, iterator).then_some(SiteAnswer::NoPanic)
            }
            SiteQuery::FullRange(param) => {
                let range = instantiated_param(tcx, site, param)?;
                matches!(range.kind(), ty::TyKind::Adt(adt, _)
                    if tcx.is_lang_item(adt.did(), rustc_attr_ir::LangItem::RangeFull))
                .then_some(SiteAnswer::NoPanic)
            }
            // `false` withholds the lemma's fact, the weaker answer.
            SiteQuery::DistinctContainers(param) => {
                let container = instantiated_param(tcx, site, param)?;
                Some(SiteAnswer::Holds(containers_are_distinct(tcx, container)))
            }
        }
    };
    let requires = spec
        .requires
        .iter()
        .map(|clause| settle_answered_guard(rewrite_std_site_markers(clause, &mut resolve)))
        .collect();
    let ensures = spec
        .ensures
        .iter()
        .map(|clause| settle_answered_guard(rewrite_std_site_markers(clause, &mut resolve)))
        .collect();
    StdSpec {
        requires,
        ensures,
        ..spec
    }
}

/// A clause `marker ==> fact` whose marker the site answered, stated as what it
/// means: the fact itself, or `true`. The clause lanes read a fact by its own
/// shape (a disequation between two permission arguments is rewritten through
/// their pointers), and a guard of `true` in front of it hides that shape.
///
/// Only a fact with no implication of its own is settled: `==>` is the loosest
/// connective, so `g ==> fact` is `g ==> (fact)` exactly when `fact` holds no
/// `==>` or `<==>`, and anything else is left for the encoder to read whole.
fn settle_answered_guard(clause: String) -> String {
    let trimmed = clause.trim_start();
    let settled = |guard: &str| {
        trimmed
            .strip_prefix(guard)
            .filter(|fact| !fact.contains("==>"))
    };
    if let Some(fact) = settled("true ==> ") {
        return fact.to_string();
    }
    if settled("false ==> ").is_some() {
        return "true".to_string();
    }
    clause
}

/// Byte size and alignment of the callee's generic parameters `params` as
/// `site` instantiates them (the tuple of them when there are several), or
/// `None` when that type is not fully concrete.
fn concrete_layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    site: CallSite<'tcx>,
    params: &[&str],
) -> Option<(u64, u64)> {
    let mut tys: Vec<Ty<'tcx>> = Vec::with_capacity(params.len());
    for name in params {
        tys.push(instantiated_param(tcx, site, name)?);
    }
    let ty = match tys.as_slice() {
        [] => return None,
        [one] => *one,
        many => Ty::new_tup(tcx, many),
    };
    concrete_type_layout(tcx, ty)
}

/// Byte size and alignment of `ty`, or `None` when it is not fully concrete
/// or not sized.
fn concrete_type_layout<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    // A layout computed for a generic parameter of the caller would be the
    // layout of whatever the solver chose; only a type every instantiation of
    // the caller agrees on has one size.
    if ty.has_non_region_param() {
        return None;
    }
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let ty = tcx
        .try_normalize_erasing_regions(
            typing_env,
            rustc_middle::ty::set_aliases_to_non_rigid(tcx, ty),
        )
        .ok()?;
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
    if layout.is_unsized() {
        return None;
    }
    Some((layout.size.bytes(), layout.align.bytes()))
}

/// Whether two live permissions over containers of type `ty` guard distinct
/// containers: a cell or atomic of trust-wp-std is its own identity, and a raw
/// pointer is an address, distinct only for a pointee of known non-zero size.
fn containers_are_distinct<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::TyKind::RawPtr(pointee, _) => {
            concrete_type_layout(tcx, *pointee).is_some_and(|(size, _)| size > 0)
        }
        ty::TyKind::Adt(adt, _) => tcx.crate_name(adt.did().krate).as_str() == "trust_wp_std",
        _ => false,
    }
}

/// Whether an iterator of type `ty` yields at most `usize::MAX` items whatever
/// its value: a slice's `Iter`/`IterMut` and a `Vec`'s `IntoIter` walk a
/// buffer whose length is a `usize`, a `Range` of an integer type no wider
/// than `usize` has at most `2^bits - 1` steps, and a `RangeInclusive` of a
/// strictly narrower one at most `2^bits`. The items are named by their
/// defining crate and lang or diagnostic item, never by a printed path.
fn iterator_length_fits_usize<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let ty::TyKind::Adt(adt, args) = ty.kind() else {
        return false;
    };
    let did = adt.did();
    let pointer_bits = tcx.data_layout.pointer_size().bits();
    let integer_bits = |index: usize| -> Option<u64> {
        let element = args.get(index)?.as_type()?;
        match element.kind() {
            ty::TyKind::Int(int) => Some(int.bit_width().unwrap_or(pointer_bits)),
            ty::TyKind::Uint(uint) => Some(uint.bit_width().unwrap_or(pointer_bits)),
            _ => None,
        }
    };
    if tcx.is_lang_item(did, rustc_attr_ir::LangItem::Range) {
        return integer_bits(0).is_some_and(|bits| bits <= pointer_bits);
    }
    if tcx.is_lang_item(did, rustc_attr_ir::LangItem::RangeInclusiveStruct) {
        return integer_bits(0).is_some_and(|bits| bits < pointer_bits);
    }
    if tcx.get_diagnostic_item(rustc_span::Symbol::intern("SliceIter")) == Some(did) {
        return true;
    }
    let path: Vec<String> = tcx
        .def_path(did)
        .data
        .iter()
        .map(|segment| segment.data.to_string())
        .collect();
    match tcx.crate_name(did.krate).as_str() {
        "core" => path == ["slice", "iter", "IterMut"],
        "alloc" => path == ["vec", "into_iter", "IntoIter"],
        _ => false,
    }
}

/// The type `site` instantiates the callee's generic parameter `name` with.
fn instantiated_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    site: CallSite<'tcx>,
    name: &str,
) -> Option<Ty<'tcx>> {
    let generics = tcx.generics_of(site.callee);
    let index =
        (0..generics.count()).find(|&index| generics.param_at(index, tcx).name.as_str() == name)?;
    site.args.get(index)?.as_type()
}

/// Rewrite each `__trust_wp_std_site_*()` marker in `clause` that `resolve`
/// answers; everything else, unresolved markers included, is kept verbatim.
fn rewrite_std_site_markers(
    clause: &str,
    resolve: &mut dyn FnMut(SiteQuery<'_>) -> Option<SiteAnswer>,
) -> String {
    let mut out = String::with_capacity(clause.len());
    let mut rest = clause;
    while let Some(position) = rest.find(STD_SITE_MARKER_PREFIX) {
        out.push_str(&rest[..position]);
        let after = &rest[position + STD_SITE_MARKER_PREFIX.len()..];
        let ident_len = after
            .bytes()
            .take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            .count();
        let ident = &after[..ident_len];
        let tail = &after[ident_len..];
        let resolved = tail.strip_prefix("()").and_then(|_| {
            if let Some(param) = ident.strip_prefix("unmodelled_panic_unless_length_fits_") {
                return (!param.is_empty() && !param.contains('_'))
                    .then(|| resolve(SiteQuery::LengthFits(param)))
                    .flatten();
            }
            if let Some(param) = ident.strip_prefix("unmodelled_panic_unless_full_range_") {
                return (!param.is_empty() && !param.contains('_'))
                    .then(|| resolve(SiteQuery::FullRange(param)))
                    .flatten();
            }
            if let Some(pair) = ident.strip_prefix("unmodelled_panic_unless_same_") {
                return match pair.split('_').collect::<Vec<_>>().as_slice() {
                    [left, right] if !left.is_empty() && !right.is_empty() => {
                        resolve(SiteQuery::SameType(left, right))
                    }
                    _ => None,
                };
            }
            if let Some(param) = ident.strip_prefix("distinct_containers_") {
                return (!param.is_empty() && !param.contains('_'))
                    .then(|| resolve(SiteQuery::DistinctContainers(param)))
                    .flatten();
            }
            if let Some(pair) = ident.strip_prefix("same_") {
                return match pair.split('_').collect::<Vec<_>>().as_slice() {
                    [left, right] if !left.is_empty() && !right.is_empty() => {
                        resolve(SiteQuery::SameTypeTest(left, right))
                    }
                    _ => None,
                };
            }
            let (query, params) = if let Some(params) = ident.strip_prefix("size_of_") {
                (LayoutQuery::Size, params)
            } else {
                (LayoutQuery::Align, ident.strip_prefix("align_of_")?)
            };
            let params: Vec<&str> = params.split('_').collect();
            if params.iter().any(|param| param.is_empty()) {
                return None;
            }
            resolve(SiteQuery::Layout(query, &params))
        });
        match resolved {
            Some(answer) => {
                match answer {
                    SiteAnswer::Bytes(bytes) => out.push_str(&bytes.to_string()),
                    SiteAnswer::NoPanic | SiteAnswer::Holds(true) => out.push_str("true"),
                    SiteAnswer::Holds(false) => out.push_str("false"),
                }
                rest = &tail["()".len()..];
            }
            None => {
                out.push_str(&rest[position..position + STD_SITE_MARKER_PREFIX.len() + ident_len]);
                rest = tail;
            }
        }
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rewrite(clause: &str, answer: &dyn Fn(LayoutQuery, &[&str]) -> Option<u64>) -> String {
        let mut resolve = |query: SiteQuery<'_>| match query {
            SiteQuery::Layout(layout, params) => answer(layout, params).map(SiteAnswer::Bytes),
            SiteQuery::SameType(..)
            | SiteQuery::SameTypeTest(..)
            | SiteQuery::LengthFits(..)
            | SiteQuery::FullRange(..)
            | SiteQuery::DistinctContainers(..) => None,
        };
        rewrite_std_site_markers(clause, &mut resolve)
    }

    fn rewrite_same(clause: &str, same: bool) -> String {
        let mut resolve = |query: SiteQuery<'_>| match query {
            SiteQuery::SameType(left, right) => {
                assert_eq!((left, right), ("Self", "Rhs"));
                same.then_some(SiteAnswer::NoPanic)
            }
            SiteQuery::Layout(..)
            | SiteQuery::SameTypeTest(..)
            | SiteQuery::LengthFits(..)
            | SiteQuery::FullRange(..)
            | SiteQuery::DistinctContainers(..) => None,
        };
        rewrite_std_site_markers(clause, &mut resolve)
    }

    #[test]
    fn a_same_type_marker_is_true_only_where_the_call_instantiates_one_type() {
        let clause = "__trust_wp_std_site_unmodelled_panic_unless_same_Self_Rhs()";
        assert_eq!(rewrite_same(clause, true), "true");
        assert_eq!(rewrite_same(clause, false), clause);
    }

    #[test]
    fn a_same_type_test_is_answered_both_ways_and_kept_when_unanswered() {
        let clause = "__trust_wp_std_site_same_Self_Rhs() || self@ >= rhs@";
        for answer in [Some(true), Some(false), None] {
            let mut resolve = |query: SiteQuery<'_>| match query {
                SiteQuery::SameTypeTest(left, right) => {
                    assert_eq!((left, right), ("Self", "Rhs"));
                    answer.map(SiteAnswer::Holds)
                }
                _ => None,
            };
            let out = rewrite_std_site_markers(clause, &mut resolve);
            let expected = match answer {
                Some(true) => "true || self@ >= rhs@",
                Some(false) => "false || self@ >= rhs@",
                None => clause,
            };
            assert_eq!(out, expected);
        }
    }

    #[test]
    fn the_refusing_same_type_marker_is_not_read_as_the_test() {
        let clause = "__trust_wp_std_site_unmodelled_panic_unless_same_Self_Rhs()";
        let mut resolve = |query: SiteQuery<'_>| match query {
            SiteQuery::SameTypeTest(..) => panic!("the refusing marker asked the test"),
            SiteQuery::SameType(..) => None,
            _ => None,
        };
        assert_eq!(rewrite_std_site_markers(clause, &mut resolve), clause);
    }

    #[test]
    fn a_length_marker_is_true_only_where_the_iterator_cannot_be_longer_than_usize() {
        let clause = "__trust_wp_std_site_unmodelled_panic_unless_length_fits_Self()";
        for fits in [true, false] {
            let mut resolve = |query: SiteQuery<'_>| match query {
                SiteQuery::LengthFits(param) => {
                    assert_eq!(param, "Self");
                    fits.then_some(SiteAnswer::NoPanic)
                }
                _ => None,
            };
            let out = rewrite_std_site_markers(clause, &mut resolve);
            assert_eq!(out, if fits { "true" } else { clause });
        }
    }

    #[test]
    fn a_distinct_containers_test_guards_the_disjointness_fact_both_ways() {
        let clause = "__trust_wp_std_site_distinct_containers_T() ==> arg0 != arg1";
        for answer in [Some(true), Some(false), None] {
            let mut resolve = |query: SiteQuery<'_>| match query {
                SiteQuery::DistinctContainers(param) => {
                    assert_eq!(param, "T");
                    answer.map(SiteAnswer::Holds)
                }
                _ => None,
            };
            let out = rewrite_std_site_markers(clause, &mut resolve);
            let expected = match answer {
                Some(true) => "true ==> arg0 != arg1",
                Some(false) => "false ==> arg0 != arg1",
                None => clause,
            };
            assert_eq!(out, expected);
        }
    }

    #[test]
    fn an_answered_guard_leaves_the_fact_or_nothing() {
        assert_eq!(
            settle_answered_guard("true ==> arg0 != arg1".to_string()),
            "arg0 != arg1"
        );
        assert_eq!(
            settle_answered_guard("false ==> arg0 != arg1".to_string()),
            "true"
        );
        let kept = "__trust_wp_std_site_distinct_containers_T() ==> arg0 != arg1";
        assert_eq!(settle_answered_guard(kept.to_string()), kept);
        let disjunction = "true || self@ >= rhs@";
        assert_eq!(settle_answered_guard(disjunction.to_string()), disjunction);
        for nested in [
            "true ==> a ==> b",
            "false ==> a <==> b",
            "true ==> a <==> b",
        ] {
            assert_eq!(settle_answered_guard(nested.to_string()), nested);
        }
    }

    #[test]
    fn a_full_range_marker_names_its_parameter() {
        let clause = "__trust_wp_std_site_unmodelled_panic_unless_full_range_R()";
        let mut resolve = |query: SiteQuery<'_>| match query {
            SiteQuery::FullRange(param) => {
                assert_eq!(param, "R");
                Some(SiteAnswer::NoPanic)
            }
            _ => None,
        };
        assert_eq!(rewrite_std_site_markers(clause, &mut resolve), "true");
    }

    #[test]
    fn size_marker_becomes_the_byte_count_of_the_named_parameter() {
        let out = rewrite(
            "capacity@ * __trust_wp_std_site_size_of_T() <= isize::MAX@",
            &|query, params| (query == LayoutQuery::Size && params == ["T"]).then_some(8),
        );
        assert_eq!(out, "capacity@ * 8 <= isize::MAX@");
    }

    #[test]
    fn tuple_marker_names_every_parameter_and_alignment_is_its_own_query() {
        let out = rewrite(
            "(__trust_wp_std_site_size_of_K_V() + 1) + __trust_wp_std_site_align_of_K_V()",
            &|query, params| {
                assert_eq!(params, ["K", "V"]);
                Some(match query {
                    LayoutQuery::Size => 24,
                    LayoutQuery::Align => 8,
                })
            },
        );
        assert_eq!(out, "(24 + 1) + 8");
    }

    #[test]
    fn an_unresolved_marker_is_kept_verbatim_so_the_encoder_refuses_it() {
        let clause = "n@ * __trust_wp_std_site_size_of_T() <= isize::MAX@";
        assert_eq!(rewrite(clause, &|_, _| None), clause);
    }

    #[test]
    fn the_unmodelled_panic_marker_is_never_resolved() {
        let clause = "__trust_wp_std_site_unmodelled_panic()";
        assert_eq!(rewrite(clause, &|_, _| Some(1)), clause);
    }

    #[test]
    fn a_marker_without_its_call_parentheses_is_not_rewritten() {
        let clause = "__trust_wp_std_site_size_of_T <= 1";
        assert_eq!(rewrite(clause, &|_, _| Some(1)), clause);
    }
}
