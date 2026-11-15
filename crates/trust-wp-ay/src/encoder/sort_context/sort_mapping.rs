// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical sort classification and `ExprSort`/ay `Sort` translation helpers.

use std::{collections::HashSet, fmt::Write};

use ay_dpll::api::{DatatypeSort, Sort};
use trust_wp_core::formula::{intern_sort_name, resolve_sort_name, ExprSort};

use crate::encoder::unsoundness;

const MUTREF_SORT_PREFIX: &str = "__trust_wp_mutref::";

/// Encode a type parameter sort name for ay.
fn decode_type_param_sort_name(_name: &str) -> Option<u32> {
    // Without a dedicated prefix, bare-name TypeParam sorts are
    // indistinguishable from Datatype sorts in ay. Return None so
    // ay_sort_to_expr_sort falls through to Datatype. The lossy
    // TypeParam→Datatype roundtrip is acceptable: both map to the
    // same Uninterpreted sort, and the ExprSort distinction only
    // matters for expression-level inference annotations.
    None
}

fn encode_name_component(name: &str) -> String {
    let mut encoded = String::with_capacity(name.len() * 2);
    for byte in name.as_bytes() {
        let _ = write!(&mut encoded, "{byte:02x}");
    }
    encoded
}

fn decode_name_component(encoded: &str) -> Option<String> {
    if !encoded.len().is_multiple_of(2) {
        return None;
    }
    let bytes = (0..encoded.len())
        .step_by(2)
        .map(|idx| u8::from_str_radix(&encoded[idx..idx + 2], 16).ok())
        .collect::<Option<Vec<_>>>()?;
    String::from_utf8(bytes).ok()
}

fn encode_mutref_inner_sort(sort: &ExprSort) -> String {
    match sort {
        ExprSort::Bool => "bool".to_string(),
        ExprSort::Int => "int".to_string(),
        ExprSort::Seq => "seq".to_string(),
        ExprSort::Unit => "unit".to_string(),
        ExprSort::Datatype(id) => {
            format!(
                "datatype_{}",
                encode_name_component(&resolve_sort_name(*id))
            )
        }
        ExprSort::FMap => "fmap".to_string(),
        ExprSort::Tuple(arity) => format!("tuple_{arity}"),
        ExprSort::Ref(inner) => format!("ref_{}", encode_mutref_inner_sort(inner)),
        ExprSort::MutRef(inner) => format!("mutref_{}", encode_mutref_inner_sort(inner)),
        ExprSort::TypeParam(id) => {
            format!(
                "typeparam_{}",
                encode_name_component(&resolve_sort_name(*id))
            )
        }
        ExprSort::Float(width) => format!("float_{}", width.rust_name()),
        #[allow(unreachable_patterns)]
        _ => "int".to_string(),
    }
}

fn decode_mutref_inner_sort(encoded: &str) -> Option<ExprSort> {
    match encoded {
        "bool" => Some(ExprSort::Bool),
        "int" => Some(ExprSort::Int),
        "seq" => Some(ExprSort::Seq),
        "unit" => Some(ExprSort::Unit),
        "fmap" => Some(ExprSort::FMap),
        "float_f32" => Some(ExprSort::Float(trust_wp_core::formula::FloatWidth::F32)),
        "float_f64" => Some(ExprSort::Float(trust_wp_core::formula::FloatWidth::F64)),
        other => {
            if let Some(rest) = other.strip_prefix("datatype_") {
                return decode_name_component(rest)
                    .map(|name| ExprSort::Datatype(intern_sort_name(&name)));
            }
            if let Some(rest) = other.strip_prefix("typeparam_") {
                return decode_name_component(rest)
                    .map(|name| ExprSort::TypeParam(intern_sort_name(&name)));
            }
            if let Some(rest) = other.strip_prefix("tuple_") {
                return rest.parse::<u8>().ok().map(ExprSort::Tuple);
            }
            if let Some(rest) = other.strip_prefix("ref_") {
                return decode_mutref_inner_sort(rest).map(|inner| ExprSort::Ref(Box::new(inner)));
            }
            if let Some(rest) = other.strip_prefix("mutref_") {
                return decode_mutref_inner_sort(rest)
                    .map(|inner| ExprSort::MutRef(Box::new(inner)));
            }
            None
        }
    }
}

fn encode_mutref_sort_name(inner: &ExprSort) -> String {
    format!("{MUTREF_SORT_PREFIX}{}", encode_mutref_inner_sort(inner))
}

fn decode_mutref_sort_name(name: &str) -> Option<ExprSort> {
    name.strip_prefix(MUTREF_SORT_PREFIX)
        .and_then(decode_mutref_inner_sort)
        .map(|inner| ExprSort::MutRef(Box::new(inner)))
}

/// #prophecy-slots (Fix B M1, blueprint C2): separator for instantiation-aware
/// stdlib `Option` annotation names.
///
/// `Option<&mut T>` must be a DIFFERENT `ExprSort` from `Option<T>`; the
/// driver appends this separator plus the mutref inner-sort grammar encoding
/// of the payload's `ExprSort` (e.g. `std::option::Option__twpm0_mutref_int`
/// for `Option<&mut i32>`). ADTs that embed no `&mut` keep byte-identical
/// names, so the passing corpus sees zero name churn.
///
/// The separator cannot collide with the token grammar: tokens are built from
/// the fixed words `bool|int|seq|unit|fmap|float|datatype_|typeparam_|
/// tuple_|ref_|mutref_` plus lowercase hex, none of which contain the letter
/// `w`. A user type whose own path embeds this marker fails the `Option`
/// base-name check or the token decode and falls back to an opaque
/// (non-conflated, inert) sort — fail-closed in the harmless direction.
pub const MUTREF_INSTANTIATION_SEP: &str = "__twpm0_";

/// Build the instantiation-aware annotation name for `Option<{payload}>`
/// where `payload` is a mutable reference (`ExprSort::MutRef`). Driver-facing
/// (re-exported from the crate root): the driver mints the name, the encoder
/// parses it back with [`parse_mutref_instantiated_option`] — one grammar,
/// one owner, no drift.
pub fn mutref_instantiated_option_name(path: &str, payload: &ExprSort) -> String {
    format!(
        "{path}{MUTREF_INSTANTIATION_SEP}{}",
        encode_mutref_inner_sort(payload)
    )
}

/// Parse an instantiation-suffixed stdlib `Option` annotation name back to
/// its payload `ExprSort`. Returns `Some(payload)` only for names minted by
/// [`mutref_instantiated_option_name`] on a stdlib `Option` path whose payload
/// is a mutable reference — or (M2) a CARRIER TUPLE, the
/// `Option<(&mut T, ..)>` shape; everything else is `None` (the caller keeps
/// the legacy resolution).
pub(crate) fn parse_mutref_instantiated_option(name: &str) -> Option<ExprSort> {
    let (base, token) = name.split_once(MUTREF_INSTANTIATION_SEP)?;
    let bare = base.rsplit("::").next().unwrap_or(base);
    if bare != "Option" {
        return None;
    }
    let payload = decode_mutref_inner_sort(token)?;
    match &payload {
        ExprSort::MutRef(_) => Some(payload),
        // #prophecy-slots (Fix B M2): a carrier-tuple payload. The name is
        // re-validated by `parse_mutref_carrier_tuple` (which itself requires
        // at least one MutRef element), so a hand-written look-alike cannot
        // route a non-carrier sort through this lane.
        ExprSort::Datatype(id) if parse_mutref_carrier_tuple(&resolve_sort_name(*id)).is_some() => {
            Some(payload)
        }
        _ => None,
    }
}

/// #prophecy-slots (Fix B M2): prefix for the CARRIER TUPLE sort — the
/// instantiation-aware sort of a tuple that embeds at least one `&mut`
/// element.
///
/// `split_first_mut` returns `Option<(&mut T, &mut [T])>`: the take_first_mut
/// sibling-binder shape. `ExprSort::Tuple(arity)` records only the arity, so
/// `(&mut T, U)` and `(T, U)` are the same annotation and the whole tuple
/// punned onto the single global `Uninterpreted("Tuple{arity}")` sort — the
/// positional getters then ranged over `Int` and the `&mut` payload lost its
/// prophecy slot exactly as an ADT field did before M1.
///
/// The carrier tuple sort names its element sorts, so
/// `__trust_wp_tuple_get_i` is declared per instantiation (the getter family
/// is signature-keyed) with the mutref record sort as its range.
pub const MUTREF_TUPLE_SORT_PREFIX: &str = "__trust_wp_mutref_tuple::";

/// Element separator inside a carrier-tuple sort name.
///
/// `__` cannot occur INSIDE a token: the grammar's words
/// (`bool|int|seq|unit|fmap|float|legacy`) contain no `__`, and the
/// parameterized forms are a single-underscore prefix
/// (`datatype_|typeparam_|tuple_|ref_|mutref_`) followed by either lowercase
/// hex, digits, or another token — none of which can start with `_`. So
/// splitting on `__` recovers exactly the element list.
const MUTREF_TUPLE_ELEM_SEP: &str = "__";

/// Token for a tuple element whose sort the driver could not resolve, or which
/// carries no `&mut`. Such an element keeps its LEGACY inference (today's
/// behaviour, still fail-closed under the Fix A guard when a `^` reaches it) —
/// this milestone lowers only the elements it can lower, and says so in the
/// sort name rather than guessing.
const MUTREF_TUPLE_LEGACY_ELEM: &str = "legacy";

/// Build the carrier-tuple sort name for a tuple whose elements are the given
/// `ExprSort`s (`None` = unresolved, recorded as `legacy`). Driver-facing.
///
/// Returns `None` unless at least one element IS a mutable reference: a tuple
/// with no `&mut` must keep the byte-identical legacy `Tuple{arity}` sort so
/// the passing corpus sees zero churn.
#[must_use]
pub fn mutref_carrier_tuple_sort_name(elements: &[Option<ExprSort>]) -> Option<String> {
    if !elements
        .iter()
        .any(|elem| matches!(elem, Some(ExprSort::MutRef(_))))
    {
        return None;
    }
    let tokens = elements
        .iter()
        .map(|elem| match elem {
            Some(sort @ ExprSort::MutRef(_)) => encode_mutref_inner_sort(sort),
            _ => MUTREF_TUPLE_LEGACY_ELEM.to_string(),
        })
        .collect::<Vec<_>>();
    Some(format!(
        "{MUTREF_TUPLE_SORT_PREFIX}{}",
        tokens.join(MUTREF_TUPLE_ELEM_SEP)
    ))
}

/// Parse a carrier-tuple sort name back to its per-element sorts. `None`
/// entries are `legacy` elements (keep the caller's own inference).
///
/// Fail-closed: a name that does not decode completely, or that carries no
/// `MutRef` element, returns `None` and the caller keeps the legacy lane.
pub(crate) fn parse_mutref_carrier_tuple(name: &str) -> Option<Vec<Option<ExprSort>>> {
    let rest = name.strip_prefix(MUTREF_TUPLE_SORT_PREFIX)?;
    if rest.is_empty() {
        return None;
    }
    let elements = rest
        .split(MUTREF_TUPLE_ELEM_SEP)
        .map(|token| {
            if token == MUTREF_TUPLE_LEGACY_ELEM {
                return Some(None);
            }
            match decode_mutref_inner_sort(token) {
                Some(sort @ ExprSort::MutRef(_)) => Some(Some(sort)),
                // A non-`MutRef` token in a carrier-tuple name is not a
                // spelling this module mints. Refuse the whole name.
                _ => None,
            }
        })
        .collect::<Option<Vec<_>>>()?;
    elements
        .iter()
        .any(std::option::Option::is_some)
        .then_some(elements)
}

/// Is this ay sort the carrier-tuple sort? (Name-level test; the sort itself
/// is uninterpreted, exactly like the mutref record sort.)
pub(crate) fn carrier_tuple_element_sorts(sort: &Sort) -> Option<Vec<Option<ExprSort>>> {
    match sort {
        Sort::Uninterpreted(name) => parse_mutref_carrier_tuple(name),
        _ => None,
    }
}

/// Create the canonical ay Sort for FMap-typed terms. (#2059 Phase 2)
pub(crate) fn fmap_sort() -> Sort {
    Sort::Uninterpreted("FMap".to_string())
}

/// Create the canonical ay Sort for Unit-typed terms. (#2059 Phase 2)
pub(crate) fn unit_sort() -> Sort {
    Sort::Uninterpreted("Unit".to_string())
}

/// Check if a bare type name represents a Seq-model type. (#2124, #2155, #2207)
///
/// Note: `List` is intentionally excluded. In Creusot compat tests, `List` is a
/// user-defined recursive enum (`Cons | Nil`) that must use Datatype encoding.
/// Including it caused `self_current` to be declared as `Seq(Int)` from sort
/// inference, conflicting with the `Datatype(Adt_Cons_Nil)` from match encoding.
/// The standard library `LinkedList` is covered by its full name. (#2231)
pub(crate) fn is_seq_model_type(type_name: &str) -> bool {
    matches!(type_name, "Vec" | "VecDeque" | "Seq" | "LinkedList")
}

/// Check if a bare type name represents an FMap-model type. (#1965)
pub(crate) fn is_fmap_model_type(type_name: &str) -> bool {
    matches!(type_name, "FMap" | "HashMap" | "GhostMap")
}

/// Check if a bare type name represents a Mapping (total function) type. (#2317)
pub(crate) fn is_mapping_model_type(type_name: &str) -> bool {
    type_name == "Mapping"
}

/// Create the canonical ay Sort for Mapping-typed terms. (#2317)
pub(crate) fn mapping_sort() -> Sort {
    Sort::Uninterpreted("Mapping".to_string())
}

/// Check if a bare type name represents an Int-model type. (#1965, #2155)
///
/// Transparent wrapper types (`Rc`, `Arc`, `Box`) are included because their
/// `Deref` and `deep_model` produce the inner type. For `Rc<i32>` etc. this
/// maps to Int, matching the sort of postcondition RHS values and avoiding the
/// sort-mismatch coercion that silently drops constraints. (#976)
pub(crate) fn is_int_model_type(type_name: &str) -> bool {
    matches!(
        type_name,
        "Snapshot"
            | "Ghost"
            | "Int"
            | "Duration"
            | "Instant"
            | "HashSet"
            | "GhostSet"
            | "FSet"
            | "NonNeg"
            | "RangeInclusive"
            | "NonZeroU8"
            | "NonZeroU16"
            | "NonZeroU32"
            | "NonZeroU64"
            | "NonZeroU128"
            | "NonZeroUsize"
            | "NonZeroI8"
            | "NonZeroI16"
            | "NonZeroI32"
            | "NonZeroI64"
            | "NonZeroI128"
            | "NonZeroIsize"
            | "Rc"
            | "Arc"
            | "Box"
    )
}

/// The name of the uninterpreted Seq carrier sort.
pub(crate) const SEQ_CARRIER_SORT_NAME: &str = "Seq";

/// Which ay `Sort` carries trust-wp's `Seq` model inside one encoding session.
///
/// trust-wp never uses ay's native sequence *operations*: every sequence fact
/// is modelled through the UF projectors that `ensure_seq_theory` declares
/// (`seq_len`, `seq_index_logic`, `seq_push_back`, …). The carrier those
/// projectors range over is therefore a free choice — but it must be exactly
/// ONE choice per encoder, because the sort plan declares the *variables* the
/// projectors are applied to. When the two disagree, `Solver::apply` fails its
/// domain-sort check.
///
/// The choice is not cosmetic. ay's
/// `unsat_proof_references_uncheckable_seq_theory` withholds strict proof
/// authority from any refutation that mentions a `Sort::Seq(_)` term, because
/// carcara rejects such a problem at parse time. A lane that wants certifiable
/// proofs must therefore keep every Seq-sorted term on the uninterpreted
/// carrier — variables included, which is what makes carrier-awareness in this
/// stateless converter necessary rather than merely tidy.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum SeqCarrier {
    /// ay's native sequence sort, `(Seq Int)`.
    ///
    /// The historical default, and still the right choice in lanes whose logic
    /// already puts uncheckable theories (arrays, native datatypes) in the
    /// proof, where an uninterpreted carrier would buy no certifiability.
    #[default]
    Native,
    /// A plain uninterpreted sort named `Seq`.
    Uninterpreted,
}

impl SeqCarrier {
    /// The ay `Sort` this carrier denotes.
    pub(crate) fn sort(self) -> Sort {
        match self {
            Self::Native => Sort::seq(Sort::Int),
            Self::Uninterpreted => Sort::Uninterpreted(SEQ_CARRIER_SORT_NAME.to_string()),
        }
    }

    /// Classify an already-minted sort as a Seq carrier, or `None` when the
    /// sort does not carry a Seq at all.
    ///
    /// Deliberately narrow: only the two spellings this enum can produce
    /// count. `Datatype("Vec")` and `Uninterpreted("Vec")` are seq-*family*
    /// sorts (see `is_seq_family_sort`) but they are not carriers — they are
    /// source-level collection names that still need bridging, and rewriting
    /// them here would silently erase that distinction.
    pub(crate) fn classify(sort: &Sort) -> Option<Self> {
        match sort {
            Sort::Seq(_) => Some(Self::Native),
            Sort::Uninterpreted(name) if name == SEQ_CARRIER_SORT_NAME => Some(Self::Uninterpreted),
            _ => None,
        }
    }
}

/// Rewrite a Seq carrier spelling to `carrier`, leaving every other sort alone.
///
/// This is the one-way funnel used where a sort minted by the *stateless*
/// converter meets a *stateful* encoder: the plan's declarations, domain-sort
/// hints, and registered-sort projections. Sorts that are not Seq carriers
/// pass through untouched.
pub(crate) fn retarget_seq_carrier(sort: Sort, carrier: SeqCarrier) -> Sort {
    match SeqCarrier::classify(&sort) {
        Some(existing) if existing != carrier => carrier.sort(),
        _ => sort,
    }
}

/// Canonical sort category for Rust type names. Single source of truth for
/// `normalize_sort`, `expr_sort_to_ay_sort`, and `sort_from_expr_sort`. (#2187)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CanonicalSort {
    Seq,
    FMap,
    Mapping,
    Int,
    Uninterpreted(String),
}

/// Classify a potentially-qualified Rust type name into its canonical sort
/// category. Strips module paths, then checks the `is_*_model_type` predicates.
/// Check ordering is safe because the type sets are disjoint. (#2187)
pub(crate) fn canonical_sort(qualified_name: &str) -> CanonicalSort {
    let bare = qualified_name.rsplit("::").next().unwrap_or(qualified_name);
    if is_seq_model_type(bare) {
        CanonicalSort::Seq
    } else if is_fmap_model_type(bare) {
        CanonicalSort::FMap
    } else if is_mapping_model_type(bare) {
        CanonicalSort::Mapping
    } else if is_int_model_type(bare) {
        CanonicalSort::Int
    } else {
        CanonicalSort::Uninterpreted(bare.to_string())
    }
}

/// Map an `ExprSort` annotation directly to a ay `Sort`, without requiring
/// a wrapping `PureExpr`. Used by both the `Var` arms of `infer_expr_sort`
/// and the `Ref` recursive unwrap. Also used by `verify::setup::datatype_predecl`
/// to convert driver-provided `AdtDecl` field sorts to ay sorts. (#1982)
pub(crate) fn expr_sort_to_ay_sort(sort: &ExprSort) -> Sort {
    expr_sort_to_ay_sort_for_carrier(sort, SeqCarrier::Native)
}

/// Map an `ExprSort` annotation to a ay `Sort`, minting Seq-sorted results on
/// `carrier` instead of the default native sequence sort.
///
/// Callers that have an encoder in hand should route through this (or through
/// the stateful `sort_from_expr_sort`) so the sort they hand to a declaration
/// agrees with the carrier `ensure_seq_theory` declared the projectors over.
pub(crate) fn expr_sort_to_ay_sort_for_carrier(sort: &ExprSort, carrier: SeqCarrier) -> Sort {
    match sort {
        ExprSort::Bool => Sort::Bool,
        ExprSort::Int => Sort::Int,
        ExprSort::Seq => carrier.sort(),
        ExprSort::Unit => unit_sort(),
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            // #prophecy-slots (Fix B M1): an instantiation-suffixed
            // `Option<&mut T>` annotation maps to the specialized carrier
            // Option family. This stateless lane returns the family NAME as
            // an uninterpreted sort (precedent: `logic_fn_sort.rs` returns
            // `Uninterpreted(stdlib_option_datatype_for_payload(..).name)`);
            // the stateful `sort_from_expr_sort` declares the datatype and
            // returns the native sort. Both lanes agree on the name, so
            // variable declarations reconcile through the registry upgrade.
            if let Some(payload) = parse_mutref_instantiated_option(&name) {
                let payload_sort = expr_sort_to_ay_sort_for_carrier(&payload, carrier);
                return Sort::Uninterpreted(
                    crate::encoder::match_enc::stdlib_option_datatype_for_payload(payload_sort)
                        .name,
                );
            }
            // #prophecy-slots (Fix B M2): the carrier tuple sort is
            // uninterpreted and its NAME is the instantiation — it must never
            // be routed through `canonical_sort`, whose `rsplit("::")` would
            // strip the prefix and conflate it with a bare element list.
            if parse_mutref_carrier_tuple(&name).is_some() {
                return Sort::Uninterpreted(name);
            }
            match canonical_sort(&name) {
                CanonicalSort::Int => Sort::Int,
                CanonicalSort::Seq => carrier.sort(),
                CanonicalSort::FMap => fmap_sort(),
                CanonicalSort::Mapping => mapping_sort(),
                CanonicalSort::Uninterpreted(bare) => Sort::Uninterpreted(bare),
            }
        }
        ExprSort::FMap => fmap_sort(),
        ExprSort::Tuple(arity) => Sort::Uninterpreted(format!("Tuple{arity}")),
        // TypeParam sorts (from generic type parameters like `T`) resolve to Int.
        // In monomorphic verification, call sites pass concrete sorts (Int, Bool,
        // etc.) for generic params. Using Uninterpreted("T") causes sort mismatches
        // everywhere: variable declarations, logic function calls, method dispatch.
        // Int is the universal sort — all concrete instantiations are compatible.
        // (#2551: previously Uninterpreted, causing __apply_coerce disconnections
        // and SortFallbackToInt demotions.)
        ExprSort::TypeParam(_) => Sort::Int,
        ExprSort::Float(width) => crate::encoder::pure_encoding::ieee::float_sort(*width),
        ExprSort::Ref(inner) => expr_sort_to_ay_sort_for_carrier(inner, carrier),
        ExprSort::MutRef(inner) => Sort::Uninterpreted(encode_mutref_sort_name(inner)),
        // ExprSort is #[non_exhaustive]; required for cross-crate match.
        // AUDIT(#2663): Currently unreachable — all ExprSort variants
        // (Int, Bool, Unit, Seq, Datatype, FMap, Tuple, TypeParam, Float,
        // Ref, MutRef) are matched above. Reclassified from HIGH
        // SortFallbackToInt to LOW SortFallbackToIntFromCatchAll
        // per #2663 Phase 1a — catch-all is future-proofing only.
        #[allow(unreachable_patterns)]
        _ => {
            unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromCatchAll);
            Sort::Int
        }
    }
}

/// Whether a SORT NAME is one of the mut-ref prophecy carriers this module's
/// grammar mints: the `(current, final, id)` record sort
/// (`__trust_wp_mutref::*`, #2141), the carrier TUPLE sort
/// (`__trust_wp_mutref_tuple::*`, Fix B M2), or an instantiation-suffixed
/// carrier `Option` (`…Option__twpm0_mutref_…`, Fix B M1 blueprint C2).
///
/// One owner: all three spellings are minted in this file, so the recognizer
/// lives beside them and cannot drift.
fn name_is_mut_ref_carrier(name: &str) -> bool {
    name.starts_with(MUTREF_SORT_PREFIX)
        || name.starts_with(MUTREF_TUPLE_SORT_PREFIX)
        || parse_mutref_instantiated_option(name).is_some()
}

/// Whether an ay `Sort` IS, or transitively CONTAINS, a mut-ref prophecy
/// carrier.
///
/// Used by the fail-closed guard on the Seq-element restore route
/// (`encoder/seq/coercion.rs` `try_restore_seq_element_from_int`). A restore
/// term is `__seq_index_restore_<sort>(seq, index)` — a FUNCTION of the Seq and
/// the index ALONE — so minting one at a carrier sort makes any two borrows
/// harmonized against the same Seq element the SAME term, forcing `a == b` and
/// with it `id(a) == id(b)`: the bug/869 borrow-identity collapse
/// (`memory/bug869-snapshot-mutref-erasure.md` BLOCKER 3).
///
/// Deliberately NARROWER than Fix A's `sort_embeds_mut_ref`, which is
/// fail-closed on any unresolvable `Datatype`. Fail-closing that widely here
/// would refuse the legitimate Mapping / List / user-ADT restores this route
/// exists for (#2316, #2699). Only a sort that actually carries a prophecy slot
/// can suffer an identity collapse, and those sorts are exactly the ones this
/// grammar names — so this is the narrowest condition that closes the route.
///
/// Recursion is bounded by a name seen-set: an edge back to a datatype already
/// being examined contributes no NEW carrier evidence.
pub(crate) fn ay_sort_contains_mut_ref_carrier(sort: &Sort) -> bool {
    ay_sort_contains_mut_ref_carrier_with(sort, &|_| None)
}

/// As [`ay_sort_contains_mut_ref_carrier`], but resolving
/// `Sort::Uninterpreted(name)` spellings of DECLARED datatypes through
/// `resolve` before concluding they carry nothing.
///
/// Needed because a carrier-payload `Option` family reaches the encoder under
/// two spellings. `stdlib_option_datatype_for_payload` hex-encodes the payload
/// sort into the family NAME (`Option` + `U<hex>`), which is NOT the carrier
/// grammar this module's `name_is_mut_ref_carrier` recognizes — so the
/// `Uninterpreted` spelling is only decidable from the declaration, whose
/// `Some` field sits at the carrier sort. Callers with encoder access should
/// pass a registry lookup; the resolver-free wrapper above is for the
/// name-only lanes.
pub(crate) fn ay_sort_contains_mut_ref_carrier_with(
    sort: &Sort,
    resolve: &dyn Fn(&str) -> Option<DatatypeSort>,
) -> bool {
    let mut seen = HashSet::new();
    contains_mut_ref_carrier_inner(sort, resolve, &mut seen)
}

fn contains_mut_ref_carrier_inner(
    sort: &Sort,
    resolve: &dyn Fn(&str) -> Option<DatatypeSort>,
    seen: &mut HashSet<String>,
) -> bool {
    match sort {
        Sort::Uninterpreted(name) | Sort::TypeVar(name) => {
            if name_is_mut_ref_carrier(name) {
                return true;
            }
            if !seen.insert(name.clone()) {
                return false;
            }
            resolve(name).is_some_and(|dt| constructors_contain_mut_ref_carrier(&dt, resolve, seen))
        }
        Sort::Datatype(dt) => {
            if name_is_mut_ref_carrier(&dt.name) {
                return true;
            }
            if !seen.insert(dt.name.clone()) {
                return false;
            }
            constructors_contain_mut_ref_carrier(dt, resolve, seen)
        }
        Sort::Seq(inner) => contains_mut_ref_carrier_inner(inner, resolve, seen),
        Sort::Array(arr) => {
            contains_mut_ref_carrier_inner(&arr.index_sort, resolve, seen)
                || contains_mut_ref_carrier_inner(&arr.element_sort, resolve, seen)
        }
        // Scalar / opaque sorts carry no prophecy slot.
        _ => false,
    }
}

fn constructors_contain_mut_ref_carrier(
    dt: &DatatypeSort,
    resolve: &dyn Fn(&str) -> Option<DatatypeSort>,
    seen: &mut HashSet<String>,
) -> bool {
    dt.constructors.iter().any(|ctor| {
        ctor.fields
            .iter()
            .any(|field| contains_mut_ref_carrier_inner(&field.sort, resolve, seen))
    })
}

/// Reverse-map a ay `Sort` to an `ExprSort` annotation for `PureExpr::Var`.
///
/// Returns `None` for `Sort::Int` (the default) to maintain backward compatibility
/// with existing code that treats `None` as Int. This is the inverse of
/// `expr_sort_to_ay_sort`, used when constructing `PureExpr` nodes from ay Sorts
/// in loop encoding and mut-borrow setup. (#994 Step 2e, #2040)
///
/// Handles all ExprSort-mapped sorts:
/// - `Sort::Bool` → `ExprSort::Bool`
/// - `Sort::Seq(_)` → `ExprSort::Seq`
/// - `Sort::Uninterpreted("FMap")` → `ExprSort::FMap`
/// - `Sort::Uninterpreted("Unit")` → `ExprSort::Unit`
/// - `Sort::Uninterpreted("Tuple<N>")` → `ExprSort::Tuple(N)`
/// - `Sort::Uninterpreted("__trust_wp_typaram::<name>")` → `ExprSort::TypeParam(intern(<name>))`
/// - `Sort::Uninterpreted(<other>)` → `ExprSort::Datatype(intern(<other>))`
/// - a floating-point sort of `f32`/`f64`'s format → `ExprSort::Float`
/// - All others (Int, BitVec, Array, etc.) → `None`
pub(crate) fn ay_sort_to_expr_sort(sort: &Sort) -> Option<ExprSort> {
    match sort {
        Sort::Bool => Some(ExprSort::Bool),
        Sort::Int => None,
        sort @ Sort::FloatingPoint(..) => {
            crate::encoder::pure_encoding::ieee::sort_float_width(sort).map(ExprSort::Float)
        }
        Sort::Seq(_) => Some(ExprSort::Seq),
        Sort::Uninterpreted(name) => match name.as_str() {
            "FMap" => Some(ExprSort::FMap),
            "Mapping" => Some(ExprSort::Datatype(intern_sort_name("Mapping"))),
            "Unit" => Some(ExprSort::Unit),
            other => {
                if let Some(sort) = decode_mutref_sort_name(other) {
                    return Some(sort);
                }
                if let Some(id) = decode_type_param_sort_name(other) {
                    return Some(ExprSort::TypeParam(id));
                }
                if let Some(arity_str) = other.strip_prefix("Tuple") {
                    if let Ok(arity) = arity_str.parse::<u8>() {
                        return Some(ExprSort::Tuple(arity));
                    }
                }
                Some(ExprSort::Datatype(intern_sort_name(other)))
            }
        },
        // ay-native Datatype sort (from match encoding declarations).
        // The DatatypeSort carries its name, which we intern for ExprSort.
        Sort::Datatype(dt) => Some(ExprSort::Datatype(intern_sort_name(&dt.name))),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
