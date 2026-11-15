// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use super::{
    trust_formula::{
        decode_trust_formula_v1_claim, decode_trust_formula_v1_declared_claim,
        validate_native_replay_definedness,
    },
    BundleClaim, BundleClaimFormat, BundleDiagnostic, BundleObligation,
};
use crate::{
    contract_parser::{parse_claim_binding_facts, ContractElisions, WrittenTypeSite},
    formula::{
        elaborate::{
            bind_facts_to_the_written_prefix, dereferenced, elaborate, first_unmodeled_dereference,
            infer_name_uses, Dereference, NativeNameUse,
        },
        BinOp, ExprSort, PureExpr, UnOp,
    },
};

/// Parsed native proof input for a bundle obligation.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeBundlePredicate {
    pub obligation_id: String,
    pub claim_format: NativeClaimFormat,
    pub predicate: PureExpr,
}

/// Native claim formats with a real decoder into [`PureExpr`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeClaimFormat {
    TrustWpPureExprV1,
    TrustFormulaV1,
}

impl NativeClaimFormat {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TrustWpPureExprV1 => "TrustWpPureExprV1",
            Self::TrustFormulaV1 => "TrustFormulaV1",
        }
    }
}

/// Convert a bundle obligation claim into trust-wp's native predicate IR.
///
/// The decoded predicate IS the goal, whatever its shape: `Verified` means the
/// predicate is valid, so `!P` is proved as `!P` and `A && !B` as the
/// conjunction it says. Nothing in a [`BundleClaim`] marks a claim as a
/// violation condition, and a claim's shape is never read as one: a producer
/// holding a verification condition `V`, whose unsatisfiability is what it
/// wants shown, sends `!V`.
///
/// This is intentionally fail-closed: only claim formats with a real typed
/// decoder into [`PureExpr`] are accepted as native proof input. Opaque formats
/// remain valid interchange artifacts, not replay claims.
pub fn native_predicate_for_obligation(
    obligation: &BundleObligation,
) -> Result<NativeBundlePredicate, BundleDiagnostic> {
    // A summary fact is about the binders the claim opens with as written:
    // each is bound there before any rewrite moves a quantifier.
    let fact_names = super::proof::summary_fact_names(&obligation.summary_facts);
    let (claim_format, predicate) = match &obligation.claim.format {
        BundleClaimFormat::TrustWpPureExprV1 => (
            NativeClaimFormat::TrustWpPureExprV1,
            decode_pure_expr_claim(&obligation.claim, &fact_names).map_err(|message| {
                BundleDiagnostic::invalid(
                    "obligation.claim.payload",
                    format!("obligation `{}` has {message}", obligation.id),
                )
            })?,
        ),
        BundleClaimFormat::TrustFormulaV1 => (
            NativeClaimFormat::TrustFormulaV1,
            decode_trust_formula_v1_claim(obligation.claim.payload.trim())
                .map(|claim| bind_facts_to_the_written_prefix(&claim, &fact_names))
                .map_err(|err| {
                    BundleDiagnostic::invalid(
                        "obligation.claim.payload",
                        format!(
                            "obligation `{}` has invalid TrustFormulaV1 claim payload: {err}",
                            obligation.id
                        ),
                    )
                })?,
        ),
        BundleClaimFormat::SmtLib2 => return Err(opaque_format_diagnostic(obligation, "SMT-LIB2")),
        BundleClaimFormat::Other(format) => {
            return Err(opaque_format_diagnostic(obligation, format.as_str()));
        }
    };

    // Every subterm's sort, decided once over the whole claim; each check
    // below and native replay read these sorts.
    let elaboration = elaborate(&predicate);

    // `*e` reads the sort `e` references. A dereference of a name no binder
    // makes a reference, or of a reference to a sort native replay does not
    // model, has no sort to read: `forall<v: bool> *v + 1 > *v` and
    // `forall<p: &T> *p + 1 > *p` were each read as integer arithmetic.
    if let Some(unmodeled) = first_unmodeled_dereference(&elaboration.typed) {
        return Err(BundleDiagnostic::invalid(
            "obligation.claim.payload",
            format!(
                "obligation `{}` has no one reading: {unmodeled}",
                obligation.id
            ),
        ));
    }

    // A name the goal reads at two sorts has no one meaning, bound or not,
    // free or bound inside the claim: `((x : bool) == (x : bool)) && x + 1 > x`
    // is two claims about two different `x`s, and proving each half about its
    // own `x` proves nothing about the one written; `forall<v: bool> (v : Int)
    // + 1 > v` reads its `v` at a sort the binder does not range over, and
    // `forall<p: &bool> *p + 1 > *p` reads `p` as a reference to a `Bool` and
    // to an `Int`.
    if let Some((name, first, second)) = elaboration.conflict {
        return Err(BundleDiagnostic::invalid(
            "obligation.claim.payload",
            format!(
                "obligation `{}` reads `{name}` at both {first} and {second}, so the claim has no \
                 one reading",
                obligation.id
            ),
        ));
    }

    if !is_boolean_predicate(&elaboration.typed) {
        return Err(BundleDiagnostic::invalid(
            "obligation.claim.payload",
            format!(
                "obligation `{}` claim payload is not a typed boolean predicate",
                obligation.id
            ),
        ));
    }

    Ok(NativeBundlePredicate {
        obligation_id: obligation.id.clone(),
        claim_format,
        predicate,
    })
}

/// A name a claim's goal is stated over, and how the claim reads it.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClaimName {
    pub name: String,
    /// The sort the claim declares the name at: a `TrustFormulaV1` top-level
    /// declaration. `None` for a pure-expr predicate, which declares none.
    pub declared: Option<ExprSort>,
    /// The sort the goal's uses read the name at.
    pub used: NativeNameUse,
}

/// The names a claim's goal is stated over, read by the decoder that produces
/// the goal: the names free in the goal, in first-use order, each with the
/// sort the claim declares it at and the sort its uses read it at.
///
/// For `TrustFormulaV1` these are the top-level declarations the body uses,
/// defaults included; a declared name the body never reads free is not one.
/// For `TrustWpPureExprV1`, the free names of the predicate, which declares
/// no sorts. A name bound inside the claim (`let`, a quantifier) is not one
/// either. `None` for a claim with no typed decoder or one that does not
/// decode: neither is native proof input, so neither can be verified.
#[must_use]
pub fn native_claim_names(claim: &BundleClaim) -> Option<Vec<NativeClaimName>> {
    let (goal, declarations) = match &claim.format {
        BundleClaimFormat::TrustFormulaV1 => {
            let decoded = decode_trust_formula_v1_declared_claim(claim.payload.trim()).ok()?;
            (decoded.body, decoded.declarations)
        }
        // Binding a fact renames only bound names, so the free ones are read
        // without the facts.
        BundleClaimFormat::TrustWpPureExprV1 => (
            decode_pure_expr_claim(claim, &HashSet::new()).ok()?,
            Vec::new(),
        ),
        BundleClaimFormat::SmtLib2 | BundleClaimFormat::Other(_) => return None,
    };
    Some(
        infer_name_uses(&goal)
            .into_iter()
            .map(|(name, used)| NativeClaimName {
                declared: declarations
                    .iter()
                    .find(|(declared, _)| *declared == name)
                    .map(|(_, sort)| sort.clone()),
                name,
                used,
            })
            .collect(),
    )
}

fn decode_pure_expr_claim(
    claim: &BundleClaim,
    fact_names: &HashSet<String>,
) -> Result<PureExpr, String> {
    let (predicate, elisions) = parse_claim_binding_facts(claim.payload.trim(), fact_names)
        .map_err(|err| format!("invalid TrustWpPureExprV1 claim payload: {err}"))?;
    if let Some(unmodeled) = first_unmodeled_elision(&elisions) {
        return Err(format!(
            "a TrustWpPureExprV1 claim the pure-expr reading does not model: it writes {unmodeled}"
        ));
    }
    validate_native_replay_definedness(&predicate)
        .map_err(|err| format!("undefined TrustWpPureExprV1 arithmetic: {err}"))?;
    Ok(predicate)
}

/// The first thing a pure-expr claim writes that its AST does not carry
/// faithfully, described for the refusal.
///
/// A pure-expr claim declares no sorts: every name is read as an unbounded
/// `Int` or a `Bool` ([`native_claim_names`]). What the parser keeps of a
/// written type is exactly that: a cast is lowered to Rust's `as` (or never
/// parses), and an ascription or `let` annotation to `Int` or `bool` becomes
/// the sort of its operand. Everything else the parser drops, and a verdict
/// over the rest would be about a claim other than the one written: a
/// machine-integer ascription, `let` annotation or literal suffix (a width
/// the reading cannot check, or that types the operators around it), an
/// `Int` or `bool` annotation on an operand the AST gives no sort
/// (`(*p : Int)` read the `*p` of a `p: &bool` as an integer), a binder over
/// a type the AST does not record or native replay does not model
/// (`forall<v: u8>` over a width native replay does not model, `forall<v>`
/// over no stated domain, `forall<v: T>` and `forall<s: [Int]>` over values
/// that are not integers), a statement a block drops (an assertion or lemma whose
/// effect is lost with it), a borrow no `*` reads through (the AST keeps `e`
/// for `&e`: `let r = &p; r == q` compares `p`, where the claim compares a
/// reference to `p`), and a reference pattern outside a `let` (`match p {
/// &t => .. }` binds `t` to `p`, where the pattern binds it to `*p`).
fn first_unmodeled_elision(elisions: &ContractElisions) -> Option<String> {
    let checked_sort = |text: &str| matches!(text, "Int" | "bool");
    let written =
        elisions.written_types.iter().find_map(|written| {
            let text = written.text.as_deref();
            match (written.site, text) {
                (WrittenTypeSite::Cast, _) => None,
                (WrittenTypeSite::Ascription, Some(text)) if checked_sort(text) => None,
                (WrittenTypeSite::LetBinding, Some(text)) if checked_sort(text) => None,
                (WrittenTypeSite::Ascription, text) => {
                    Some(format!("type ascription `: {}`", text.unwrap_or("_")))
                }
                (WrittenTypeSite::LetBinding, text) => {
                    Some(format!("`let` annotation `: {}`", text.unwrap_or("_")))
                }
                (WrittenTypeSite::LiteralSuffix, Some("int")) => None,
                (WrittenTypeSite::LiteralSuffix, text) => {
                    Some(format!("literal type suffix `{}`", text.unwrap_or("_")))
                }
                (WrittenTypeSite::QuantifierBinder | WrittenTypeSite::ClosureParam, None) => {
                    Some("a binder with no written type".to_string())
                }
                (WrittenTypeSite::QuantifierBinder, Some(text)) => (!recorded_binder_type(text))
                    .then(|| format!("quantifier binder type `{text}`")),
                (WrittenTypeSite::ClosureParam, Some(text)) => (!recorded_binder_type(text))
                    .then(|| format!("closure parameter type `{text}`")),
            }
        });
    written
        .or_else(|| {
            elisions.unchecked_annotations.first().map(|annotation| {
                format!("{annotation}, an operand whose sort it neither records nor checks")
            })
        })
        .or_else(|| {
            elisions
                .discarded_statements
                .first()
                .map(|statement| format!("the statement `{statement}`, which a block drops"))
        })
        .or_else(|| {
            elisions
                .dropped_borrows
                .first()
                .map(|borrow| format!("the borrow `{borrow}`, whose reference the AST drops"))
        })
        .or_else(|| {
            elisions.dropped_reference_patterns.first().map(|pattern| {
                format!("the reference pattern `{pattern}`, whose reference level the AST drops")
            })
        })
}

/// A binder type the AST records as a sort native replay models: `Int`,
/// `bool`, or a reference, which native replay reads as a pointer (to a type
/// parameter or a slice of one, among others). A machine integer, or a
/// reference to one, is read at `Int` under the range the AST states for it
/// (D-203, D-204), a width native replay does not model, and any other type
/// maps to no sort native replay models: a bare type parameter `T` could be
/// any type, and was read as an integer (`forall<v: T> v + 1 > v`); a slice
/// `[T]` is a sequence, and was read as one too (`forall<s: [Int]> s + 1 > s`).
fn recorded_binder_type(text: &str) -> bool {
    let text = text.trim();
    if let Some(referent) = text
        .strip_prefix("&mut ")
        .or_else(|| text.strip_prefix('&'))
    {
        return recorded_referent_type(referent);
    }
    matches!(text, "Int" | "bool")
}

/// A type a reference binder may point at, as the AST records it: `Int`,
/// `bool`, a type parameter, a reference, or a slice of one of these.
fn recorded_referent_type(text: &str) -> bool {
    let text = text.trim();
    if let Some(referent) = text
        .strip_prefix("&mut ")
        .or_else(|| text.strip_prefix('&'))
    {
        return recorded_referent_type(referent);
    }
    if let Some(element) = text
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
    {
        return recorded_referent_type(element);
    }
    let mut chars = text.chars();
    matches!(text, "Int" | "bool")
        || matches!((chars.next(), chars.next()), (Some(ch), None) if ch.is_ascii_uppercase())
}

fn opaque_format_diagnostic(obligation: &BundleObligation, format: &str) -> BundleDiagnostic {
    BundleDiagnostic::invalid(
        "obligation.claim.format",
        format!(
            "obligation `{}` uses opaque claim format `{format}`; native proof input requires a typed decoder into PureExpr",
            obligation.id
        ),
    )
}

/// Whether an elaborated claim is a boolean native replay can read: every
/// subterm at a sort it models, the whole a `Bool`.
fn is_boolean_predicate(typed: &PureExpr) -> bool {
    matches!(infer_native_sort(typed), Some(NativeExprSort::Bool))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeExprSort {
    Bool,
    Int,
    Pointer(NativePointerKind),
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativePointerKind {
    Thin,
    Fat,
}

/// The sort native replay reads an elaborated subterm at: a name at its
/// elaborated sort (with none, the unsorted `Unknown` an integer is read
/// at), and every other node from its operands'.
fn infer_native_sort(expr: &PureExpr) -> Option<NativeExprSort> {
    match expr {
        PureExpr::Bool(_) => Some(NativeExprSort::Bool),
        PureExpr::Int(_) => Some(NativeExprSort::Int),
        PureExpr::Var(_, sort) => match sort {
            Some(sort) => native_sort_from_expr_sort(sort),
            None => Some(NativeExprSort::Unknown),
        },
        PureExpr::BinOp(left, op, right) => match op {
            BinOp::Eq | BinOp::Ne => {
                compatible_comparison(left, right).then_some(NativeExprSort::Bool)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                int_like(left).then_some(())?;
                int_like(right).then_some(NativeExprSort::Bool)
            }
            BinOp::And | BinOp::Or | BinOp::Implies => bool_like(left, right),
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::DivTrunc
            | BinOp::RemTrunc
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::BitOr => {
                int_like(left).then_some(())?;
                int_like(right).then_some(NativeExprSort::Int)
            }
        },
        PureExpr::UnOp(UnOp::Not, inner) => {
            (infer_native_sort(inner)? == NativeExprSort::Bool).then_some(NativeExprSort::Bool)
        }
        PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, inner) => {
            int_like(inner).then_some(NativeExprSort::Int)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            (infer_native_sort(cond)? == NativeExprSort::Bool).then_some(())?;
            merge_branch_sorts(infer_native_sort(then_expr)?, infer_native_sort(else_expr)?)
        }
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            (infer_native_sort(body)? == NativeExprSort::Bool).then_some(NativeExprSort::Bool)
        }
        PureExpr::Let { body, .. } | PureExpr::Closure { body, .. } => infer_native_sort(body),
        PureExpr::LetAssume { assumption, body } => bool_like(assumption, body),
        PureExpr::LetObligation { obligation, body } => bool_like(obligation, body),
        PureExpr::Old(inner) => infer_native_sort(inner),
        // The view of an integer is that integer; native replay models the
        // view of no other sort.
        PureExpr::View(inner) => match infer_native_sort(inner)? {
            sort @ (NativeExprSort::Int | NativeExprSort::Unknown) => Some(sort),
            NativeExprSort::Bool | NativeExprSort::Pointer(_) => None,
        },
        // `*e` and `^e` read the sort `e` references, and nothing where `e`
        // is no reference to a sort native replay models.
        PureExpr::Deref(operand) => dereferenced(operand, Dereference::Current)
            .referent()
            .and_then(|referent| native_sort_from_expr_sort(&referent)),
        PureExpr::Final(operand) => dereferenced(operand, Dereference::Final)
            .referent()
            .and_then(|referent| native_sort_from_expr_sort(&referent)),
        PureExpr::Float(_)
        | PureExpr::MethodCall { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. } => None,
    }
}

fn bool_like(left: &PureExpr, right: &PureExpr) -> Option<NativeExprSort> {
    (infer_native_sort(left)? == NativeExprSort::Bool).then_some(())?;
    (infer_native_sort(right)? == NativeExprSort::Bool).then_some(NativeExprSort::Bool)
}

fn int_like(expr: &PureExpr) -> bool {
    matches!(
        infer_native_sort(expr),
        Some(NativeExprSort::Int | NativeExprSort::Unknown)
    )
}

fn compatible_comparison(left: &PureExpr, right: &PureExpr) -> bool {
    left == right || sorts_compatible(infer_native_sort(left), infer_native_sort(right))
}

fn sorts_compatible(left: Option<NativeExprSort>, right: Option<NativeExprSort>) -> bool {
    matches!(
        (left, right),
        (Some(NativeExprSort::Unknown), Some(_))
            | (Some(_), Some(NativeExprSort::Unknown))
            | (Some(NativeExprSort::Bool), Some(NativeExprSort::Bool))
            | (Some(NativeExprSort::Int), Some(NativeExprSort::Int))
            | (
                Some(NativeExprSort::Pointer(_)),
                Some(NativeExprSort::Pointer(_))
            )
    )
}

fn merge_branch_sorts(left: NativeExprSort, right: NativeExprSort) -> Option<NativeExprSort> {
    match (left, right) {
        (NativeExprSort::Unknown, sort) | (sort, NativeExprSort::Unknown) => Some(sort),
        (NativeExprSort::Bool, NativeExprSort::Bool) => Some(NativeExprSort::Bool),
        (NativeExprSort::Int, NativeExprSort::Int) => Some(NativeExprSort::Int),
        (NativeExprSort::Pointer(left), NativeExprSort::Pointer(right)) if left == right => {
            Some(NativeExprSort::Pointer(left))
        }
        _ => None,
    }
}

fn native_sort_from_expr_sort(sort: &ExprSort) -> Option<NativeExprSort> {
    match sort {
        ExprSort::Bool => Some(NativeExprSort::Bool),
        ExprSort::Int => Some(NativeExprSort::Int),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => Some(NativeExprSort::Pointer(
            pointer_kind_from_referent_sort(inner),
        )),
        // A type parameter could be any type; reading it as an integer (the
        // `Unknown` an unsorted name is) proved `v + 1 > v` over it.
        ExprSort::TypeParam(_)
        | ExprSort::Seq
        | ExprSort::Unit
        | ExprSort::Datatype(_)
        | ExprSort::FMap
        | ExprSort::Tuple(_)
        | ExprSort::Float(_) => None,
    }
}

fn pointer_kind_from_referent_sort(sort: &ExprSort) -> NativePointerKind {
    match sort {
        ExprSort::Seq | ExprSort::FMap => NativePointerKind::Fat,
        _ => NativePointerKind::Thin,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::formula::elaborate::NativeUseSort;

    /// The first name `claim` reads at two sorts.
    fn name_read_at_two_sorts(claim: &PureExpr) -> Option<(String, NativeUseSort, NativeUseSort)> {
        elaborate(claim).conflict
    }

    /// Whether `claim`, elaborated, is a boolean native replay can read.
    fn is_boolean(claim: &PureExpr) -> bool {
        is_boolean_predicate(&elaborate(claim).typed)
    }

    fn var(name: &str, sort: Option<ExprSort>) -> Arc<PureExpr> {
        Arc::new(PureExpr::Var(name.to_string(), sort))
    }

    /// `v + 1 > v`, each `v` read at `sort`.
    fn successor_gt(sort: Option<ExprSort>) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                var("v", sort.clone()),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
            BinOp::Gt,
            var("v", sort),
        )
    }

    fn forall(sort: ExprSort, body: PureExpr) -> PureExpr {
        PureExpr::Forall {
            var: "v".to_string(),
            var_sort: Some(sort),
            body: Arc::new(body),
            triggers: Vec::new(),
        }
    }

    /// The claim-side readings of a bound name, independent of the parser
    /// that refuses these spellings first: `forall<v: bool> (v : Int) + 1 >
    /// (v : Int)` verified when native sort inference preferred the
    /// annotation to the binder and the two-sort check read free names only.
    #[test]
    fn a_bound_name_is_read_at_its_binders_sort() {
        let annotated_against_binder = forall(ExprSort::Bool, successor_gt(Some(ExprSort::Int)));
        assert_eq!(
            name_read_at_two_sorts(&annotated_against_binder),
            Some(("v".to_string(), NativeUseSort::Int, NativeUseSort::Bool))
        );
        assert!(!is_boolean(&annotated_against_binder));

        // A `let` name is read at its value's sort: `t` is the bool `v`.
        let let_bound = forall(
            ExprSort::Bool,
            PureExpr::Let {
                var: "t".to_string(),
                value: var("v", None),
                body: Arc::new(PureExpr::BinOp(
                    var("t", Some(ExprSort::Int)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                )),
            },
        );
        assert!(matches!(
            name_read_at_two_sorts(&let_bound),
            Some((_, NativeUseSort::Int, NativeUseSort::Bool))
        ));

        // A binder over a sort native replay does not model is not an
        // integer: `forall<v: T> v + 1 > v`, `forall<s: [Int]> s + 1 > s`.
        for sort in [
            ExprSort::TypeParam(crate::formula::intern_sort_name("T")),
            ExprSort::Seq,
        ] {
            assert!(
                !is_boolean(&forall(sort.clone(), successor_gt(None))),
                "{sort}"
            );
        }

        // Controls: the binder's own sort, spelled or not.
        for body in [successor_gt(None), successor_gt(Some(ExprSort::Int))] {
            let claim = forall(ExprSort::Int, body);
            assert_eq!(name_read_at_two_sorts(&claim), None);
            assert!(is_boolean(&claim));
        }
    }
}
