// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::{
    formula::{intern_sort_name, ExprSort, PureExpr},
    logic::is_invariant_method_name,
};

use super::ParsedContract;

/// Extract root variable name from a receiver expression,
/// stripping through Old/Deref/Final/View wrappers.
pub(in crate::callbacks) fn receiver_root_var_name(receiver: &PureExpr) -> Option<&str> {
    match receiver {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => receiver_root_var_name(inner),
        _ => None,
    }
}

/// Builtin logic-method names that a local USER `#[logic]` trait impl may
/// shadow for its own receiver type.
///
/// `is_builtin_method_call` blocks these names from the name-based
/// `LogicFnCall` rewrite because on Vec/Seq/slice receivers they carry
/// builtin encoder semantics. When a user writes
/// `impl IndexLogic<I> for MyAdt { #[logic] fn index_logic(self, i: I) .. }`,
/// calls with a `MyAdt`-sorted receiver must instead route through
/// `PureExpr::LogicFnCall` so the encoder emits the triggered defining
/// forall for the user impl — otherwise every such call lowers to a fully
/// uninterpreted `method_index_logic_..` UF (list_reversal_lasso).
///
/// Kept deliberately narrow: only names with a live user-shadowing use case.
const SHADOWABLE_BUILTIN_LOGIC_METHODS: &[&str] = &["index_logic"];

/// Per-method shadow resolution: receiver datatypes (interned ADT
/// `def_path_str` sort ids, matching `ty_to_expr_sort_enriched`) whose user
/// trait impl unambiguously shadows the builtin name, plus the impl method's
/// total arity (receiver included) for a call-shape sanity gate.
#[derive(Debug, Default)]
pub(in crate::callbacks) struct UserShadowedBuiltins {
    map: HashMap<String, (HashSet<u32>, usize)>,
}

impl UserShadowedBuiltins {
    pub(in crate::callbacks) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn matches(&self, method: &str, receiver_datatype: u32, total_args: usize) -> bool {
        self.map
            .get(method)
            .is_some_and(|(adts, arity)| adts.contains(&receiver_datatype) && *arity == total_args)
    }

    /// Whether `name` is a builtin method name shadowed by a user impl.
    pub(in crate::callbacks) fn contains_method(&self, name: &str) -> bool {
        self.map.contains_key(name)
    }

    /// Test-only constructor: one shadowed method for one receiver datatype.
    #[cfg(test)]
    pub(in crate::callbacks) fn for_test(
        method: &str,
        datatype_sort_id: u32,
        arity: usize,
    ) -> Self {
        let mut map = HashMap::new();
        map.insert(
            method.to_string(),
            (std::iter::once(datatype_sort_id).collect(), arity),
        );
        Self { map }
    }
}

/// Build the set of builtin logic-method names shadowed by local USER
/// `#[logic]` trait impls, keyed by receiver ADT sort.
///
/// A `(method, receiver ADT)` pair is included ONLY when ALL of:
/// - the method name is in `SHADOWABLE_BUILTIN_LOGIC_METHODS`;
/// - a local trait-impl associated fn of that name carries the `#[logic]`
///   marker and has a `self` receiver;
/// - the impl's trait ref is fully concrete (no generic params), its `Self`
///   type is a nominal ADT, and `Instance::try_resolve` (the same
///   monomorphization-faithful resolution codegen uses; mirrors
///   `open_logic_unfold::resolve_open_impl_body`) resolves the trait method
///   back to exactly this impl method;
/// - the short name is globally unambiguous among local `#[logic]` fns:
///   the encoder resolves `LogicFnCall` by bare name, so a second logic fn
///   with the same short name (another impl OR a free/inherent logic fn)
///   would collide — in that case the name is dropped entirely.
///
/// Every failure path falls closed to the builtin routing, i.e. the exact
/// pre-existing behavior. Fail-closed here can only cost completeness
/// (an opaque UF), never soundness.
pub(in crate::callbacks) fn build_user_shadowed_builtins(
    tcx: rustc_middle::ty::TyCtxt<'_>,
) -> UserShadowedBuiltins {
    use rustc_hir::def::DefKind;
    use rustc_middle::ty::{self, TypeVisitableExt};

    use crate::logic::discovery::has_logic_marker;

    // method name -> candidate (impl method DefId, receiver ADT sort id, arity)
    let mut candidates: HashMap<String, Vec<(rustc_hir::def_id::DefId, u32, usize)>> =
        HashMap::new();
    // short name -> count of ALL local #[logic] fns sharing it (collision gate)
    let mut logic_fn_name_counts: HashMap<String, usize> = HashMap::new();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        if !has_logic_marker(tcx.get_all_attrs(def_id)) {
            continue;
        }
        let short_name = tcx.item_name(def_id).to_string();
        if !SHADOWABLE_BUILTIN_LOGIC_METHODS.contains(&short_name.as_str()) {
            continue;
        }
        *logic_fn_name_counts.entry(short_name.clone()).or_insert(0) += 1;

        // Candidate gates: trait-impl assoc fn with a self receiver.
        let Some(assoc) = tcx.opt_associated_item(def_id) else {
            continue;
        };
        // TraitImpl container only (also yields the trait method DefId).
        let Some(trait_method_def_id) = assoc.trait_item_def_id() else {
            continue;
        };
        if !matches!(assoc.kind, ty::AssocKind::Fn { has_self: true, .. }) {
            continue;
        }
        let impl_def_id = tcx.parent(def_id);
        // Safe: TraitImpl container implies the parent is a trait impl.
        let trait_ref = tcx
            .impl_trait_ref(impl_def_id)
            .instantiate_identity()
            .skip_norm_wip();
        // Generic impls cannot be resolved under fully_monomorphized — fail
        // closed (builtin routing) rather than guess.
        if trait_ref.args.has_non_region_param() {
            continue;
        }
        let ty::TyKind::Adt(adt_def, _) = trait_ref.self_ty().kind() else {
            continue;
        };
        // Monomorphization-faithful resolution must select exactly this impl
        // method (guards specialization/blanket-impl surprises).
        let resolved = ty::Instance::try_resolve(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            trait_method_def_id,
            trait_ref.args,
        )
        .ok()
        .flatten()
        .and_then(|instance| match instance.def {
            ty::InstanceKind::Item(did) => Some(did),
            _ => None,
        });
        if resolved != Some(def_id) {
            continue;
        }
        let arity = tcx
            .fn_sig(def_id)
            .skip_binder()
            .inputs()
            .skip_binder()
            .len();
        let adt_sort_id = intern_sort_name(&tcx.def_path_str(adt_def.did()));
        candidates
            .entry(short_name)
            .or_default()
            .push((def_id, adt_sort_id, arity));
    }

    let mut map: HashMap<String, (HashSet<u32>, usize)> = HashMap::new();
    for (name, cands) in candidates {
        // Unambiguity: exactly one local #[logic] fn bears this short name
        // (so the by-name LogicFnCall resolution cannot pick a different def).
        if logic_fn_name_counts.get(&name) != Some(&1) {
            continue;
        }
        let [(_, adt_sort_id, arity)] = cands.as_slice() else {
            continue;
        };
        map.insert(name, (std::iter::once(*adt_sort_id).collect(), *arity));
    }
    UserShadowedBuiltins { map }
}

fn is_builtin_method_call(method: &str) -> bool {
    matches!(
        method,
        "len"
            | "index"
            | "index_logic"
            | "push_back"
            | "precondition"
            | "postcondition"
            | "postcondition_once"
            | "postcondition_mut"
            | "is_some"
            | "is_none"
            | "unwrap"
            | "is_ok"
            | "is_err"
            | "unwrap_err"
            | "contains"
    ) || is_invariant_method_name(method)
}

/// Rewrite user-defined logic method calls to `LogicFnCall` nodes.
///
/// Transforms `receiver.method(args)` -> `LogicFnCall("method", [receiver, ...args])`
/// for methods in `logic_method_names` that are not built-in methods.
pub(in crate::callbacks) fn rewrite_logic_method_calls_expr(
    expr: &PureExpr,
    logic_method_names: &HashSet<String>,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if logic_method_names.contains(&method) && !is_builtin_method_call(&method) => {
            let mut call_args = Vec::with_capacity(1 + args.len());
            call_args.push(Arc::unwrap_or_clone(receiver));
            call_args.extend(args);
            PureExpr::LogicFnCall {
                name: method,
                args: call_args,
            }
        }
        other => other,
    })
}

/// Shallow receiver sort resolution for the shadowed-builtin rewrite.
///
/// Reads `Var` sort annotations (falling back to `lookup` for unannotated
/// vars, e.g. logic-fn body params), peels `Old` (same sort), and peels one
/// reference layer per `Deref`/`Final`. Deliberately does NOT look through
/// `View` — `x@[i]` is Seq indexing and must keep builtin routing. Any
/// unresolvable receiver returns `None` (fail closed to builtin routing).
fn shallow_receiver_sort(
    receiver: &PureExpr,
    lookup: &dyn Fn(&str) -> Option<ExprSort>,
) -> Option<ExprSort> {
    match receiver {
        PureExpr::Var(name, sort) => sort.clone().or_else(|| lookup(name)),
        PureExpr::Old(inner) => shallow_receiver_sort(inner, lookup),
        PureExpr::Deref(inner) | PureExpr::Final(inner) => shallow_receiver_sort(inner, lookup)
            .map(|sort| match sort {
                ExprSort::Ref(inner) | ExprSort::MutRef(inner) => *inner,
                other => other,
            }),
        _ => None,
    }
}

/// Resolve a method receiver to a `Datatype` sort id, applying method-call
/// autoderef through at most one outer `&`/`&mut` layer.
fn receiver_datatype_sort_id(
    receiver: &PureExpr,
    lookup: &dyn Fn(&str) -> Option<ExprSort>,
) -> Option<u32> {
    match shallow_receiver_sort(receiver, lookup)? {
        ExprSort::Datatype(id) => Some(id),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => match *inner {
            ExprSort::Datatype(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

/// Rewrite builtin-named logic method calls whose receiver is an ADT with a
/// USER `#[logic]` trait impl into `LogicFnCall` nodes.
///
/// `receiver.index_logic(i)` / `receiver[i]` with a `Datatype`-sorted
/// receiver listed in `shadowed` becomes
/// `LogicFnCall("index_logic", [receiver, i])`, so the encoder registers the
/// user's logic fn and emits its triggered defining forall. Receivers that
/// do not resolve to a shadowing ADT (Vec/Seq/slice views, unannotated
/// vars, field projections) are left untouched — EXACTLY the pre-existing
/// builtin routing.
pub(in crate::callbacks) fn rewrite_user_shadowed_builtin_calls_expr(
    expr: &PureExpr,
    shadowed: &UserShadowedBuiltins,
    lookup: &dyn Fn(&str) -> Option<ExprSort>,
) -> PureExpr {
    if shadowed.is_empty() {
        return expr.clone();
    }
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if receiver_datatype_sort_id(&receiver, lookup)
            .is_some_and(|id| shadowed.matches(&method, id, 1 + args.len())) =>
        {
            let mut call_args = Vec::with_capacity(1 + args.len());
            call_args.push(Arc::unwrap_or_clone(receiver));
            call_args.extend(args);
            PureExpr::LogicFnCall {
                name: method,
                args: call_args,
            }
        }
        other => other,
    })
}

/// Apply the shadowed-builtin rewrite to all expressions in a parsed
/// contract. Must run AFTER `propagate_param_sort_annotations` (receiver
/// `Var` sorts are required) and BEFORE newtype field-0 simplification
/// (which could collapse `x.0` field projections onto the ADT var).
pub(super) fn rewrite_parsed_contract_shadowed_builtin_calls(
    parsed: &mut ParsedContract,
    shadowed: &UserShadowedBuiltins,
) {
    if shadowed.is_empty() {
        return;
    }
    parsed.rewrite_all_exprs(|expr| {
        rewrite_user_shadowed_builtin_calls_expr(expr, shadowed, &|_| None)
    });
}

/// Apply the shadowed-builtin rewrite to logic function definitions.
///
/// Logic-fn body `Var` nodes carry no sort annotations, so receiver sorts are
/// resolved from each function's own parameter sort hints. After the rewrite,
/// the shadowed def itself (e.g. `Memory::index_logic`) gets its recursion
/// flag re-detected: `detect_recursion` had counted the body's builtin
/// occurrences (`self.0[i]` parses to an `index_logic` MethodCall on the Vec
/// field) as self-calls, and that false flag makes the encoder suppress the
/// global defining axiom (`skip_global_quantified_axioms_for_datatype_logic`),
/// leaving the fn uninterpreted at every call site (list_reversal_lasso).
/// Genuine self-dispatch occurrences are LogicFnCall nodes after the rewrite,
/// so genuinely recursive shadowed impls stay flagged.
pub(in crate::callbacks) fn rewrite_logic_fn_defs_shadowed_builtin_calls(
    logic_fns: &mut [trust_wp_core::logic::LogicFnDef],
    shadowed: &UserShadowedBuiltins,
) {
    if shadowed.is_empty() {
        return;
    }
    for lf in logic_fns {
        let param_sorts: HashMap<String, ExprSort> = lf
            .params()
            .iter()
            .zip(
                lf.param_sorts()
                    .iter()
                    .chain(std::iter::repeat(&None::<ExprSort>)),
            )
            .filter_map(|(name, sort)| sort.clone().map(|s| (name.clone(), s)))
            .collect();
        let lookup = |name: &str| param_sorts.get(name).cloned();
        lf.set_body(rewrite_user_shadowed_builtin_calls_expr(
            lf.body(),
            shadowed,
            &lookup,
        ));
        for require in lf.requires_mut() {
            *require = rewrite_user_shadowed_builtin_calls_expr(require, shadowed, &lookup);
        }
        for ensure in lf.ensures_mut() {
            *ensure = rewrite_user_shadowed_builtin_calls_expr(ensure, shadowed, &lookup);
        }
        if shadowed.contains_method(lf.name()) {
            lf.redetect_recursion_logic_calls_only();
        }
    }
}

fn receiver_sort(receiver: &PureExpr) -> Option<&ExprSort> {
    match receiver {
        PureExpr::Var(_, sort) => sort.as_ref(),
        PureExpr::Old(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => {
            receiver_sort(inner)
        }
        _ => None,
    }
}

fn is_reference_sort(sort: &ExprSort) -> bool {
    matches!(sort, ExprSort::Ref(_) | ExprSort::MutRef(_))
}

/// Rewrite `(&T).deep_model()` to the model of the current dereferenced value.
///
/// Contract parsing preserves method syntax for trait-provided `deep_model`.
/// When the receiver is an annotated reference, the mathematical model is the
/// view of the referent, not an opaque UF over the reference carrier.
pub(in crate::callbacks) fn rewrite_ref_deep_model_calls_expr(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "deep_model"
            && args.is_empty()
            && receiver_sort(&receiver).is_some_and(is_reference_sort) =>
        {
            PureExpr::View(Arc::new(PureExpr::Deref(receiver)))
        }
        other => other,
    })
}

/// Apply logic method call rewriting to all expressions in a parsed contract.
pub(super) fn rewrite_parsed_contract_logic_method_calls(
    parsed: &mut ParsedContract,
    logic_method_names: &HashSet<String>,
) {
    if logic_method_names.is_empty() {
        return;
    }
    parsed.rewrite_all_exprs(|expr| rewrite_logic_method_calls_expr(expr, logic_method_names));
}

/// Apply reference-receiver `deep_model()` rewriting to all contract expressions.
pub(super) fn rewrite_ref_deep_model_calls_in_contract(parsed: &mut ParsedContract) {
    parsed.rewrite_all_exprs(rewrite_ref_deep_model_calls_expr);
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

    use super::{
        rewrite_ref_deep_model_calls_expr, rewrite_user_shadowed_builtin_calls_expr,
        UserShadowedBuiltins,
    };

    fn memory_shadows() -> UserShadowedBuiltins {
        UserShadowedBuiltins::for_test("index_logic", intern_sort_name("Memory"), 2)
    }

    fn memory_sort() -> ExprSort {
        ExprSort::Datatype(intern_sort_name("Memory"))
    }

    fn index_logic_call(receiver: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Var("i".to_string(), Some(ExprSort::Int))],
        }
    }

    fn expected_logic_fn_call(receiver: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: "index_logic".to_string(),
            args: vec![
                receiver,
                PureExpr::Var("i".to_string(), Some(ExprSort::Int)),
            ],
        }
    }

    #[test]
    fn shadowed_builtin_rewrites_datatype_receiver() {
        let receiver = PureExpr::Var("self".to_string(), Some(memory_sort()));
        let rewritten = rewrite_user_shadowed_builtin_calls_expr(
            &index_logic_call(receiver.clone()),
            &memory_shadows(),
            &|_| None,
        );
        assert_eq!(rewritten, expected_logic_fn_call(receiver));
    }

    #[test]
    fn shadowed_builtin_rewrites_ref_receiver_autoderef() {
        let receiver = PureExpr::Var(
            "self".to_string(),
            Some(ExprSort::Ref(Box::new(memory_sort()))),
        );
        let rewritten = rewrite_user_shadowed_builtin_calls_expr(
            &index_logic_call(receiver.clone()),
            &memory_shadows(),
            &|_| None,
        );
        assert_eq!(rewritten, expected_logic_fn_call(receiver));
    }

    #[test]
    fn shadowed_builtin_rewrites_deref_and_final_of_mut_ref() {
        let mut_ref_self = PureExpr::Var(
            "self".to_string(),
            Some(ExprSort::MutRef(Box::new(memory_sort()))),
        );
        for wrap in [PureExpr::Deref, PureExpr::Final] {
            let receiver = wrap(Arc::new(mut_ref_self.clone()));
            let rewritten = rewrite_user_shadowed_builtin_calls_expr(
                &index_logic_call(receiver.clone()),
                &memory_shadows(),
                &|_| None,
            );
            assert_eq!(rewritten, expected_logic_fn_call(receiver));
        }
    }

    #[test]
    fn shadowed_builtin_resolves_receiver_via_lookup() {
        let receiver = PureExpr::Var("self".to_string(), None);
        let lookup = |name: &str| (name == "self").then(memory_sort);
        let rewritten = rewrite_user_shadowed_builtin_calls_expr(
            &index_logic_call(receiver.clone()),
            &memory_shadows(),
            &lookup,
        );
        assert_eq!(rewritten, expected_logic_fn_call(receiver));
    }

    #[test]
    fn shadowed_builtin_leaves_seq_receiver() {
        let expr = index_logic_call(PureExpr::Var("s".to_string(), Some(ExprSort::Seq)));
        let rewritten =
            rewrite_user_shadowed_builtin_calls_expr(&expr, &memory_shadows(), &|_| None);
        assert_eq!(rewritten, expr);
    }

    #[test]
    fn shadowed_builtin_leaves_view_receiver() {
        // `x@[i]` — View receivers are Seq indexing even when x is the ADT.
        let expr = index_logic_call(PureExpr::View(Arc::new(PureExpr::Var(
            "self".to_string(),
            Some(memory_sort()),
        ))));
        let rewritten =
            rewrite_user_shadowed_builtin_calls_expr(&expr, &memory_shadows(), &|_| None);
        assert_eq!(rewritten, expr);
    }

    #[test]
    fn shadowed_builtin_leaves_unannotated_receiver() {
        let expr = index_logic_call(PureExpr::Var("mystery".to_string(), None));
        let rewritten =
            rewrite_user_shadowed_builtin_calls_expr(&expr, &memory_shadows(), &|_| None);
        assert_eq!(rewritten, expr);
    }

    #[test]
    fn shadowed_builtin_leaves_other_datatype_receiver() {
        let expr = index_logic_call(PureExpr::Var(
            "b".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("Board"))),
        ));
        let rewritten =
            rewrite_user_shadowed_builtin_calls_expr(&expr, &memory_shadows(), &|_| None);
        assert_eq!(rewritten, expr);
    }

    #[test]
    fn shadowed_builtin_leaves_arity_mismatch() {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self".to_string(), Some(memory_sort()))),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(1)],
        };
        let rewritten =
            rewrite_user_shadowed_builtin_calls_expr(&expr, &memory_shadows(), &|_| None);
        assert_eq!(rewritten, expr);
    }

    #[test]
    fn shadowed_builtin_rewrites_nested_receivers_only() {
        // self[s[i]] — outer receiver is Memory (rewritten), inner is Seq (kept).
        let seq_index = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), Some(ExprSort::Seq))),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Var("i".to_string(), Some(ExprSort::Int))],
        };
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self".to_string(), Some(memory_sort()))),
            method: "index_logic".to_string(),
            args: vec![seq_index.clone()],
        };
        let rewritten =
            rewrite_user_shadowed_builtin_calls_expr(&expr, &memory_shadows(), &|_| None);
        assert_eq!(
            rewritten,
            PureExpr::LogicFnCall {
                name: "index_logic".to_string(),
                args: vec![
                    PureExpr::Var("self".to_string(), Some(memory_sort())),
                    seq_index,
                ],
            }
        );
    }

    #[test]
    fn rewrite_ref_deep_model_to_view_of_deref() {
        let self_var = PureExpr::Var(
            "self".to_string(),
            Some(ExprSort::Ref(Box::new(ExprSort::Int))),
        );
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(self_var.clone()),
            method: "deep_model".to_string(),
            args: vec![],
        };

        let rewritten = rewrite_ref_deep_model_calls_expr(&expr);

        assert_eq!(
            rewritten,
            PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(self_var))))
        );
    }

    #[test]
    fn rewrite_ref_deep_model_recurses_through_logic_args() {
        let receiver = PureExpr::Var(
            "self".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        );
        let expr = PureExpr::LogicFnCall {
            name: "hash_log".to_string(),
            args: vec![PureExpr::MethodCall {
                receiver: Arc::new(receiver.clone()),
                method: "deep_model".to_string(),
                args: vec![],
            }],
        };

        let rewritten = rewrite_ref_deep_model_calls_expr(&expr);

        assert_eq!(
            rewritten,
            PureExpr::LogicFnCall {
                name: "hash_log".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    receiver
                ))))],
            }
        );
    }

    #[test]
    fn rewrite_ref_deep_model_leaves_non_ref_receiver() {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
            method: "deep_model".to_string(),
            args: vec![],
        };

        assert_eq!(rewrite_ref_deep_model_calls_expr(&expr), expr);
    }

    #[test]
    fn rewrite_ref_deep_model_leaves_calls_with_args() {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(
                "x".to_string(),
                Some(ExprSort::Ref(Box::new(ExprSort::Int))),
            )),
            method: "deep_model".to_string(),
            args: vec![PureExpr::Int(0)],
        };

        assert_eq!(rewrite_ref_deep_model_calls_expr(&expr), expr);
    }

    #[test]
    fn rewrite_ref_deep_model_inside_binary_expr() {
        let receiver = PureExpr::Var(
            "self".to_string(),
            Some(ExprSort::Ref(Box::new(ExprSort::Int))),
        );
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(receiver.clone()),
                method: "deep_model".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        );

        let rewritten = rewrite_ref_deep_model_calls_expr(&expr);

        assert_eq!(
            rewritten,
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    receiver
                ))))),
                BinOp::Eq,
                Arc::new(PureExpr::Int(1)),
            )
        );
    }
}
