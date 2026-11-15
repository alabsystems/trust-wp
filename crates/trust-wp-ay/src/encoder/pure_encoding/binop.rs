// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use ay_dpll::api::{DatatypeSort, Sort, Term};
use tracing::debug;
use trust_wp_core::formula::{
    internal::tuple_lowering::{
        tuple_field_logic_fn_index, tuple_logic_fn_arity, TUPLE_FIELD_LOGIC_FN_PREFIX,
    },
    BinOp, ExprSort, PureExpr, UnOp,
};

use super::{
    super::{
        coerce_to_numeric,
        sort_context::{
            is_seq_family_sort, resolve_nameable_expr, resolve_view_var_name, DerivedKind,
        },
        AYEncoder, NumericOperandMode,
    },
    fold_int_truncate_const, parse_int_truncate_name, strip_low_bitop_marker,
};
use crate::{
    encoder::{
        extract_inner_var_annotation,
        ground_pool::AxiomKind,
        match_enc::{
            datatype_constructor_matches, datatype_constructor_name, short_constructor_name,
        },
        quantifier::pure_quantifier::is_sort_agnostic_equal,
    },
    error::EncodingError,
};

const BITWISE_PROOF_BV_WIDTH: u32 = 64;

enum OptionConstructor<'a> {
    Some(&'a PureExpr),
    None,
}

fn fmap_get_method_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if !matches!(method.as_str(), "get" | "get_ghost" | "get_mut_ghost") || args.len() != 1 {
        return None;
    }
    Some((receiver.as_ref(), &args[0]))
}

fn option_constructor(expr: &PureExpr) -> Option<OptionConstructor<'_>> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    match short_constructor_name(name) {
        "Some" if args.len() == 1 => Some(OptionConstructor::Some(&args[0])),
        "None" if args.is_empty() => Some(OptionConstructor::None),
        _ => None,
    }
}

fn is_stdlib_none_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            args.is_empty()
                && short_constructor_name(name) == "None"
                && matches!(
                    crate::encoder::match_enc::stdlib_constructor_target(name),
                    Some(crate::encoder::match_enc::SwitchTarget::OptionInt)
                )
        }
        PureExpr::Var(name, _) => short_constructor_name(name) == "None",
        _ => false,
    }
}

fn option_datatype_from_sort(sort: &Sort) -> Option<DatatypeSort> {
    let Sort::Datatype(datatype) = sort else {
        return None;
    };
    if !datatype.name.starts_with("Option") {
        return None;
    }
    let has_none = datatype.constructors.iter().any(|constructor| {
        datatype_constructor_matches(datatype, &constructor.name, "None")
            && constructor.fields.is_empty()
    });
    let has_some = datatype
        .constructors
        .iter()
        .any(|constructor| datatype_constructor_matches(datatype, &constructor.name, "Some"));
    (has_none && has_some).then(|| datatype.clone())
}

fn fmap_method_call(receiver: &PureExpr, method: &str, key: &PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver.clone()),
        method: method.to_string(),
        args: vec![key.clone()],
    }
}

fn fmap_insert_expr(receiver: &PureExpr, key: &PureExpr, value: &PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver.clone()),
        method: "insert".to_string(),
        args: vec![key.clone(), value.clone()],
    }
}

fn fmap_get_some_formula(receiver: &PureExpr, key: &PureExpr, value: &PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(fmap_method_call(receiver, "contains", key)),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(fmap_method_call(receiver, "lookup", key)),
            BinOp::Eq,
            Arc::new(value.clone()),
        )),
    )
}

fn int_literal(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        _ => None,
    }
}

fn positive_int_literal(expr: &PureExpr) -> Option<i64> {
    int_literal(expr).filter(|value| *value > 0)
}

fn div_by_positive_int_literal(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(dividend, BinOp::Div, divisor) = expr else {
        return None;
    };
    Some((dividend.as_ref(), positive_int_literal(divisor)?))
}

fn bin_expr(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
}

fn positive_const_div_comparison_expr(
    quotient: &PureExpr,
    dividend: &PureExpr,
    divisor: i64,
    op: BinOp,
) -> Option<PureExpr> {
    let divisor_expr = PureExpr::Int(divisor);
    let quotient_times_divisor = bin_expr(quotient.clone(), BinOp::Mul, divisor_expr.clone());
    let next_quotient = bin_expr(quotient.clone(), BinOp::Add, PureExpr::Int(1));
    let next_quotient_times_divisor = bin_expr(next_quotient, BinOp::Mul, divisor_expr);
    let exact_multiple = bin_expr(quotient_times_divisor.clone(), BinOp::Eq, dividend.clone());

    match op {
        BinOp::Eq => Some(bin_expr(
            exact_multiple,
            BinOp::Or,
            bin_expr(
                bin_expr(quotient_times_divisor.clone(), BinOp::Le, dividend.clone()),
                BinOp::And,
                bin_expr(
                    dividend.clone(),
                    BinOp::Lt,
                    next_quotient_times_divisor.clone(),
                ),
            ),
        )),
        BinOp::Ne => Some(bin_expr(
            bin_expr(dividend.clone(), BinOp::Lt, quotient_times_divisor.clone()),
            BinOp::Or,
            bin_expr(
                next_quotient_times_divisor.clone(),
                BinOp::Le,
                dividend.clone(),
            ),
        )),
        // The sole caller reaches this only for Eq/Ne, but a caller's guard is
        // not this function's contract and `unreachable!` is a panic the
        // verifier has to discharge. `None` routes the impossible case through
        // the "cannot encode this" path the caller already has.
        _ => None,
    }
}

fn nonnegative_single_bit_mask(expr: &PureExpr) -> Option<u64> {
    let value = int_literal(expr)?;
    let mask = u64::try_from(value).ok()?;
    (mask == 0 || mask.is_power_of_two()).then_some(mask)
}

fn bitand_single_bit_mask(expr: &PureExpr) -> Option<(&PureExpr, u64)> {
    let PureExpr::BinOp(left, BinOp::BitAnd, right) = strip_low_bitop_marker(expr) else {
        return None;
    };
    if let Some(mask) = nonnegative_single_bit_mask(right) {
        return Some((left.as_ref(), mask));
    }
    nonnegative_single_bit_mask(left).map(|mask| (right.as_ref(), mask))
}

fn shl_one_mask(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(left, BinOp::Shl, shift) = strip_low_bitop_marker(expr) else {
        return None;
    };
    (int_literal(left) == Some(1)).then_some(shift.as_ref())
}

fn bitand_shl_one_mask(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::BitAnd, right) = strip_low_bitop_marker(expr) else {
        return None;
    };
    if let Some(shift) = shl_one_mask(right) {
        return Some((left.as_ref(), shift));
    }
    shl_one_mask(left).map(|shift| (right.as_ref(), shift))
}

fn is_same_shl_one_mask(value: &PureExpr, shift: &PureExpr) -> bool {
    shl_one_mask(value).is_some_and(|value_shift| is_sort_agnostic_equal(value_shift, shift))
}

fn fold_known_layout_const(name: &str) -> Option<PureExpr> {
    match name {
        "USIZE_BITS" => Some(PureExpr::Int((std::mem::size_of::<usize>() * 8) as i64)),
        _ => None,
    }
}

fn inline_local_lets(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Let { var, value, body } => {
            let mut substitutions = HashMap::new();
            substitutions.insert(var.clone(), inline_local_lets(value));
            inline_local_lets(&body.substitute(&substitutions))
        }
        PureExpr::Var(name, _) => fold_known_layout_const(name).unwrap_or_else(|| expr.clone()),
        PureExpr::LogicFnCall { name, args } => {
            let args: Vec<_> = args.iter().map(inline_local_lets).collect();
            if let Some((target_bits, signed)) = parse_int_truncate_name(name) {
                if let [PureExpr::Int(value)] = args.as_slice() {
                    if let Some(folded) = fold_int_truncate_const(*value, target_bits, signed) {
                        return PureExpr::Int(folded);
                    }
                }
            }
            PureExpr::LogicFnCall {
                name: name.clone(),
                args,
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(inline_local_lets(receiver)),
            method: method.clone(),
            args: args.iter().map(inline_local_lets).collect(),
        },
        PureExpr::BinOp(left, op, right) => {
            bin_expr(inline_local_lets(left), *op, inline_local_lets(right))
        }
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, Arc::new(inline_local_lets(inner))),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(inline_local_lets(cond)),
            Arc::new(inline_local_lets(then_expr)),
            Arc::new(inline_local_lets(else_expr)),
        ),
        _ => expr.clone(),
    }
}

fn inline_bitwise_value_context(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::LetAssume { body, .. } | PureExpr::LetObligation { body, .. } => {
            inline_bitwise_value_context(body)
        }
        _ => {
            let inlined = inline_local_lets(expr);
            match inlined {
                PureExpr::LetAssume { body, .. } | PureExpr::LetObligation { body, .. } => {
                    inline_bitwise_value_context(&body)
                }
                _ => inlined,
            }
        }
    }
}

fn logic_body_contains_call(expr: &PureExpr, fn_name: &str) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        if matches!(node, PureExpr::LogicFnCall { name, .. } if name == fn_name) {
            found = true;
        }
    });
    found
}

fn sort_is_mapping(sort: &Sort) -> bool {
    matches!(sort, Sort::Uninterpreted(name) if name == "Mapping")
}

fn is_single_param_closure(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Closure { params, .. } if params.len() == 1)
}

/// Detect whether an equality has a single-parameter Closure on one side and a
/// Mapping-sorted expression on the other. Used to activate `mapping_context`
/// for PredCell contract patterns like `c@ == |z: u32| z@ % 2 == 0`. (#2316)
fn is_closure_mapping_equality(
    l: &PureExpr,
    r: &PureExpr,
    left_sort: &Sort,
    right_sort: &Sort,
) -> bool {
    (sort_is_mapping(left_sort) && is_single_param_closure(r))
        || (sort_is_mapping(right_sort) && is_single_param_closure(l))
}

/// When two inferred sorts disagree, prefer the more specific one.
///
/// Sort::Int is the universal default for unresolved variables. When one
/// operand has a more specific sort (Seq/Uninterpreted/Datatype), use that
/// for the equality encoding rather than blindly using the left operand's
/// sort. This prevents sort mismatches when `eq_or_iff` calls `solver.eq()`
/// with terms whose actual ay sorts differ from the syntactic inference.
/// (#1805)
///
/// When both sides are specific but disagree (e.g., Datatype(OptionInt) vs
/// Uninterpreted("Option")), use `select_structural_sort_target` to find
/// the best sort in the same family rather than arbitrarily picking the left
/// side. This resolves cross-sort-type mismatches from match encoding
/// (which produces Datatype) vs sort inference (which produces Uninterpreted).
/// (#2699)
fn prefer_specific_sort(left: Sort, right: Sort) -> Sort {
    if left == right {
        return left;
    }
    match (&left, &right) {
        // If both are Int, Int is correct
        (Sort::Int, Sort::Int) => left,
        // If left is Int but right is more specific, prefer right
        (Sort::Int, _) => right,
        // If right is Int but left is specific, prefer left
        (_, Sort::Int) => left,
        // Both are specific but disagree: try structural sort resolution
        // to find the best sort in the same family. (#2699)
        _ => super::super::select_structural_sort_target(&left, &right).unwrap_or(left),
    }
}

/// Detect the Box-collapsed whole-reborrow pattern `Deref(Final|Deref(Var(_,
/// MutRef(scalar))))` (= `*^x` / `**x` for a `&mut Box<T>` whose `Box` layer was
/// collapsed) and return the bare `MutRef`-carrier `Var`. Returns `None` for any
/// other shape, and crucially `None` when the referent is itself a reference
/// (`&mut &mut T`), where the inner deref is a real reference peel rather than a
/// collapsed `Box` layer.
fn box_collapsed_reborrow_carrier(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::Deref(inner) = expr else {
        return None;
    };
    let carrier = match inner.as_ref() {
        PureExpr::Final(c) | PureExpr::Deref(c) => c.as_ref(),
        _ => return None,
    };
    let PureExpr::Var(_, Some(ExprSort::MutRef(referent))) = carrier else {
        return None;
    };
    if matches!(referent.as_ref(), ExprSort::MutRef(_) | ExprSort::Ref(_)) {
        return None;
    }
    Some(carrier)
}

impl AYEncoder {
    fn is_seq_index_expr(&self, expr: &PureExpr, prefix: Option<DerivedKind>) -> bool {
        let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        else {
            return false;
        };
        matches!(method.as_str(), "index" | "index_logic")
            && args.len() == 1
            && self.is_seq_receiver(receiver, prefix)
    }

    fn is_closure_seq_mapping_equality(
        &self,
        l: &PureExpr,
        r: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> bool {
        (is_single_param_closure(l) && self.is_seq_index_expr(r, prefix))
            || (is_single_param_closure(r) && self.is_seq_index_expr(l, prefix))
    }

    fn coerce_closure_mapping_peer(
        &mut self,
        expr: &PureExpr,
        term: Term,
        prefix: Option<DerivedKind>,
    ) -> Term {
        let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
        if self.solver.get_sort(term) == mapping_sort {
            return term;
        }
        if self.is_seq_index_expr(expr, prefix) && self.solver.get_sort(term) == Sort::Int {
            return self
                .try_restore_seq_element_from_int(term, &mapping_sort)
                .unwrap_or_else(|| self.coerce_to_mapping(term));
        }
        term
    }

    fn encode_closure_mapping_peer(
        &mut self,
        expr: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let saved_hint = if let PureExpr::MethodCall {
            receiver, method, ..
        } = expr
        {
            let qualified_key =
                crate::encoder::sort_context::hint_collection::receiver_qualified_method_hint_key(
                    receiver, method,
                );
            let saved = self.sort_hint_cloned(&qualified_key);
            if saved == Some(ExprSort::Bool) && self.is_seq_index_expr(expr, prefix) {
                self.remove_sort_hint(&qualified_key);
            }
            Some((qualified_key, saved))
        } else {
            None
        };

        let term = self.encode_pure_impl(expr, prefix);

        if let Some((qualified_key, Some(hint))) = saved_hint {
            self.record_sort_hint(qualified_key, hint);
        }

        term.map(|term| self.coerce_closure_mapping_peer(expr, term, prefix))
    }

    fn bitwise_alias_expr(&self, expr: &PureExpr) -> PureExpr {
        match expr {
            PureExpr::Var(name, _) => self
                .var_expr_alias(name)
                .map(inline_bitwise_value_context)
                .unwrap_or_else(|| inline_bitwise_value_context(expr)),
            _ => inline_bitwise_value_context(expr),
        }
    }

    fn bitand_or_operand_mask_with_aliases(
        &self,
        expr: &PureExpr,
    ) -> Option<(PureExpr, PureExpr, PureExpr)> {
        let expr = self.bitwise_alias_expr(expr);
        let PureExpr::BinOp(left, BinOp::BitAnd, right) = strip_low_bitop_marker(&expr) else {
            return None;
        };

        let left = self.bitwise_alias_expr(left);
        let right = self.bitwise_alias_expr(right);
        if let PureExpr::BinOp(or_left, BinOp::BitOr, or_right) = strip_low_bitop_marker(&left) {
            return Some((or_left.as_ref().clone(), or_right.as_ref().clone(), right));
        }
        if let PureExpr::BinOp(or_left, BinOp::BitOr, or_right) = strip_low_bitop_marker(&right) {
            return Some((or_left.as_ref().clone(), or_right.as_ref().clone(), left));
        }
        None
    }

    fn open_logic_body_expansion(&self, expr: &PureExpr) -> Option<PureExpr> {
        let PureExpr::LogicFnCall { name, args } = expr else {
            return None;
        };
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        let axiom = self.ground_pool.axioms().iter().find(|axiom| {
            axiom.fn_symbol == smt_name
                && axiom.kind == AxiomKind::Defining
                && axiom.requires.is_empty()
                && axiom.params.len() == args.len()
                && !logic_body_contains_call(&axiom.body, name)
        })?;

        let substitutions: HashMap<String, PureExpr> = axiom
            .params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        Some(inline_local_lets(&axiom.body.substitute(&substitutions)))
    }

    fn guarded_open_logic_call(&self, expr: &PureExpr) -> bool {
        let PureExpr::LogicFnCall { name, args } = expr else {
            return false;
        };
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        self.ground_pool.axioms().iter().any(|axiom| {
            axiom.fn_symbol == smt_name
                && axiom.kind == AxiomKind::Defining
                && !axiom.requires.is_empty()
                && axiom.params.len() == args.len()
        })
    }

    fn try_encode_open_logic_body_equality(
        &mut self,
        left: &PureExpr,
        op: BinOp,
        right: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        if !matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(None);
        }
        if self.quantifier_state.quantifier_depth() > 0 {
            return Ok(None);
        }
        if self.guarded_open_logic_call(left) || self.guarded_open_logic_call(right) {
            let equality = self.solver.fresh_var("guarded_logic_equality", Sort::Bool);
            return Ok(Some(if matches!(op, BinOp::Eq) {
                equality
            } else {
                self.solver.not(equality)
            }));
        }
        let left_expanded = self.open_logic_body_expansion(left);
        let right_expanded = self.open_logic_body_expansion(right);
        if left_expanded.is_none() && right_expanded.is_none() {
            return Ok(None);
        }

        let normalized_left = left_expanded.unwrap_or_else(|| self.bitwise_alias_expr(left));
        let normalized_right = right_expanded.unwrap_or_else(|| self.bitwise_alias_expr(right));
        if normalized_left == normalized_right
            || is_sort_agnostic_equal(&normalized_left, &normalized_right)
        {
            return Ok(Some(self.solver.bool_const(matches!(op, BinOp::Eq))));
        }

        let rewritten = bin_expr(normalized_left, op, normalized_right);
        self.encode_pure_impl(&rewritten, prefix).map(Some)
    }

    fn tuple2_local_update_output_parts<'a>(
        &self,
        expr: &'a PureExpr,
    ) -> Option<(usize, &'a PureExpr, &'a PureExpr, &'a PureExpr)> {
        let PureExpr::LogicFnCall { name, args } = expr else {
            return None;
        };
        let output_index = tuple_field_logic_fn_index(name)?;
        if output_index > 1 || args.len() != 1 {
            return None;
        }

        let PureExpr::MethodCall {
            receiver,
            method,
            args: update_args,
        } = &args[0]
        else {
            return None;
        };
        if method != "update" || update_args.len() != 2 {
            return None;
        }

        let PureExpr::LogicFnCall {
            name: receiver_name,
            args: receiver_args,
        } = receiver.as_ref()
        else {
            return None;
        };
        if tuple_logic_fn_arity(receiver_name) != Some(2) || receiver_args.len() != 2 {
            return None;
        }

        let key = &receiver_args[0];
        let value = &receiver_args[1];
        let source = update_args.get(output_index)?;
        Some((output_index, source, key, value))
    }

    fn tuple2_local_update_output_source<'a>(&self, expr: &'a PureExpr) -> Option<&'a PureExpr> {
        self.tuple2_local_update_output_parts(expr)
            .map(|(_, source, _, _)| source)
    }

    fn tuple2_local_update_value<'a>(&self, expr: &'a PureExpr) -> Option<&'a PureExpr> {
        self.tuple2_local_update_output_parts(expr)
            .map(|(_, _, _, value)| value)
    }

    fn record_fmap_view_hint(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        if let Some(name) = resolve_view_var_name(expr, prefix) {
            self.record_sort_hint(name, ExprSort::FMap);
        }
    }

    fn record_fmap_value_sort_hint(
        &mut self,
        expr: &PureExpr,
        value_sort: Sort,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        if let Some(name) = resolve_view_var_name(expr, prefix) {
            self.encoding_cache
                .insert_fmap_value_sort_name(name, value_sort.clone());
        }
        if let Some(name) = crate::encoder::sort_context::resolve_nameable_expr(expr, prefix) {
            self.encoding_cache
                .insert_fmap_value_sort_name(name, value_sort);
        }
    }

    fn infer_fmap_local_update_value_sort(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Sort {
        if let Some(annotation) = extract_inner_var_annotation(expr) {
            let annotated = self.sort_from_expr_sort(annotation.clone());
            if annotated != Sort::Int {
                return annotated;
            }
        }
        self.infer_expr_sort_with_context(expr, prefix)
    }

    fn preseed_fmap_local_update_view_equality(
        &mut self,
        output_side: &PureExpr,
        view_side: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        let Some(source_arg) = self.tuple2_local_update_output_source(output_side) else {
            return;
        };
        self.record_fmap_view_hint(source_arg, prefix);
        self.record_fmap_view_hint(view_side, prefix);
        if let Some(value_arg) = self.tuple2_local_update_value(output_side) {
            let value_sort = self.infer_fmap_local_update_value_sort(value_arg, prefix);
            self.record_fmap_value_sort_hint(source_arg, value_sort.clone(), prefix);
            self.record_fmap_value_sort_hint(view_side, value_sort, prefix);
        }
    }

    fn rewrite_fmap_local_update_output_equality(
        &mut self,
        output_side: &PureExpr,
        peer_side: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<PureExpr> {
        let (_, source, key, value) = self.tuple2_local_update_output_parts(output_side)?;
        self.record_fmap_view_hint(source, prefix);
        self.record_fmap_view_hint(peer_side, prefix);
        let value_sort = self.infer_fmap_local_update_value_sort(value, prefix);
        self.record_fmap_value_sort_hint(source, value_sort.clone(), prefix);
        self.record_fmap_value_sort_hint(peer_side, value_sort, prefix);
        let inserted = fmap_insert_expr(source, key, value);
        Some(PureExpr::BinOp(
            Arc::new(peer_side.clone()),
            BinOp::Eq,
            Arc::new(inserted),
        ))
    }

    #[allow(clippy::self_only_used_in_recursion)] // Method signature kept for consistency with other encoder helpers
    pub(in crate::encoder) fn peel_tuple_getter_call<'a>(
        &self,
        expr: &'a PureExpr,
    ) -> Option<(&'a str, &'a [PureExpr])> {
        match expr {
            PureExpr::LogicFnCall { name, args }
                if name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX) =>
            {
                Some((name.as_str(), args.as_slice()))
            }
            PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => self.peel_tuple_getter_call(inner),
            _ => None,
        }
    }

    fn preseed_tuple_getter_placeholder_from_equality_context(
        &mut self,
        tuple_side: &PureExpr,
        other_side: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        let Some((getter_name, getter_args)) = self.peel_tuple_getter_call(tuple_side) else {
            return;
        };

        let peer_sort = self.infer_expr_sort_with_context(other_side, prefix);
        if matches!(peer_sort, Sort::Int | Sort::Bool) {
            return;
        }

        let param_sorts: Vec<Sort> = getter_args
            .iter()
            .map(|arg| self.tuple_getter_preseed_arg_sort(arg, prefix))
            .collect();
        if param_sorts.first().is_none_or(|sort| *sort == Sort::Int) {
            return;
        }

        let smt_name = trust_wp_core::logic::logic_fn_smt_name(getter_name);
        let decl_key = Self::placeholder_smt_name(&smt_name, &param_sorts, &peer_sort);
        self.get_or_declare_logic_func(&decl_key, &param_sorts, peer_sort);
    }

    fn concrete_equality_peer_sort(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<Sort> {
        match expr {
            PureExpr::Bool(_) => Some(Sort::Bool),
            PureExpr::Int(_) => Some(Sort::Int),
            PureExpr::Float(bits) => Some(super::ieee::float_sort(
                bits.width()
                    .unwrap_or(trust_wp_core::formula::FloatWidth::F64),
            )),
            PureExpr::Var(_, Some(sort)) => Some(self.sort_from_expr_sort(sort.clone())),
            PureExpr::BinOp(_, op, _) => match op {
                BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or
                | BinOp::Implies => Some(Sort::Bool),
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
                | BinOp::BitOr => Some(Sort::Int),
                #[allow(unreachable_patterns)]
                _ => None,
            },
            PureExpr::UnOp(UnOp::Not, _) => Some(Sort::Bool),
            PureExpr::UnOp(UnOp::BitNot | UnOp::Neg, _) => Some(Sort::Int),
            PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => self.concrete_equality_peer_sort(inner, prefix),
            PureExpr::LogicFnCall { name, args } => {
                let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
                if let Some(func_decl) = self.logic_func_decl_cloned(&smt_name) {
                    return Some(func_decl.range().clone());
                }
                let param_sorts = args
                    .iter()
                    .map(|arg| self.infer_expr_sort_with_context(arg, prefix))
                    .collect::<Vec<_>>();
                self.existing_placeholder_return_sort(&smt_name, &param_sorts)
                    .or_else(|| {
                        self.sort_hint_cloned(&smt_name)
                            .map(|hint| self.sort_from_expr_sort(hint))
                    })
            }
            _ => None,
        }
    }

    fn preseed_logic_fn_placeholder_from_equality_context(
        &mut self,
        logic_side: &PureExpr,
        other_side: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        let PureExpr::LogicFnCall { name, args } = logic_side else {
            return;
        };
        // Seq/FMap literal builtins must NEVER be preseeded as placeholder
        // UFs: the dispatch level routes them to dedicated axiom-backed
        // encoders (`seq![v]` → seq_singleton, `seq![]`/`Seq::empty()` →
        // seq_empty, `FMap::empty()` → the fmap_empty constant). A
        // context-derived return sort here can be arbitrarily wrong: `s@ ==
        // seq!['Ã']` with `s: String` preseeds
        // `logic_seq__placeholder_i__ret_d537472696e67` (ret = the String
        // datatype), whose declaration panics in ay-dpll's core-identity gate
        // (function_declarations.rs) — the third declare-collision route
        // beyond #2706's two (cc/string `test_string_len`).
        if matches!(
            name.as_str(),
            "seq" | "seq_empty" | "Seq::empty" | "Seq::singleton" | "fmap_empty" | "FMap::empty"
        ) {
            return;
        }
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        if self.has_logic_func_decl(&smt_name) {
            return;
        }
        let Some(return_sort) = self.concrete_equality_peer_sort(other_side, prefix) else {
            return;
        };
        let param_sorts = args
            .iter()
            .map(|arg| self.infer_expr_sort_with_context(arg, prefix))
            .collect::<Vec<_>>();
        let decl_key = Self::placeholder_smt_name(&smt_name, &param_sorts, &return_sort);
        self.get_or_declare_logic_func(&decl_key, &param_sorts, return_sort);
    }

    fn tuple_getter_preseed_arg_sort(
        &mut self,
        arg: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Sort {
        if let Some(sort) = Self::local_update_result_tuple_sort(arg) {
            return sort;
        }
        if let Some(sort) = self.fmap_get_payload_sort_for_tuple_preseed(arg, prefix) {
            return sort.as_term_sort();
        }
        self.infer_expr_sort_with_context(arg, prefix)
    }

    fn local_update_result_tuple_sort(expr: &PureExpr) -> Option<Sort> {
        let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        else {
            return None;
        };
        if method != "update" || args.len() != 2 {
            return None;
        }
        let PureExpr::LogicFnCall {
            name: receiver_name,
            args: receiver_args,
        } = receiver.as_ref()
        else {
            return None;
        };
        if tuple_logic_fn_arity(receiver_name) == Some(2) && receiver_args.len() == 2 {
            Some(Sort::Uninterpreted("Tuple2".to_string()))
        } else {
            None
        }
    }

    fn fmap_get_payload_sort_for_tuple_preseed(
        &self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<Sort> {
        let value_expr = match expr {
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if matches!(method.as_str(), "unwrap" | "unwrap_logic") && args.is_empty() => {
                receiver.as_ref()
            }
            other => other,
        };
        let (receiver, _) = fmap_get_method_parts(value_expr)?;
        if !self.is_fmap_receiver(receiver, prefix) {
            return None;
        }
        if let Some(name) = resolve_view_var_name(receiver, prefix) {
            if let Some(sort) = self.encoding_cache.fmap_value_sort_name(&name) {
                return Some(sort);
            }
        }
        if let Some(name) = resolve_nameable_expr(receiver, prefix) {
            if let Some(sort) = self.encoding_cache.fmap_value_sort_name(&name) {
                return Some(sort);
            }
        }
        None
    }

    fn normalize_fmap_get_option_comparison(
        &self,
        left: &PureExpr,
        op: BinOp,
        right: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<PureExpr> {
        self.normalize_fmap_get_option_side(left, op, right, prefix)
            .or_else(|| self.normalize_fmap_get_option_side(right, op, left, prefix))
    }

    fn normalize_fmap_get_option_side(
        &self,
        get_side: &PureExpr,
        op: BinOp,
        option_side: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<PureExpr> {
        let (receiver, key) = fmap_get_method_parts(get_side)?;
        if !self.is_fmap_receiver(receiver, prefix) {
            return None;
        }

        match (op, option_constructor(option_side)?) {
            (BinOp::Eq, OptionConstructor::Some(value)) => {
                Some(fmap_get_some_formula(receiver, key, value))
            }
            (BinOp::Eq, OptionConstructor::None) => Some(PureExpr::UnOp(
                UnOp::Not,
                Arc::new(fmap_method_call(receiver, "contains", key)),
            )),
            (BinOp::Ne, OptionConstructor::Some(value)) => Some(PureExpr::UnOp(
                UnOp::Not,
                Arc::new(fmap_get_some_formula(receiver, key, value)),
            )),
            (BinOp::Ne, OptionConstructor::None) => {
                Some(fmap_method_call(receiver, "contains", key))
            }
            _ => None,
        }
    }

    fn encode_single_bit_mask_zero_comparison(
        &mut self,
        value: &PureExpr,
        mask: u64,
        op: BinOp,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        if !self.arithmetic_mode.bitwise_proof_mode() {
            return Ok(None);
        }
        if mask == 0 {
            return Ok(Some(self.solver.bool_const(matches!(op, BinOp::Eq))));
        }

        let value_term = self.encode_pure_impl(value, prefix)?;
        let zero = self.solver.int_const(0);
        let (value_term, _) = coerce_to_numeric(
            &mut self.solver,
            value_term,
            zero,
            NumericOperandMode::IntOnly,
        );

        let bit = mask.trailing_zeros();
        if bit < 62 {
            let mask_int = self.solver.int_const(mask as i64);
            let period = self.solver.int_const((mask << 1) as i64);
            let low_bits = self.solver.modulo(value_term, period);
            return Ok(Some(if matches!(op, BinOp::Eq) {
                self.solver.lt(low_bits, mask_int)
            } else {
                self.solver.ge(low_bits, mask_int)
            }));
        }

        let Ok(value_bv) = self.solver.try_int2bv(value_term, BITWISE_PROOF_BV_WIDTH) else {
            return Ok(None);
        };

        let extracted = self.solver.bvextract(value_bv, bit, bit);
        let zero_bit = self.solver.bv_const(0, 1);
        let bit_is_clear = self.eq_term(extracted, zero_bit);

        Ok(Some(if matches!(op, BinOp::Eq) {
            bit_is_clear
        } else {
            self.solver.not(bit_is_clear)
        }))
    }

    fn try_encode_bitand_zero_comparison(
        &mut self,
        left: &PureExpr,
        op: BinOp,
        right: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        if !matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(None);
        }

        let comparison = if int_literal(right) == Some(0) {
            bitand_single_bit_mask(left)
        } else if int_literal(left) == Some(0) {
            bitand_single_bit_mask(right)
        } else {
            None
        };

        if let Some((left_value, right_value, mask)) = if int_literal(right) == Some(0) {
            self.bitand_or_operand_mask_with_aliases(left)
        } else if int_literal(left) == Some(0) {
            self.bitand_or_operand_mask_with_aliases(right)
        } else {
            None
        } {
            // Absorption shortcut for set-bit-style obligations (#5):
            // when one OR-operand is sort-equivalent to the mask, the BV
            // identity `(A | M) & M = M` collapses the conjunction
            // `(A & M) ∧ (M & M)` to the trivial half. Emit `(M & M) op 0`
            // so `try_encode_symbolic_single_bit_mask_zero_comparison` can
            // discharge it via its `is_same_shl_one_mask` range-guard
            // shortcut (`shift < 0 ∨ shift >= width`). Without this, the
            // `(A & M)` conjunct leaves a `bvand(int2bv(A), mask)` literal
            // that is opaque to LRA, blocking cross-theory propagation and
            // producing `quantifier-unhandled`.
            if is_sort_agnostic_equal(&left_value, &mask)
                || is_sort_agnostic_equal(&right_value, &mask)
            {
                let rewritten = bin_expr(
                    bin_expr(mask.clone(), BinOp::BitAnd, mask),
                    op,
                    PureExpr::Int(0),
                );
                return self.encode_pure_impl(&rewritten, prefix).map(Some);
            }
            let left_test = bin_expr(
                bin_expr(left_value, BinOp::BitAnd, mask.clone()),
                op,
                PureExpr::Int(0),
            );
            let right_test = bin_expr(
                bin_expr(right_value, BinOp::BitAnd, mask),
                op,
                PureExpr::Int(0),
            );
            let connective = if matches!(op, BinOp::Eq) {
                BinOp::And
            } else {
                BinOp::Or
            };
            let rewritten = bin_expr(left_test, connective, right_test);
            return self.encode_pure_impl(&rewritten, prefix).map(Some);
        }

        let Some((value, mask)) = comparison else {
            return self
                .try_encode_symbolic_single_bit_mask_zero_comparison(left, op, right, prefix);
        };
        self.encode_single_bit_mask_zero_comparison(value, mask, op, prefix)
    }

    fn try_encode_symbolic_single_bit_mask_zero_comparison(
        &mut self,
        left: &PureExpr,
        op: BinOp,
        right: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        if !self.arithmetic_mode.bitwise_proof_mode() || !matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(None);
        }

        let comparison = if int_literal(right) == Some(0) {
            bitand_shl_one_mask(left)
        } else if int_literal(left) == Some(0) {
            bitand_shl_one_mask(right)
        } else {
            None
        };
        let Some((value, shift)) = comparison else {
            return Ok(None);
        };

        if is_same_shl_one_mask(value, shift) {
            let shift_term = self.encode_pure_impl(shift, prefix)?;
            let zero = self.solver.int_const(0);
            let width = self.solver.int_const(i64::from(BITWISE_PROOF_BV_WIDTH));
            let ge_zero = self.solver.ge(shift_term, zero);
            let lt_width = self.solver.lt(shift_term, width);
            let in_range = self.solver.and(ge_zero, lt_width);
            return Ok(Some(if matches!(op, BinOp::Eq) {
                self.solver.not(in_range)
            } else {
                in_range
            }));
        }

        let value_term = self.encode_pure_impl(value, prefix)?;
        let shift_term = self.encode_pure_impl(shift, prefix)?;
        let zero = self.solver.int_const(0);
        let (value_term, _) = coerce_to_numeric(
            &mut self.solver,
            value_term,
            zero,
            NumericOperandMode::IntOnly,
        );
        let (shift_term, _) = coerce_to_numeric(
            &mut self.solver,
            shift_term,
            zero,
            NumericOperandMode::IntOnly,
        );

        let Ok(value_bv) = self.solver.try_int2bv(value_term, BITWISE_PROOF_BV_WIDTH) else {
            return Ok(None);
        };
        let Ok(shift_bv) = self.solver.try_int2bv(shift_term, BITWISE_PROOF_BV_WIDTH) else {
            return Ok(None);
        };
        let one_bv = self.solver.bv_const(1, BITWISE_PROOF_BV_WIDTH);
        let mask_bv = self.solver.bvshl(one_bv, shift_bv);
        let masked = self.solver.bvand(value_bv, mask_bv);
        let zero_bv = self.solver.bv_const(0, BITWISE_PROOF_BV_WIDTH);
        let is_zero = self.solver.eq(masked, zero_bv);

        Ok(Some(if matches!(op, BinOp::Eq) {
            is_zero
        } else {
            self.solver.not(is_zero)
        }))
    }

    fn try_encode_positive_const_div_comparison(
        &mut self,
        left: &PureExpr,
        op: BinOp,
        right: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        if !matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(None);
        }

        if let Some((dividend, divisor)) = div_by_positive_int_literal(right) {
            return self.encode_positive_const_div_comparison(left, dividend, divisor, op, prefix);
        }
        if let Some((dividend, divisor)) = div_by_positive_int_literal(left) {
            return self.encode_positive_const_div_comparison(right, dividend, divisor, op, prefix);
        }
        Ok(None)
    }

    fn encode_positive_const_div_comparison(
        &mut self,
        quotient: &PureExpr,
        dividend: &PureExpr,
        divisor: i64,
        op: BinOp,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        let quotient_sort = self.infer_expr_sort_with_context(quotient, prefix);
        let dividend_sort = self.infer_expr_sort_with_context(dividend, prefix);
        if !matches!(quotient_sort, Sort::Int) || !matches!(dividend_sort, Sort::Int) {
            return Ok(None);
        }

        let Some(normalized) = positive_const_div_comparison_expr(quotient, dividend, divisor, op)
        else {
            return Ok(None);
        };
        self.encode_pure_impl(&normalized, prefix).map(Some)
    }

    /// Encodes a binary operation expression (`BinOp`).
    ///
    /// Handles Bool-context operands, Eq/Ne sort reconciliation, constructor
    /// preseeding, Bool iff encoding, Seq equality decomposition, SeqValue
    /// propagation, and sort preference for `eq_or_iff`.
    #[allow(clippy::too_many_lines)]
    pub(super) fn encode_binop_expr(
        &mut self,
        l: &PureExpr,
        op: BinOp,
        r: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if !matches!(op, BinOp::Eq) {
            return self.encode_binop_expr_inner(l, op, r, prefix);
        }
        // Constructor-equality consequences discovered while encoding this
        // equality are collected, not asserted: they hold only when the
        // equality itself holds, and this equality may be a (negated) goal.
        // Asserting them bare made `Err(3) == Err(0)` assert both
        // `get0(Err 0) = 3` and `get0(Err 3) = 0` — a contradictory base that
        // "proved" any goal (s25_ctor_eq_goal_payload_facts.rs).
        let saved = self.constructor_alias_fact_buffer.replace(Vec::new());
        let result = self.encode_binop_expr_inner(l, op, r, prefix);
        let facts =
            std::mem::replace(&mut self.constructor_alias_fact_buffer, saved).unwrap_or_default();
        let equality = result?;
        if !facts.is_empty() {
            self.flush_guarded_constructor_alias_facts(equality, facts);
        }
        Ok(equality)
    }

    /// Assert each deferred constructor-equality consequence as
    /// `equality => fact`. SOUND: every fact is a consequence of the equality
    /// (`alias == Ctor(args)` entails `field_i(alias) == args[i]`), so the
    /// implication is valid in every model; when the equality is a premise the
    /// fact follows by modus ponens, and when it is a negated goal nothing is
    /// assumed. Dropped (completeness only) inside quantifier bodies, where the
    /// terms mention bound variables, and when the equality is not Bool-sorted.
    fn flush_guarded_constructor_alias_facts(
        &mut self,
        equality: Term,
        facts: Vec<super::super::ConstructorAliasFact>,
    ) {
        if self.quantifier_state.quantifier_depth() != 0
            || self.solver.get_sort(equality) != Sort::Bool
        {
            return;
        }
        for fact in facts {
            match fact {
                super::super::ConstructorAliasFact::Equality { label, lhs, rhs } => {
                    let fact_term = self.seq_aware_equality_term(lhs, rhs);
                    let guarded = self.solver.implies(equality, fact_term);
                    self.assert_solver_term(label, guarded);
                }
                super::super::ConstructorAliasFact::Registration {
                    datatype,
                    constructor_name,
                    alias,
                    args,
                } => {
                    let symbol =
                        Self::native_constructor_ground_symbol(&datatype.name, &constructor_name);
                    let mut path_conditions = self.active_path_conditions_cloned();
                    path_conditions.push(equality);
                    self.ground_pool
                        .register_term_application_with_path_conditions(
                            &symbol,
                            alias,
                            args,
                            path_conditions,
                        );
                }
            }
        }
    }

    fn defer_constructor_alias_equality(&mut self, label: &'static str, lhs: Term, rhs: Term) {
        if let Some(buffer) = self.constructor_alias_fact_buffer.as_mut() {
            buffer.push(super::super::ConstructorAliasFact::Equality { label, lhs, rhs });
        }
    }

    fn defer_constructor_alias_registration(
        &mut self,
        datatype: &DatatypeSort,
        constructor_name: &str,
        alias: Term,
        args: &[Term],
    ) {
        if let Some(buffer) = self.constructor_alias_fact_buffer.as_mut() {
            buffer.push(super::super::ConstructorAliasFact::Registration {
                datatype: datatype.clone(),
                constructor_name: constructor_name.to_string(),
                alias,
                args: args.to_vec(),
            });
        }
    }

    fn encode_binop_expr_inner(
        &mut self,
        l: &PureExpr,
        op: BinOp,
        r: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if matches!(op, BinOp::And | BinOp::Or | BinOp::Implies) {
            let lt = self.encode_bool_context_operand(l, prefix)?;
            let rt = self.encode_bool_context_operand(r, prefix)?;
            return self.encode_binop(lt, op, rt, None);
        }
        // For arithmetic operators (add/sub/mul/div/mod/lt/le/gt/ge),
        // pre-declare operand variables with Int sort when they have
        // Datatype annotations that model as integers (Duration, Instant,
        // Ghost, NonZero*, etc.). Without this, the variable may be
        // declared with Sort::Uninterpreted("std::time::Duration") by
        // a different code path before encode_var runs, causing ay sort
        // mismatches in arithmetic operations. (#1965)
        if matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::DivTrunc
                | BinOp::RemTrunc
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
        ) {
            self.preseed_int_model_type_sort(l, prefix);
            self.preseed_int_model_type_sort(r, prefix);
        }
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            // Reflexive equality short-circuit (#2673): when both sides of
            // Eq/Ne are structurally identical PureExpr trees, return true/false
            // immediately without encoding either side. This prevents sort
            // coercion in logic function calls from creating fresh unconstrained
            // constants that break term identity (e.g., `u(*a) == u(*a)` in
            // bug/206 where sort mismatch on the logic function argument causes
            // each call to produce a different ay term via apply_coerce).
            //
            // Sound because `x == x` is always true and `x != x` is always false
            // in SMT for any well-sorted `x`.
            if l == r {
                return Ok(self.solver.bool_const(matches!(op, BinOp::Eq)));
            }
            // Sort-agnostic reflexive equality short-circuit (#2673): when both
            // sides are structurally identical except for ExprSort annotations on
            // Var nodes, return true/false. The driver may attach different sort
            // annotations to syntactically identical expressions (e.g., Var("a",
            // Some(Datatype("A"))) vs Var("a", None)). Since sorts are a hint and
            // the underlying expression is the same, this is sound.
            if is_sort_agnostic_equal(l, r) {
                return Ok(self.solver.bool_const(matches!(op, BinOp::Eq)));
            }
            if let Some(encoded) = self.try_encode_open_logic_body_equality(l, op, r, prefix)? {
                return Ok(encoded);
            }
            if matches!(op, BinOp::Eq) {
                if let Some(rewritten) =
                    self.rewrite_fmap_local_update_output_equality(l, r, prefix)
                {
                    return self.encode_pure_impl(&rewritten, prefix);
                }
                if let Some(rewritten) =
                    self.rewrite_fmap_local_update_output_equality(r, l, prefix)
                {
                    return self.encode_pure_impl(&rewritten, prefix);
                }
            }
            if let Some(normalized) = self.normalize_fmap_get_option_comparison(l, op, r, prefix) {
                return self.encode_pure_impl(&normalized, prefix);
            }
            if let Some(encoded) =
                self.try_encode_positive_const_div_comparison(l, op, r, prefix)?
            {
                return Ok(encoded);
            }
            if let Some(encoded) = self.try_encode_bitand_zero_comparison(l, op, r, prefix)? {
                return Ok(encoded);
            }
            if let Some(encoded) = self.try_encode_option_none_equality(l, op, r, prefix)? {
                return Ok(encoded);
            }
        }
        // Nested constructor equality decomposition (#1296):
        // When one side of an equality is a constructor call whose args have a
        // sort mismatch with the native datatype fields (e.g., `OwnResult::Ok(None)`
        // where Ok expects Int but None is OptionInt-sorted), the standard encoding
        // produces a UF placeholder term disconnected from the body's match-based
        // encoding. Decompose into tester/selector checks instead:
        //   `X == OwnResult::Ok(None)` → `is-Ok(X) && !is_some(ownresult_ok_ok(X))`
        // This uses the same Int-model UF accessors (is_some, spec_unwrap) that the
        // match encoding uses, maintaining semantic connection.
        if matches!(op, BinOp::Eq) {
            if let Some(decomposed) = self.try_decompose_nested_ctor_equality(l, r, prefix)? {
                return Ok(decomposed);
            }
        }
        // For Eq/Ne: reconcile sort hints before encoding to prevent
        // sort mismatches when a LogicFnCall has a stale Bool hint but
        // the other operand is Int. (#585)
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            self.reconcile_eq_sort_hints(l, r);
            // Pre-seed variable sorts when one side is a known datatype
            // constructor (Some/None/Ok/Err). Without this, variables
            // default to Int sort and mk_eq panics when the constructor
            // side produces a datatype-sorted term. (#1572)
            self.preseed_constructor_var_sort(l, r);
            // Tuple-lowered FMap local updates return `(auth, frag)`.
            // When Authority::update equates a final view with one of those
            // tuple fields, seed the final view as FMap before tuple-getter
            // placeholder sort selection runs.
            self.preseed_fmap_local_update_view_equality(l, r, prefix);
            self.preseed_fmap_local_update_view_equality(r, l, prefix);
            // Tuple getters over tuple-typed temporaries do not carry field-sort
            // information in their receiver annotation alone. Seed the placeholder
            // with the equality peer's non-Int sort so the first declaration for
            // `tuple_get_i(tupleN_value)` does not freeze at Int. (#permcell)
            self.preseed_tuple_getter_placeholder_from_equality_context(l, r, prefix);
            self.preseed_tuple_getter_placeholder_from_equality_context(r, l, prefix);
            // Generic undeclared logic functions can also be forced by equality
            // context: `f(x) == 0` gives `f` an exact Int return sort before
            // generic sort inference would otherwise take the demoting Int
            // fallback. The placeholder remains signature-keyed, so mixed-sort
            // uses do not collide. (#1581)
            self.preseed_logic_fn_placeholder_from_equality_context(l, r, prefix);
            self.preseed_logic_fn_placeholder_from_equality_context(r, l, prefix);
        }
        let left_sort = self.infer_expr_sort_with_context(l, prefix);
        let right_sort = self.infer_expr_sort_with_context(r, prefix);

        // Closure-Mapping equality: `view@ == |z| body` in PredCell contracts (#2316)
        //
        // When one side of an equality is a single-parameter Closure (inferred Bool
        // from its body, e.g., `|z: u32| z@ % 2 == 0`) and the other side infers
        // as Mapping, the closure represents a predicate function, not a Boolean.
        // Without this, the closure falls through to `__closure_logic_N: Bool` in
        // `encode_closure_in_logic` and the equality becomes `Mapping == Bool`,
        // which is unsatisfiable. Enable `mapping_context` so the closure encodes
        // as a proper Mapping constant with a defining axiom.
        let closure_mapping_override = matches!(op, BinOp::Eq | BinOp::Ne)
            && (is_closure_mapping_equality(l, r, &left_sort, &right_sort)
                || self.is_closure_seq_mapping_equality(l, r, prefix));

        let equality_target_sort = if matches!(op, BinOp::Eq | BinOp::Ne) {
            if closure_mapping_override {
                // Both sides should be Mapping, not Bool.
                Some(Sort::Uninterpreted("Mapping".to_string()))
            } else if matches!(left_sort, Sort::Bool) || matches!(right_sort, Sort::Bool) {
                Some(Sort::Bool)
            } else {
                Some(prefer_specific_sort(left_sort.clone(), right_sort.clone()))
            }
        } else {
            None
        };

        let (mut lt, mut rt) = if closure_mapping_override {
            // Encode the non-closure side normally. For the closure side,
            // activate mapping_context so encode_closure_in_logic produces a
            // Mapping constant with a defining axiom instead of a Bool fallback.
            let (non_closure, closure_expr, left_is_closure) =
                if matches!(l, PureExpr::Closure { .. }) {
                    (r, l, true)
                } else {
                    (l, r, false)
                };
            let non_closure_term = self.encode_closure_mapping_peer(non_closure, prefix)?;
            let old_mapping = self.closure_state.set_mapping_context(true);
            let closure_term = self.encode_pure_impl(closure_expr, prefix)?;
            self.closure_state.set_mapping_context(old_mapping);
            if left_is_closure {
                (closure_term, non_closure_term)
            } else {
                (non_closure_term, closure_term)
            }
        } else if matches!(op, BinOp::Eq | BinOp::Ne) {
            if matches!(left_sort, Sort::Bool) && !matches!(right_sort, Sort::Bool) {
                (
                    self.encode_pure_impl(l, prefix)?,
                    self.encode_bool_context_operand(r, prefix)?,
                )
            } else if matches!(right_sort, Sort::Bool) && !matches!(left_sort, Sort::Bool) {
                (
                    self.encode_bool_context_operand(l, prefix)?,
                    self.encode_pure_impl(r, prefix)?,
                )
            } else {
                (
                    self.encode_pure_impl(l, prefix)?,
                    self.encode_pure_impl(r, prefix)?,
                )
            }
        } else {
            (
                self.encode_pure_impl(l, prefix)?,
                self.encode_pure_impl(r, prefix)?,
            )
        };
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            lt = self.fit_unsuffixed_float_literal(l, lt, rt)?;
            rt = self.fit_unsuffixed_float_literal(r, rt, lt)?;
        }
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            // `seq.index_logic(i)` still encodes through the Int carrier.
            // When equality gives us a richer peer sort (for example Mapping
            // in `result[i]@ == pred[i]`), restore the seq element first so
            // `eq_or_iff` does not replace it with a fresh placeholder.
            if self.solver.get_sort(lt) == Sort::Int {
                let target_sort = self.solver.get_sort(rt);
                if !matches!(target_sort, Sort::Int | Sort::Bool) {
                    if let Some(restored) = self.try_restore_seq_element_from_int(lt, &target_sort)
                    {
                        lt = restored;
                    }
                }
            }
            if self.solver.get_sort(rt) == Sort::Int {
                let target_sort = self.solver.get_sort(lt);
                if !matches!(target_sort, Sort::Int | Sort::Bool) {
                    if let Some(restored) = self.try_restore_seq_element_from_int(rt, &target_sort)
                    {
                        rt = restored;
                    }
                }
            }
            if self.solver.get_sort(lt) == Sort::Int && self.solver.get_sort(rt) == Sort::Int {
                if let Some(target_sort) = equality_target_sort.as_ref() {
                    if !matches!(target_sort, Sort::Int | Sort::Bool) {
                        if let Some(restored) =
                            self.try_restore_seq_element_from_int(lt, target_sort)
                        {
                            lt = restored;
                        }
                        if let Some(restored) =
                            self.try_restore_seq_element_from_int(rt, target_sort)
                        {
                            rt = restored;
                        }
                    }
                }
            }
        }
        // Box-collapsed whole-reborrow equality (`bug/final_borrows::
        // reborrow_in_box`). For `x: &mut Box<T>` returning `&mut T`, the
        // postcondition `result == &mut **x` lowers to
        // `result == Deref(Final(x))` (= `*^x`) with `result` and `x` both the
        // collapsed `MutRef(T)` carrier. Because the `Box` indirection is
        // collapsed, `&mut **x` IS the reborrow `x` itself, so the equality is a
        // whole-mut-ref equality `result == x`. But the extra `Deref` over the
        // `MutRef`-carrier `Final(x)` encodes (under scalar collapse)
        // to a non-`MutRef` leaf, so `result(MutRef) == leaf` sort-coerces into a
        // fresh unconstrained const and the goal becomes trivially SAT.
        //
        // When one operand is a `MutRef`-sorted carrier and the other operand is
        // the Box-collapse pattern `Deref(Final|Deref(Var(_, MutRef(scalar))))`
        // whose encoded term is NOT `MutRef`-sorted, re-encode that operand as the
        // bare carrier `Var`, recovering a `MutRef`-vs-`MutRef` equality that
        // decomposes component-wise below. SOUND: dereferencing the collapsed
        // `Box` layer of a single-layer mut-ref is the identity, so `*^x` over the
        // collapsed carrier IS `^x`'s carrier `x` — an exact rewrite, never an
        // added assumption. Guarded on a *scalar* (non-reference) referent so a
        // genuine nested `&mut &mut T` (where the inner deref is a real reference
        // peel) is left to the general path.
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            if self.is_mut_ref_sorted(rt) && !self.is_mut_ref_sorted(lt) {
                if let Some(carrier) = box_collapsed_reborrow_carrier(l) {
                    let carrier_term = self.encode_pure_impl(carrier, prefix)?;
                    if self.is_mut_ref_sorted(carrier_term) {
                        lt = carrier_term;
                    }
                }
            } else if self.is_mut_ref_sorted(lt) && !self.is_mut_ref_sorted(rt) {
                if let Some(carrier) = box_collapsed_reborrow_carrier(r) {
                    let carrier_term = self.encode_pure_impl(carrier, prefix)?;
                    if self.is_mut_ref_sorted(carrier_term) {
                        rt = carrier_term;
                    }
                }
            }
        }
        if matches!(op, BinOp::Eq) {
            self.assert_native_constructor_equality_payload_alias(l, r, rt, prefix)?;
            self.assert_native_constructor_equality_payload_alias(r, l, lt, prefix)?;
            self.assertion_pipeline.push_pending_pure_equality((lt, rt));
        }
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            if let Some(decomposed) = self.try_decompose_mut_ref_equality(lt, rt)? {
                return if matches!(op, BinOp::Ne) {
                    Ok(self.solver.not(decomposed))
                } else {
                    Ok(decomposed)
                };
            }
        }
        // Seq equality decomposition (#1317): ay-dpll's `eq` on
        // uninterpreted Seq sort cannot leverage Array theory.
        // Decompose `s1 == s2` into component-wise equality
        // `arr(s1)==arr(s2) && len(s1)==len(s2) && off(s1)==off(s2)`
        // when at least one operand has a SeqValue, making the
        // equality decidable via ay's native Array axioms.
        //
        // IMPORTANT: This must run BEFORE `propagate_seq_value` because
        // propagation asserts component equalities as side-effects. If
        // propagation runs first, both terms share the same SeqValue and
        // the decomposed equality becomes trivially true — which breaks
        // negated postconditions (the solver cannot falsify a tautology).
        // When decomposition fires, it returns the equality as a normal
        // Bool term without side-effect assertions, allowing the caller
        // to negate it for postcondition checking.
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            if let Some(decomposed) = self.try_decompose_seq_equality(lt, rt)? {
                // Do not propagate SeqValue metadata while merely building an
                // equality proposition. The caller may negate this term. A
                // propagation refinement would then assert the equality as a
                // side effect and make that negation vacuously UNSAT. Stable
                // target projector identities were already allocated by the
                // decomposition above; authenticated assertion paths propagate
                // only after they assert the returned equality.
                return if matches!(op, BinOp::Ne) {
                    Ok(self.solver.not(decomposed))
                } else {
                    Ok(decomposed)
                };
            }
        }
        // Pass operand sort for Eq/Ne so encode_binop can preserve
        // equality-sort bookkeeping even though the native equality
        // helper has no Bool-specific branch.
        // When inferred sorts disagree, prefer the more specific sort:
        // Bool > Seq/Uninterpreted/Datatype > Int (the default). (#1805)
        let eq_sort = equality_target_sort;
        // Signed narrow-width hint for bitwise ops: when both operand
        // expressions are premise-pinned into the same signed W-window, the
        // BV bridge encodes at width W with a SIGNED wrap-back instead of
        // the unsigned width-64 default (#route-100 rightmostbit latent
        // false-reject; see `encode_int_binop_bv_hinted`).
        let signed_narrow = if matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor) {
            self.signed_narrow_bitwise_hint(l, r)
        } else {
            None
        };
        self.encode_binop_with_bv_hint(lt, op, rt, eq_sort.as_ref(), signed_narrow)
    }

    fn try_encode_option_none_equality(
        &mut self,
        left: &PureExpr,
        op: BinOp,
        right: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        let peer = if is_stdlib_none_expr(left) {
            right
        } else if is_stdlib_none_expr(right) {
            left
        } else {
            return Ok(None);
        };

        let peer_sort = self.infer_expr_sort_with_context(peer, prefix);
        let Some(datatype) = option_datatype_from_sort(&peer_sort) else {
            return Ok(None);
        };

        self.ensure_datatype_declared(&datatype);
        let peer_term = self.encode_pure_impl(peer, prefix)?;
        let none_term =
            self.safe_datatype_constructor("option_none_equality", &datatype, "None", &[])?;
        self.materialize_ground_native_constructor(&datatype, "None", none_term, &[]);
        if matches!(op, BinOp::Eq) {
            self.assertion_pipeline
                .push_pending_pure_equality((peer_term, none_term));
        }

        self.encode_binop(
            peer_term,
            op,
            none_term,
            Some(&Sort::Datatype(datatype.clone())),
        )
        .map(Some)
    }

    fn assert_native_constructor_equality_payload_alias(
        &mut self,
        constructor_side: &PureExpr,
        alias_side: &PureExpr,
        alias_term: ay_dpll::api::Term,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        let PureExpr::LogicFnCall { name, args } = constructor_side else {
            return Ok(());
        };
        let Some((datatype, constructor_name, _)) = self
            .native_constructor_call(name, args, prefix)
            .or_else(|| self.declared_constructor_call_metadata(name, args))
        else {
            return Ok(());
        };
        let datatype_sort = Sort::Datatype(datatype.clone());
        let alias_sort = self.solver.get_sort(alias_term);

        let arg_terms = args
            .iter()
            .map(|arg| self.encode_pure_impl(arg, prefix))
            .collect::<Result<Vec<_>, _>>()?;
        let Some(constructor) = datatype
            .constructors
            .iter()
            .find(|constructor| constructor.name == constructor_name)
        else {
            return Ok(());
        };
        if let (Some(field), Some(arg_term)) = (constructor.fields.first(), arg_terms.first()) {
            if constructor.fields.len() == 1 {
                let mut alias_candidates = vec![alias_term];
                if let Some(alias_name) = resolve_nameable_expr(alias_side, prefix) {
                    if let Some(original_alias_term) = self.var_term(&alias_name) {
                        if original_alias_term != alias_term {
                            alias_candidates.push(original_alias_term);
                        }
                    }
                }
                let mut asserted_payload_alias = false;
                for candidate in alias_candidates {
                    let candidate_sort = self.solver.get_sort(candidate);
                    let field_sort = field.sort.as_term_sort();
                    if candidate_sort == field_sort
                        || (is_seq_family_sort(&candidate_sort) && is_seq_family_sort(&field_sort))
                    {
                        self.defer_constructor_alias_equality(
                            "datatype_constructor/ground_erased_alias_payload",
                            candidate,
                            *arg_term,
                        );
                        asserted_payload_alias = true;
                    }
                }
                if asserted_payload_alias {
                    return Ok(());
                }

                if alias_sort == datatype_sort || alias_sort == datatype_sort.as_term_sort() {
                    let tuple_get_name =
                        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(
                            0,
                        );
                    let smt_name = trust_wp_core::logic::logic_fn_smt_name(&tuple_get_name);
                    let arg_sort = self.solver.get_sort(*arg_term);
                    let decl_key = Self::placeholder_smt_name(
                        &smt_name,
                        std::slice::from_ref(&alias_sort),
                        &arg_sort,
                    );
                    let projection_decl = self.get_or_declare_logic_func(
                        &decl_key,
                        std::slice::from_ref(&alias_sort),
                        arg_sort,
                    );
                    let projection = self.safe_apply(
                        "datatype_constructor/ground_alias_tuple_get",
                        &projection_decl,
                        &[alias_term],
                    )?;
                    self.defer_constructor_alias_equality(
                        "datatype_constructor/ground_alias_tuple_get",
                        projection,
                        *arg_term,
                    );
                    return Ok(());
                }
            }
        }

        if alias_sort != datatype_sort && alias_sort != datatype_sort.as_term_sort() {
            return Ok(());
        }

        self.defer_constructor_alias_registration(
            &datatype,
            &constructor_name,
            alias_term,
            &arg_terms,
        );
        for (index, field) in constructor.fields.iter().enumerate() {
            let Some(arg_term) = arg_terms.get(index).copied() else {
                continue;
            };
            if alias_sort == datatype_sort {
                let Ok(selector_term) =
                    self.solver
                        .try_datatype_selector(&field.name, alias_term, field.sort.clone())
                else {
                    continue;
                };
                self.defer_constructor_alias_equality(
                    "datatype_constructor/ground_alias_selector",
                    selector_term,
                    arg_term,
                );
            }
        }

        Ok(())
    }

    fn declared_constructor_call_metadata(
        &self,
        name: &str,
        args: &[PureExpr],
    ) -> Option<(ay_dpll::api::DatatypeSort, String, Vec<Sort>)> {
        let datatype = self
            .datatypes_for_constructor(name)
            .find(|datatype| {
                datatype.constructors.iter().any(|constructor| {
                    datatype_constructor_matches(datatype, &constructor.name, name)
                        && constructor.fields.len() == args.len()
                })
            })?
            .clone();
        let constructor_name = datatype_constructor_name(&datatype, name);
        let field_sorts = datatype
            .constructors
            .iter()
            .find(|constructor| datatype_constructor_matches(&datatype, &constructor.name, name))?
            .fields
            .iter()
            .map(|field| field.sort.clone())
            .collect();
        Some((datatype, constructor_name, field_sorts))
    }

    /// Decompose `X == Outer(Inner(...))` into tester/selector checks when
    /// the outer constructor's args have a sort mismatch with the native
    /// datatype fields.
    ///
    /// For example, `self == OwnResult::Ok(None)` becomes:
    ///   `is-Ok(self) && !is_some(ownresult_ok_ok(self))`
    ///
    /// This avoids constructing a UF placeholder term for `OwnResult::Ok(None)`
    /// which would be disconnected from the match body's encoding that uses
    /// native testers/selectors with Int-model UF accessors.
    ///
    /// Returns `None` when the equality doesn't need decomposition (no sort
    /// mismatch, or not a constructor call).
    fn try_decompose_nested_ctor_equality(
        &mut self,
        left: &PureExpr,
        right: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        // Try both orientations: X == Ctor(args) and Ctor(args) == X
        if let Some(term) = self.try_decompose_ctor_eq_side(right, left, prefix)? {
            return Ok(Some(term));
        }
        self.try_decompose_ctor_eq_side(left, right, prefix)
    }

    /// Check one side of an equality for constructor decomposition.
    /// `ctor_side` is the potential constructor expression, `other_side` is the scrutinee.
    fn try_decompose_ctor_eq_side(
        &mut self,
        ctor_side: &PureExpr,
        other_side: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        let PureExpr::LogicFnCall {
            name: outer_name,
            args: outer_args,
        } = ctor_side
        else {
            return Ok(None);
        };
        // Only fire for constructor calls that have a registered datatype
        let Some(outer_dt) = self.constructor_datatype(outer_name) else {
            return Ok(None);
        };
        let outer_short = short_constructor_name(outer_name);
        // Only fire when the native constructor path would fail (sort mismatch)
        if self
            .native_constructor_call(outer_name, outer_args, prefix)
            .is_some()
        {
            return Ok(None);
        }
        // Only handle single-arg constructors with nested constructor/nullary args
        if outer_args.len() != 1 {
            return Ok(None);
        }
        let inner_arg = &outer_args[0];
        // Only decompose when the inner arg is a NULLARY constructor (e.g., None).
        // Non-nullary inner constructors (e.g., Some(t)) are handled by the
        // quantifier-level nested constructor equality elimination which has
        // full control over variable binding. Decomposing non-nullary inner
        // constructors at the BinOp level would interfere with the consequent
        // encoding in quantified postconditions. (#1296)
        let inner_name = match inner_arg {
            PureExpr::Var(name, _) if self.nullary_constructor_datatype(name).is_some() => {
                name.as_str()
            }
            PureExpr::LogicFnCall { name, args } if args.is_empty() => {
                if self.nullary_constructor_datatype(name).is_none() {
                    return Ok(None);
                }
                name.as_str()
            }
            _ => return Ok(None),
        };
        // Inner must have a registered datatype
        if self.constructor_datatype(inner_name).is_none() {
            return Ok(None);
        }
        let inner_short = short_constructor_name(inner_name);

        debug!("[trust-wp-ay] decomposing non-quantified {outer_short}({inner_short}) equality");

        // Pre-seed the scrutinee's sort to the outer datatype
        if let Some(var_name) =
            crate::encoder::quantifier_ctor_elim::extract_scrutinee_var_name(other_side)
        {
            let dt_sort = Sort::Datatype(outer_dt.clone());
            if !self.has_var_sort(var_name) || matches!(self.var_sort(var_name), Some(Sort::Int)) {
                self.insert_var_sort(var_name.to_string(), dt_sort);
            }
        }

        let scrutinee = self.encode_pure_impl(other_side, prefix)?;

        // Step 1: Outer tester — is-Ctor(scrutinee)
        let outer_actual = datatype_constructor_name(&outer_dt, outer_short);
        let outer_tester = self
            .solver
            .try_datatype_tester(&outer_actual, scrutinee)
            .map_err(|e| {
                EncodingError::solver_error(format!(
                    "nested ctor eq decomp: outer tester {outer_short}: {e}"
                ))
            })?;

        // Step 2: Extract outer payload via native selector
        let outer_ctor = outer_dt
            .constructors
            .iter()
            .find(|c| datatype_constructor_matches(&outer_dt, &c.name, outer_short));
        let Some(outer_ctor_decl) = outer_ctor else {
            return Ok(None);
        };
        let Some(outer_field) = outer_ctor_decl.fields.first() else {
            return Ok(None);
        };
        let payload = self
            .solver
            .try_datatype_selector(&outer_field.name, scrutinee, outer_field.sort.clone())
            .map_err(|e| {
                EncodingError::solver_error(format!(
                    "nested ctor eq decomp: outer selector {}: {e}",
                    outer_field.name,
                ))
            })?;

        // Step 3: Inner tester on payload
        let inner_tester = self.encode_constructor_test(
            inner_name,
            payload,
            self.constructor_datatype(inner_name).as_ref(),
        )?;

        // Step 4: Combine outer tester + inner tester.
        // Since we only handle nullary inner constructors, no selector
        // equalities are needed — the tester fully determines the value.
        let guard = self.solver.and(outer_tester, inner_tester);

        Ok(Some(guard))
    }
}
