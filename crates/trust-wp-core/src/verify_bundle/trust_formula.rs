// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{error::Error, fmt, sync::Arc};

use serde::{de, Deserialize};
use serde_json::Value;
use trust_ir_contract::{
    proof_json::UniqueJsonValue,
    trust_formula_v1::{self as wire, Algebra, DecodePolicy, WireSort},
};

use crate::formula::{intern_sort_name, BinOp, ExprSort, PureExpr, UnOp};

/// Error returned when a `TrustFormulaV1` replay claim is malformed or outside
/// trust-wp's native replay fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustFormulaDecodeError {
    message: String,
}

impl TrustFormulaDecodeError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for TrustFormulaDecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for TrustFormulaDecodeError {}

/// A `TrustFormulaV1` claim as the decoder reads it.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustFormulaV1Claim {
    /// The top-level `variables`, then the `result` declaration, as
    /// `(name, sort)`: the only free names `body` can have. A `result` record
    /// without a `name` declares `result`.
    pub declarations: Vec<(String, ExprSort)>,
    /// The goal.
    pub body: PureExpr,
}

/// Decode the common typed wire claim into the existing native expression IR.
pub fn decode_trust_formula_v1_claim(payload: &str) -> Result<PureExpr, TrustFormulaDecodeError> {
    decode_trust_formula_v1_declared_claim(payload).map(|claim| claim.body)
}

/// Decode a claim with its declarations, preserving their original order.
pub fn decode_trust_formula_v1_declared_claim(
    payload: &str,
) -> Result<TrustFormulaV1Claim, TrustFormulaDecodeError> {
    decode_trust_formula_v1_declared_claim_and_value(payload).map(|(claim, _)| claim)
}

/// Decode once while retaining original syntax for exact proof-atom projection.
/// The value is data, not a second interpreter or a proof of the claim.
pub fn decode_trust_formula_v1_declared_claim_and_value(
    payload: &str,
) -> Result<(TrustFormulaV1Claim, Value), TrustFormulaDecodeError> {
    let value = parse_unique_json(payload)
        .map_err(|err| TrustFormulaDecodeError::new(format!("invalid JSON: {err}")))?;
    let decoded = wire::decode_value(&value, DecodePolicy::NativeReplay, &mut NativeReplayAlgebra)
        .map_err(|error| TrustFormulaDecodeError::new(error.to_string()))?;
    let claim = TrustFormulaV1Claim {
        declarations: decoded
            .declarations
            .into_iter()
            .map(|(name, sort)| (name, native_sort(&sort)))
            .collect(),
        body: decoded.body,
    };
    validate_native_replay_definedness(&claim.body)?;
    Ok((claim, value))
}

fn native_sort(sort: &WireSort) -> ExprSort {
    match sort {
        WireSort::Bool => ExprSort::Bool,
        WireSort::Int => ExprSort::Int,
        WireSort::Seq => ExprSort::Seq,
        WireSort::Ref { mutable, inner } => {
            let inner = Box::new(native_sort(inner));
            if *mutable {
                ExprSort::MutRef(inner)
            } else {
                ExprSort::Ref(inner)
            }
        }
        WireSort::TypeParam(name) => ExprSort::TypeParam(intern_sort_name(&name.to_string())),
    }
}

struct NativeReplayAlgebra;

impl Algebra for NativeReplayAlgebra {
    type Expr = PureExpr;

    fn bool_literal(&mut self, value: bool) -> PureExpr {
        PureExpr::Bool(value)
    }
    fn integer_literal(&mut self, value: wire::IntegerLiteral) -> PureExpr {
        match value {
            wire::IntegerLiteral::I64(value) => PureExpr::Int(value),
            wire::IntegerLiteral::U64(value) => {
                crate::formula::int_bounds::unsigned_literal_expr(value)
            }
        }
    }
    fn variable(&mut self, name: &str, sort: &WireSort) -> PureExpr {
        PureExpr::Var(name.to_owned(), Some(native_sort(sort)))
    }
    fn old(&mut self, expr: PureExpr) -> PureExpr {
        PureExpr::Old(Arc::new(expr))
    }
    fn unary(&mut self, op: wire::UnaryOp, expr: PureExpr) -> PureExpr {
        let op = match op {
            wire::UnaryOp::Not => UnOp::Not,
            wire::UnaryOp::Neg => UnOp::Neg,
        };
        PureExpr::UnOp(op, Arc::new(expr))
    }
    fn binary(&mut self, op: wire::BinaryOp, left: PureExpr, right: PureExpr) -> PureExpr {
        let op = match op {
            wire::BinaryOp::Add => BinOp::Add,
            wire::BinaryOp::Sub => BinOp::Sub,
            wire::BinaryOp::Mul => BinOp::Mul,
            wire::BinaryOp::Div => BinOp::Div,
            wire::BinaryOp::Mod => BinOp::Mod,
            wire::BinaryOp::Eq => BinOp::Eq,
            wire::BinaryOp::Ne => BinOp::Ne,
            wire::BinaryOp::Lt => BinOp::Lt,
            wire::BinaryOp::Le => BinOp::Le,
            wire::BinaryOp::Gt => BinOp::Gt,
            wire::BinaryOp::Ge => BinOp::Ge,
            wire::BinaryOp::And => BinOp::And,
            wire::BinaryOp::Or => BinOp::Or,
            wire::BinaryOp::Implies => BinOp::Implies,
        };
        PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
    }
    fn let_binding(
        &mut self,
        name: &str,
        _sort: &WireSort,
        value: PureExpr,
        body: PureExpr,
    ) -> PureExpr {
        PureExpr::Let {
            var: name.to_owned(),
            value: Arc::new(value),
            body: Arc::new(body),
        }
    }
    fn quantified(
        &mut self,
        quantifier: wire::Quantifier,
        name: &str,
        sort: &WireSort,
        body: PureExpr,
    ) -> PureExpr {
        let var = name.to_owned();
        let var_sort = Some(native_sort(sort));
        let body = Arc::new(body);
        match quantifier {
            wire::Quantifier::Forall => PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers: Vec::new(),
            },
            wire::Quantifier::Exists => PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers: Vec::new(),
            },
        }
    }
}

/// Parse a proof-bearing claim with one unambiguous interpretation.
///
/// `serde_json::Value` otherwise silently keeps the last occurrence of a
/// duplicate object key. Reject duplicates recursively so a producer, replay
/// checker, and evidence consumer cannot disagree about which schema, body, or
/// operator the payload commits to.
fn parse_unique_json(payload: &str) -> Result<Value, serde_json::Error> {
    // The formula consumer has a bounded deeper acyclic-body fragment. Check
    // lexical JSON nesting before asking serde to parse beyond its default
    // depth; the original duplicate-key visitor still reads every object.
    check_json_nesting(payload).map_err(de::Error::custom)?;
    let mut decoder = serde_json::Deserializer::from_str(payload);
    decoder.disable_recursion_limit();
    let value = UniqueJsonValue::deserialize(&mut decoder)?;
    decoder.end()?;
    Ok(value.into_value())
}

fn check_json_nesting(payload: &str) -> Result<(), &'static str> {
    const MAX_JSON_DEPTH: usize = 260;
    let mut depth = 0_usize;
    let mut quoted = false;
    let mut escaped = false;
    for byte in payload.bytes() {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'{' | b'[' => {
                    depth = depth.checked_add(1).ok_or("JSON nesting overflow")?;
                    if depth > MAX_JSON_DEPTH {
                        return Err("JSON nesting exceeds native formula depth budget");
                    }
                }
                b'}' | b']' => depth = depth.checked_sub(1).ok_or("unbalanced JSON nesting")?,
                _ => {}
            }
        }
    }
    Ok(())
}

pub(super) fn validate_native_replay_definedness(
    expr: &PureExpr,
) -> Result<(), TrustFormulaDecodeError> {
    validate_div_mod_defined(expr, &[])
}

fn validate_div_mod_defined(
    expr: &PureExpr,
    assumptions: &[PureExpr],
) -> Result<(), TrustFormulaDecodeError> {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            let mut scoped = assumptions.to_vec();
            collect_definedness_facts(expr, &mut scoped);
            validate_div_mod_defined(left, &scoped)?;
            validate_div_mod_defined(right, &scoped)
        }
        PureExpr::BinOp(left, BinOp::Implies, right) => {
            let mut scoped = assumptions.to_vec();
            collect_definedness_facts(left, &mut scoped);
            validate_div_mod_defined(left, &scoped)?;
            validate_div_mod_defined(right, &scoped)
        }
        PureExpr::BinOp(
            left,
            op @ (BinOp::Div | BinOp::Mod | BinOp::DivTrunc | BinOp::RemTrunc),
            right,
        ) => {
            validate_div_mod_defined(left, assumptions)?;
            validate_div_mod_defined(right, assumptions)?;
            if pure_expr_known_nonzero(right, assumptions) {
                Ok(())
            } else {
                Err(TrustFormulaDecodeError::new(format!(
                    "TrustFormulaV1 `{}` divisor must be syntactically nonzero or guarded by a nonzero assumption",
                    match op {
                        BinOp::Div | BinOp::DivTrunc => "div",
                        BinOp::Mod | BinOp::RemTrunc => "mod",
                        _ => unreachable!("operator pattern is fixed"),
                    }
                )))
            }
        }
        PureExpr::BinOp(left, _, right) => {
            validate_div_mod_defined(left, assumptions)?;
            validate_div_mod_defined(right, assumptions)
        }
        // Entry-state expressions need entry-state definedness evidence. A
        // current-state guard such as `denominator != 0` says nothing about
        // `old(denominator)`, so never carry the surrounding assumptions
        // across this state boundary.
        PureExpr::Old(inner) => validate_div_mod_defined(inner, &[]),
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => validate_div_mod_defined(inner, assumptions),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            validate_div_mod_defined(cond, assumptions)?;
            validate_div_mod_defined(then_expr, assumptions)?;
            validate_div_mod_defined(else_expr, assumptions)
        }
        PureExpr::Let { value, body, .. } => {
            validate_div_mod_defined(value, assumptions)?;
            validate_div_mod_defined(body, assumptions)
        }
        PureExpr::Forall { body, .. }
        | PureExpr::Exists { body, .. }
        | PureExpr::Closure { body, .. } => validate_div_mod_defined(body, assumptions),
        PureExpr::LetAssume { assumption, body } => {
            validate_div_mod_defined(assumption, assumptions)?;
            let mut scoped = assumptions.to_vec();
            collect_definedness_facts(assumption, &mut scoped);
            validate_div_mod_defined(body, &scoped)
        }
        PureExpr::LetObligation { obligation, body } => {
            validate_div_mod_defined(obligation, assumptions)?;
            let mut scoped = assumptions.to_vec();
            collect_definedness_facts(obligation, &mut scoped);
            validate_div_mod_defined(body, &scoped)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            validate_div_mod_defined(receiver, assumptions)?;
            for arg in args {
                validate_div_mod_defined(arg, assumptions)?;
            }
            Ok(())
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                validate_div_mod_defined(arg, assumptions)?;
            }
            Ok(())
        }
        PureExpr::Match { scrutinee, arms } => {
            validate_div_mod_defined(scrutinee, assumptions)?;
            for arm in arms {
                validate_div_mod_defined(&arm.body, assumptions)?;
            }
            Ok(())
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => Ok(()),
    }
}

fn collect_definedness_facts(expr: &PureExpr, facts: &mut Vec<PureExpr>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_definedness_facts(left, facts);
            collect_definedness_facts(right, facts);
        }
        PureExpr::BinOp(_, op, _)
            if is_definedness_fact_operator(*op) && !contains_div_mod(expr) =>
        {
            facts.push(expr.clone());
        }
        _ => {}
    }
}

fn is_definedness_fact_operator(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

fn pure_expr_known_nonzero(expr: &PureExpr, assumptions: &[PureExpr]) -> bool {
    constant_int(expr).is_some_and(|value| value != 0)
        || assumptions
            .iter()
            .any(|assumption| pure_assumption_proves_nonzero(assumption, expr))
}

fn pure_assumption_proves_nonzero(assumption: &PureExpr, target: &PureExpr) -> bool {
    let PureExpr::BinOp(left, op, right) = assumption else {
        return false;
    };
    match op {
        BinOp::Ne => {
            (left.as_ref() == target && is_int_zero(right))
                || (right.as_ref() == target && is_int_zero(left))
        }
        BinOp::Gt => {
            (left.as_ref() == target && is_int_zero(right))
                || (is_int_zero(left) && right.as_ref() == target)
        }
        BinOp::Lt => {
            (left.as_ref() == target && is_int_zero(right))
                || (is_int_zero(left) && right.as_ref() == target)
        }
        _ => false,
    }
}

fn contains_div_mod(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(_, BinOp::Div | BinOp::Mod | BinOp::DivTrunc | BinOp::RemTrunc, _) => true,
        PureExpr::BinOp(left, _, right) => contains_div_mod(left) || contains_div_mod(right),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_div_mod(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_div_mod(cond) || contains_div_mod(then_expr) || contains_div_mod(else_expr)
        }
        PureExpr::Let { value, body, .. } => contains_div_mod(value) || contains_div_mod(body),
        PureExpr::Forall { body, .. }
        | PureExpr::Exists { body, .. }
        | PureExpr::Closure { body, .. } => contains_div_mod(body),
        PureExpr::LetAssume { assumption, body } => {
            contains_div_mod(assumption) || contains_div_mod(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_div_mod(obligation) || contains_div_mod(body)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_div_mod(receiver) || args.iter().any(contains_div_mod)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(contains_div_mod),
        PureExpr::Match { scrutinee, arms } => {
            contains_div_mod(scrutinee) || arms.iter().any(|arm| contains_div_mod(&arm.body))
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
    }
}

fn is_int_zero(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Int(0))
}

fn constant_int(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        _ => None,
    }
}

#[cfg(test)]
#[path = "trust_formula_legacy.rs"]
mod legacy;

#[cfg(test)]
mod codec_equivalence_tests {
    use serde_json::json;

    use super::*;

    fn same(payload: &str) {
        let old = legacy::decode_trust_formula_v1_declared_claim(payload);
        let new = decode_trust_formula_v1_declared_claim(payload);
        match (old, new) {
            (Ok(old), Ok(new)) => {
                assert_eq!(old.declarations, new.declarations, "{payload}");
                assert_eq!(old.body, new.body, "{payload}");
            }
            (Err(_), Err(_)) => {}
            (old, new) => {
                panic!("decoder admission changed for {payload}: old={old:?}, new={new:?}")
            }
        }
    }

    fn claim(body: Value) -> Value {
        json!({"schema":"trust_wp.trust_formula.v1", "variables":[
            {"name":"x#0","sort":"Int"}, {"name":"flag","sort":"Bool"}],
            "result":{"sort":"Int"},"body":body})
    }

    #[test]
    fn shared_codec_matches_frozen_native_expression_and_scope_oracle() {
        let x = json!({"var":"x#0"});
        for body in [
            json!({"bool":true}),
            json!({"bool":false}),
            json!({"result":true}),
            json!({"int":i64::MIN}),
            json!({"int":i64::MAX}),
            json!({"int":1_u64 << 63}),
            json!({"int":u64::MAX}),
            json!({"old":x.clone()}),
            json!({"op":"not","expr":{"var":"flag"}}),
            json!({"op":"neg","expr":x.clone()}),
            json!({"op":"let","name":"local","sort":"int","value":x.clone(),"body":{"var":"local"}}),
        ] {
            same(&claim(body).to_string());
        }
        for op in [
            "add", "sub", "mul", "div", "mod", "eq", "ne", "lt", "le", "gt", "ge", "and", "or",
            "implies",
        ] {
            same(&claim(json!({"op":op,"lhs":x,"rhs":{"int":3}})).to_string());
        }
        for sort in [
            "int",
            "Int",
            "bool",
            "Bool",
            "seq",
            "Seq",
            "[Int]",
            "&Int",
            "&mut Bool",
            "T",
        ] {
            let mut value = claim(json!({"bool":true}));
            value["variables"][0]["sort"] = json!(sort);
            same(&value.to_string());
            for quantifier in ["forall", "exists"] {
                value["body"] =
                    json!({"op":quantifier,"name":"bound","sort":sort,"body":{"bool":true}});
                same(&value.to_string());
            }
        }
        for body in [
            json!({"op":"let","name":"x#0","sort":"int","value":{"int":0},"body":{"bool":true}}),
            json!({"op":"let","name":"local","sort":"int","value":{"bool":true},"body":{"bool":true}}),
            json!({"var":"undeclared"}),
            json!({"result":false}),
            json!({"op":"unknown","lhs":x,"rhs":{"int":1}}),
            json!({"op":"div","lhs":x,"rhs":{"int":0}}),
        ] {
            same(&claim(body).to_string());
        }
        let nonzero = json!({"op":"ne","lhs":x,"rhs":{"int":0}});
        let division = json!({"op":"div","lhs":{"int":7},"rhs":x});
        same(&claim(json!({"op":"implies","lhs":nonzero,"rhs":{"op":"eq","lhs":division.clone(),"rhs":{"int":1}}})).to_string());
        same(&claim(json!({"op":"implies","lhs":nonzero,"rhs":{"old":division}})).to_string());
        for schema in ["trust_wp.trust_formula.v1", "trust-wp.trust-formula.v1"] {
            let mut value = claim(json!({"bool":true}));
            value["schema"] = json!(schema);
            same(&value.to_string());
        }
    }

    #[test]
    fn shared_codec_matches_frozen_duplicate_trailing_and_depth_refusals() {
        for payload in [
            r#"{"schema":"trust-wp.trust-formula.v1","body":{"bool":true},"body":{"bool":false}}"#,
            r#"{"schema":"trust-wp.trust-formula.v1","body":{"op":"not","op":"neg","expr":{"bool":true}}}"#,
            r#"{"schema":"trust-wp.trust-formula.v1","body":{"bool":true}} true"#,
            r#""source formula""#,
        ] {
            same(payload);
        }
        for depth in [120, 240, 270] {
            let mut body = String::from(r#"{"bool":true}"#);
            for _ in 0..depth {
                body = format!(r#"{{"op":"not","expr":{body}}}"#);
            }
            let payload = format!(r#"{{"schema":"trust-wp.trust-formula.v1","body":{body}}}"#);
            same(&payload);
        }
    }
}
