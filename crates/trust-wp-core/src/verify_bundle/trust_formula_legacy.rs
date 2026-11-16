#![cfg(test)]
#![allow(dead_code)]
// Frozen pre-migration decoder, exercised only as a qualification oracle.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, error::Error, fmt, sync::Arc};

use serde::{
    de::{self, MapAccess, SeqAccess, Visitor},
    Deserialize, Deserializer,
};
use serde_json::{Map, Value};

use crate::{
    formula::{intern_sort_name, BinOp, ExprSort, PureExpr, UnOp},
    verify_bundle::TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
};

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

/// Decode the tRust typed replay-claim fragment into trust-wp's PureExpr IR.
///
/// Accepted payload shape:
///
/// ```text
/// {
///   "schema": "trust-wp.trust-formula.v1",
///   "variables": [{"name": "x", "sort": "int"}],
///   "result": {"name": "result", "sort": "int"},
///   "body": {"op": "gt", "lhs": {"var": "result"}, "rhs": {"var": "x"}}
/// }
/// ```
///
/// The decoder is deliberately fail-closed. It only accepts declared variables,
/// an optional declared result binding, scoped let bindings, quantified
/// bindings, int/bool literals, old/result/var refs, and the arithmetic and
/// boolean operators admitted by native replay.
pub fn decode_trust_formula_v1_claim(payload: &str) -> Result<PureExpr, TrustFormulaDecodeError> {
    decode_trust_formula_v1_declared_claim(payload).map(|claim| claim.body)
}

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

/// Decode a `TrustFormulaV1` claim together with its top-level declarations.
///
/// A consumer that attaches meaning to the claim's names reads them here, so
/// it sees the names the goal is stated over exactly as the decoder does,
/// defaults included.
pub fn decode_trust_formula_v1_declared_claim(
    payload: &str,
) -> Result<TrustFormulaV1Claim, TrustFormulaDecodeError> {
    let value = parse_unique_json(payload)
        .map_err(|err| TrustFormulaDecodeError::new(format!("invalid JSON: {err}")))?;
    let object = value
        .as_object()
        .ok_or_else(|| TrustFormulaDecodeError::new("claim payload must be a JSON object"))?;
    reject_unknown_fields(object, "claim", &["schema", "variables", "result", "body"])?;

    let schema = required_str(object.get("schema"), "schema")?;
    // The compiler-side envelope tags the schema with the namespace token in its
    // identifier spelling (`trust_wp.trust-formula.v1`), while this constant uses
    // the crate spelling (`trust-wp.…`). They denote the same format, so compare
    // separator-canonically (only `_`↔`-` differs) — like the trust-mc identity
    // fix. Distinct schemas (e.g. `…pure-expr.v1`) still mismatch.
    if schema.replace('_', "-") != TRUST_FORMULA_CLAIM_SCHEMA_VERSION {
        return Err(TrustFormulaDecodeError::new(format!(
            "unsupported trust formula schema `{schema}`; expected `{TRUST_FORMULA_CLAIM_SCHEMA_VERSION}`"
        )));
    }

    let mut env: HashMap<String, ExprSort> = HashMap::new();
    let mut declarations = Vec::new();
    if let Some(variables) = object.get("variables") {
        let variables: &[Value] = variables
            .as_array()
            .map(Vec::as_slice)
            .ok_or_else(|| TrustFormulaDecodeError::new("variables must be an array"))?;
        for (index, variable) in variables.iter().enumerate() {
            let binding = decode_binding(variable, &format!("variables[{index}]"))?;
            declarations.push((binding.name.clone(), binding.sort.clone()));
            insert_binding(&mut env, binding)?;
        }
    }

    let result_name = if let Some(result) = object.get("result") {
        let binding = decode_result_binding(result)?;
        let result_name = binding.name.clone();
        declarations.push((binding.name.clone(), binding.sort.clone()));
        insert_binding(&mut env, binding)?;
        Some(result_name)
    } else {
        None
    };

    let body = object
        .get("body")
        .ok_or_else(|| TrustFormulaDecodeError::new("missing required field `body`"))?;
    let body = decode_expr(body, &env, result_name.as_deref(), "body")?;
    validate_native_replay_definedness(&body)?;
    Ok(TrustFormulaV1Claim { declarations, body })
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
    Ok(value.0)
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

struct UniqueJsonValue(Value);

impl<'de> Deserialize<'de> for UniqueJsonValue {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(UniqueJsonVisitor)
    }
}

struct UniqueJsonVisitor;

impl<'de> Visitor<'de> for UniqueJsonVisitor {
    type Value = UniqueJsonValue;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value without duplicate object keys")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Bool(value)))
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Number(value.into())))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Number(value.into())))
    }

    fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        serde_json::Number::from_f64(value)
            .map(Value::Number)
            .map(UniqueJsonValue)
            .ok_or_else(|| E::custom("non-finite JSON number"))
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(UniqueJsonValue(Value::String(value.to_string())))
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::String(value)))
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Null))
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(UniqueJsonValue(Value::Null))
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        UniqueJsonValue::deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut values = Vec::new();
        while let Some(UniqueJsonValue(value)) = sequence.next_element()? {
            values.push(value);
        }
        Ok(UniqueJsonValue(Value::Array(values)))
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut values = Map::new();
        while let Some(key) = map.next_key::<String>()? {
            if values.contains_key(&key) {
                return Err(de::Error::custom(format!(
                    "duplicate JSON object key `{key}`"
                )));
            }
            let UniqueJsonValue(value) = map.next_value()?;
            values.insert(key, value);
        }
        Ok(UniqueJsonValue(Value::Object(values)))
    }
}

/// Validate partial arithmetic before any native replay rule can use
/// reflexivity or implication reasoning over the expression.
pub(super) fn validate_native_replay_definedness(
    expr: &PureExpr,
) -> Result<(), TrustFormulaDecodeError> {
    validate_div_mod_defined(expr, &[])
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Binding {
    name: String,
    sort: ExprSort,
}

fn decode_binding(value: &Value, path: &str) -> Result<Binding, TrustFormulaDecodeError> {
    let object = value
        .as_object()
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path} must be an object")))?;
    reject_unknown_fields(object, path, &["name", "sort"])?;
    let name = required_str(object.get("name"), &format!("{path}.name"))?;
    validate_name(name, &format!("{path}.name"))?;
    let sort = decode_sort(
        required_str(object.get("sort"), &format!("{path}.sort"))?,
        path,
    )?;
    Ok(Binding {
        name: name.to_string(),
        sort,
    })
}

fn decode_result_binding(value: &Value) -> Result<Binding, TrustFormulaDecodeError> {
    let object = value
        .as_object()
        .ok_or_else(|| TrustFormulaDecodeError::new("result must be an object"))?;
    reject_unknown_fields(object, "result", &["name", "sort"])?;
    let name = optional_str(object.get("name"), "result.name")?.unwrap_or("result");
    validate_name(name, "result.name")?;
    let sort = decode_sort(required_str(object.get("sort"), "result.sort")?, "result")?;
    Ok(Binding {
        name: name.to_string(),
        sort,
    })
}

fn insert_binding(
    env: &mut HashMap<String, ExprSort>,
    binding: Binding,
) -> Result<(), TrustFormulaDecodeError> {
    if env.insert(binding.name.clone(), binding.sort).is_some() {
        return Err(TrustFormulaDecodeError::new(format!(
            "duplicate binding `{}`",
            binding.name
        )));
    }
    Ok(())
}

fn decode_expr(
    value: &Value,
    env: &HashMap<String, ExprSort>,
    result_name: Option<&str>,
    path: &str,
) -> Result<PureExpr, TrustFormulaDecodeError> {
    let object = value
        .as_object()
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path} must be an object")))?;

    if let Some(value) = object.get("bool") {
        let value: &Value = value;
        reject_unknown_fields(object, path, &["bool"])?;
        return value
            .as_bool()
            .map(PureExpr::Bool)
            .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.bool must be a boolean")));
    }
    if let Some(value) = object.get("int") {
        let value: &Value = value;
        reject_unknown_fields(object, path, &["int"])?;
        return decode_int_literal(value, path);
    }
    if let Some(value) = object.get("var") {
        let value: &Value = value;
        reject_unknown_fields(object, path, &["var"])?;
        let name = value
            .as_str()
            .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.var must be a string")))?;
        let sort = env.get(name).cloned().ok_or_else(|| {
            TrustFormulaDecodeError::new(format!(
                "{path}.var references undeclared binding `{name}`"
            ))
        })?;
        return Ok(PureExpr::Var(name.to_string(), Some(sort)));
    }
    if let Some(value) = object.get("result") {
        let value: &Value = value;
        reject_unknown_fields(object, path, &["result"])?;
        let true_value = value.as_bool().ok_or_else(|| {
            TrustFormulaDecodeError::new(format!("{path}.result must be boolean true"))
        })?;
        if !true_value {
            return Err(TrustFormulaDecodeError::new(format!(
                "{path}.result must be boolean true"
            )));
        }
        let name = result_name.ok_or_else(|| {
            TrustFormulaDecodeError::new(format!(
                "{path}.result requires a top-level result binding"
            ))
        })?;
        let sort = env.get(name).cloned().ok_or_else(|| {
            TrustFormulaDecodeError::new("top-level result binding is missing from environment")
        })?;
        return Ok(PureExpr::Var(name.to_string(), Some(sort)));
    }
    if let Some(inner) = object.get("old") {
        reject_unknown_fields(object, path, &["old"])?;
        return Ok(PureExpr::Old(Arc::new(decode_expr(
            inner,
            env,
            result_name,
            &format!("{path}.old"),
        )?)));
    }

    let op = required_str(object.get("op"), &format!("{path}.op"))?;
    match op {
        "not" | "neg" => {
            reject_unknown_fields(object, path, &["op", "expr"])?;
            let expr = object
                .get("expr")
                .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.expr is required")))?;
            let op = if op == "not" { UnOp::Not } else { UnOp::Neg };
            Ok(PureExpr::UnOp(
                op,
                Arc::new(decode_expr(
                    expr,
                    env,
                    result_name,
                    &format!("{path}.expr"),
                )?),
            ))
        }
        "let" => decode_let_expr(object, env, result_name, path),
        "forall" | "exists" => decode_quantifier_expr(op, object, env, result_name, path),
        "add" | "sub" | "mul" | "div" | "mod" | "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and"
        | "or" | "implies" => {
            reject_unknown_fields(object, path, &["op", "lhs", "rhs"])?;
            let lhs = object
                .get("lhs")
                .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.lhs is required")))?;
            let rhs = object
                .get("rhs")
                .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.rhs is required")))?;
            Ok(PureExpr::BinOp(
                Arc::new(decode_expr(lhs, env, result_name, &format!("{path}.lhs"))?),
                decode_bin_op(op),
                Arc::new(decode_expr(rhs, env, result_name, &format!("{path}.rhs"))?),
            ))
        }
        unsupported => Err(TrustFormulaDecodeError::new(format!(
            "{path}.op `{unsupported}` is outside the trust-formula v1 native int/bool fragment"
        ))),
    }
}

fn decode_int_literal(value: &Value, path: &str) -> Result<PureExpr, TrustFormulaDecodeError> {
    value
        .as_i64()
        .map(PureExpr::Int)
        .or_else(|| {
            value
                .as_u64()
                .map(crate::formula::int_bounds::unsigned_literal_expr)
        })
        .ok_or_else(|| {
            TrustFormulaDecodeError::new(format!(
                "{path}.int must be an exact signed or unsigned 64-bit integer"
            ))
        })
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

fn decode_quantifier_expr(
    op: &str,
    object: &Map<String, Value>,
    env: &HashMap<String, ExprSort>,
    result_name: Option<&str>,
    path: &str,
) -> Result<PureExpr, TrustFormulaDecodeError> {
    reject_unknown_fields(object, path, &["op", "name", "sort", "body"])?;
    let name = required_str(object.get("name"), &format!("{path}.name"))?;
    validate_name(name, &format!("{path}.name"))?;
    if env.contains_key(name) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path}.name shadows existing binding `{name}`"
        )));
    }
    let written_sort = required_str(object.get("sort"), &format!("{path}.sort"))?;
    let sort = decode_sort(written_sort, path)?;
    // A binder ranges over its sort, and native replay models the range of
    // `int`, `bool` and a reference (a pointer) only: a type parameter could
    // be any type, a sequence is not an integer, and either was read as one.
    if !matches!(
        sort,
        ExprSort::Int | ExprSort::Bool | ExprSort::Ref(_) | ExprSort::MutRef(_)
    ) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path}.sort `{written_sort}` is a quantifier sort native replay does not model: a \
             binder ranges over `int`, `bool` or a reference"
        )));
    }
    let body = object
        .get("body")
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.body is required")))?;

    let mut scoped_env = env.clone();
    insert_binding(
        &mut scoped_env,
        Binding {
            name: name.to_string(),
            sort: sort.clone(),
        },
    )?;
    let body = Arc::new(decode_expr(
        body,
        &scoped_env,
        result_name,
        &format!("{path}.body"),
    )?);

    match op {
        "forall" => Ok(PureExpr::Forall {
            var: name.to_string(),
            var_sort: Some(sort),
            body,
            triggers: Vec::new(),
        }),
        "exists" => Ok(PureExpr::Exists {
            var: name.to_string(),
            var_sort: Some(sort),
            body,
            triggers: Vec::new(),
        }),
        _ => unreachable!("quantifier operator checked by caller"),
    }
}

fn decode_let_expr(
    object: &Map<String, Value>,
    env: &HashMap<String, ExprSort>,
    result_name: Option<&str>,
    path: &str,
) -> Result<PureExpr, TrustFormulaDecodeError> {
    reject_unknown_fields(object, path, &["op", "name", "sort", "value", "body"])?;
    let name = required_str(object.get("name"), &format!("{path}.name"))?;
    validate_name(name, &format!("{path}.name"))?;
    if env.contains_key(name) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path}.name shadows existing binding `{name}`"
        )));
    }
    let sort = decode_sort(
        required_str(object.get("sort"), &format!("{path}.sort"))?,
        path,
    )?;
    let value = object
        .get("value")
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.value is required")))?;
    let body = object
        .get("body")
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.body is required")))?;
    let value = decode_expr(value, env, result_name, &format!("{path}.value"))?;
    // The declaration types every read of the name in the body; the value is
    // what those reads denote. A value of another sort would be read at the
    // declared sort by the body and at its own by whatever inlines it.
    match decoded_sort(&value) {
        Some(value_sort) if value_sort == sort => {}
        found => {
            return Err(TrustFormulaDecodeError::new(format!(
                "{path} declares `{name}` at sort `{sort}` but binds it to a value of sort `{}`",
                found.map_or_else(|| "unknown".to_string(), |found| found.to_string())
            )));
        }
    }
    let mut scoped_env = env.clone();
    insert_binding(
        &mut scoped_env,
        Binding {
            name: name.to_string(),
            sort,
        },
    )?;
    Ok(PureExpr::Let {
        var: name.to_string(),
        value: Arc::new(value),
        body: Arc::new(decode_expr(
            body,
            &scoped_env,
            result_name,
            &format!("{path}.body"),
        )?),
    })
}

/// The sort of an expression this decoder produced: every name it emits
/// carries its declared sort, so the sort follows from the syntax. `None` for
/// a shape the decoder never emits.
fn decoded_sort(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Bool(_) => Some(ExprSort::Bool),
        PureExpr::Int(_) => Some(ExprSort::Int),
        PureExpr::Var(_, sort) => sort.clone(),
        PureExpr::Old(inner) => decoded_sort(inner),
        PureExpr::Let { body, .. } => decoded_sort(body),
        PureExpr::UnOp(UnOp::Not, _) | PureExpr::Forall { .. } | PureExpr::Exists { .. } => {
            Some(ExprSort::Bool)
        }
        PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, _) => Some(ExprSort::Int),
        PureExpr::BinOp(_, op, _) => Some(match op {
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or
            | BinOp::Implies => ExprSort::Bool,
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
            | BinOp::BitOr => ExprSort::Int,
        }),
        _ => None,
    }
}

fn decode_bin_op(op: &str) -> BinOp {
    match op {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        "div" => BinOp::Div,
        "mod" => BinOp::Mod,
        "eq" => BinOp::Eq,
        "ne" => BinOp::Ne,
        "lt" => BinOp::Lt,
        "le" => BinOp::Le,
        "gt" => BinOp::Gt,
        "ge" => BinOp::Ge,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "implies" => BinOp::Implies,
        _ => unreachable!("operator checked by caller"),
    }
}

fn decode_sort(sort: &str, path: &str) -> Result<ExprSort, TrustFormulaDecodeError> {
    let sort = sort.trim();
    if let Some(inner) = sort.strip_prefix("&mut ") {
        return Ok(ExprSort::MutRef(Box::new(decode_sort(inner, path)?)));
    }
    if let Some(inner) = sort.strip_prefix('&') {
        return Ok(ExprSort::Ref(Box::new(decode_sort(inner, path)?)));
    }
    if sort.starts_with('[') && sort.ends_with(']') {
        let inner = sort[1..sort.len() - 1].trim();
        if inner.is_empty() {
            return Err(TrustFormulaDecodeError::new(format!(
                "{path}.sort slice element type is empty"
            )));
        }
        let _ = decode_sort(inner, path)?;
        return Ok(ExprSort::Seq);
    }

    match sort {
        "int" | "Int" => Ok(ExprSort::Int),
        "bool" | "Bool" => Ok(ExprSort::Bool),
        "seq" | "Seq" => Ok(ExprSort::Seq),
        type_param if is_type_param_sort(type_param) => {
            Ok(ExprSort::TypeParam(intern_sort_name(type_param)))
        }
        unsupported => Err(TrustFormulaDecodeError::new(format!(
            "{path}.sort `{unsupported}` is outside the trust-formula v1 native replay sort fragment"
        ))),
    }
}

fn is_type_param_sort(sort: &str) -> bool {
    let mut chars = sort.chars();
    matches!(
        (chars.next(), chars.next()),
        (Some(ch), None) if ch.is_ascii_uppercase()
    )
}

fn required_str<'a>(
    value: Option<&'a Value>,
    path: &str,
) -> Result<&'a str, TrustFormulaDecodeError> {
    value
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("missing required field `{path}`")))?
        .as_str()
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path} must be a string")))
}

fn optional_str<'a>(
    value: Option<&'a Value>,
    path: &str,
) -> Result<Option<&'a str>, TrustFormulaDecodeError> {
    value
        .map(|value: &Value| {
            value
                .as_str()
                .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path} must be a string")))
        })
        .transpose()
}

fn validate_name(name: &str, path: &str) -> Result<(), TrustFormulaDecodeError> {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return Err(TrustFormulaDecodeError::new(format!("{path} is empty")));
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path} must start with `_` or an ASCII letter"
        )));
    }
    // Accept the SMT-symbol characters the compiler's VC generator legitimately
    // emits in variable names: SSA version suffixes (`_0#s0_0`) and place
    // projections (`_t.0`, `arr[_i]`, `*p`, `@1`, `[off;min=2]`). These are
    // opaque keys in trust-wp's native pure replay (and quoted in any textual
    // SMT backend), and the bounds-obligation path already accepts them — so the
    // postcondition/refinement claim schema must too, rather than fail-closing a
    // legitimate name and reporting a contract `Unsupported`.
    if !chars.all(is_claim_name_char) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path} contains characters outside the supported SMT-symbol set"
        )));
    }
    Ok(())
}

/// Characters permitted after the first in a `trust_wp.trust-formula.v1` variable
/// name: identifier characters plus the SSA-version (`#`) and place-projection
/// sigils (`.`, `[`, `]`, `*`, `@`, `-`, `;`, `=`) the trust-vcgen formula layer
/// produces. The leading character is still constrained to `_` or an ASCII
/// letter by the caller, matching every base local / source name.
fn is_claim_name_char(ch: char) -> bool {
    ch == '_'
        || ch.is_ascii_alphanumeric()
        || matches!(ch, '#' | '.' | '[' | ']' | '*' | '@' | '-' | ';' | '=')
}

fn reject_unknown_fields(
    object: &Map<String, Value>,
    path: &str,
    allowed: &[&str],
) -> Result<(), TrustFormulaDecodeError> {
    if let Some(field) = object
        .keys()
        .find(|field: &&String| !allowed.contains(&field.as_str()))
    {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path} contains unsupported field `{field}`"
        )));
    }
    Ok(())
}
