// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Operator encoding for the AY encoder.
//!
//! Binary and unary operator encoding, Bool-context operand handling, bitwise
//! BV (bitvector) encoding, legacy UF axioms, and division proof obligations.
//!
//! Bitwise operations (AND, OR, XOR, SHL, SHR) use ay's native BV theory by
//! default via `encode_int_binop_bv` (#2666). Int-sorted operands are
//! converted to BV(64) via `int2bv`, the native BV operation is applied, and
//! the result is converted back to Int via `bv2int`. The legacy UF path
//! (`encode_int_binop_uf`) is retained for test backward compatibility but is
//! unreachable in production since `bitwise_proof_mode` defaults to `true`.

use std::collections::HashSet;

use ay_dpll::api::{Sort, Term, TermKind};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use tracing::debug;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};

use super::{
    coerce_to_numeric, collect_bool_hints,
    sort_context::{collect_names_as_bool, is_seq_family_sort},
    unsoundness, AYEncoder, NumericOperandMode,
};
use crate::error::EncodingError;

/// A machine-integer bit operation encoded at its type (D-242).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MachineBitOp {
    And,
    Or,
    Xor,
    Shl,
    Shr,
    /// `!` (bitwise complement).
    Not,
}

impl MachineBitOp {
    /// The binary bit operator `op`, if it is one.
    pub(crate) fn from_binop(op: BinOp) -> Option<Self> {
        Some(match op {
            BinOp::BitAnd => Self::And,
            BinOp::BitOr => Self::Or,
            BinOp::BitXor => Self::Xor,
            BinOp::Shl => Self::Shl,
            BinOp::Shr => Self::Shr,
            _ => return None,
        })
    }
}

/// Bitwise operation kind for the native BV encoding path (#2666).
enum BitwiseBvOp {
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

fn expr_is_known_int_key_for_bool_context(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::Var(_, Some(sort)) => {
            super::sort_context::expr_sort_to_ay_sort(sort) == Sort::Int
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_is_known_int_key_for_bool_context(inner),
        PureExpr::UnOp(UnOp::Neg, inner) => expr_is_known_int_key_for_bool_context(inner),
        PureExpr::BinOp(left, op, right) => {
            matches!(
                op,
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
                    | BinOp::BitOr
            ) && expr_is_known_int_key_for_bool_context(left)
                && expr_is_known_int_key_for_bool_context(right)
        }
        // A machine bit operation at its type (D-242) is an integer.
        PureExpr::LogicFnCall { name, .. } => super::parse_int_bitop_name(name).is_some(),
        PureExpr::MethodCall { method, .. } => matches!(
            method.as_str(),
            "len"
                | "len_logic"
                | "pow2"
                | "sum"
                | "deep_model"
                | "shallow_model"
                | "discriminant"
                | "capacity"
        ),
        _ => false,
    }
}

/// Which bound axioms to assert for a bitwise UF on non-negative inputs (#2666).
enum BitwiseBoundKind {
    /// AND: `result >= 0`, `result <= x`, `result <= y`
    AndBounds,
    /// OR: `result >= 0`, `result >= x`, `result >= y`
    OrBounds,
    /// XOR: `result >= 0` only
    NonNegOnly,
    /// SHL: `result >= 0`, `result >= x`
    ShlBounds,
    /// SHR: `result >= 0`, `result <= x`
    ShrBounds,
}

/// Default bitvector width for Int↔BV conversion in bitwise proof mode.
///
/// When the encoder operates on `Sort::Int` terms (the default for Rust
/// integer variables in trust-wp's encoding), bitwise operations need a
/// concrete BV width for the Int→BV→Int round-trip. We use 64 bits as
/// the default since it covers the common Rust integer types (u8..u64)
/// via the modular semantics of `int2bv`. For types wider than 64 bits
/// (u128, i128), this may produce incorrect results. (#2666)
const DEFAULT_BV_WIDTH: u32 = 64;

/// SMT-LIB Euclidean integer division `(div n d)` for `d != 0`.
///
/// Matches ay's model evaluator `euclidean_div` (the remainder always
/// satisfies `0 <= n - d*q < |d|`). Rust's `BigInt` `/` truncates toward
/// zero, so adjust the quotient when the truncated remainder is negative.
fn euclidean_div_bigint(n: &BigInt, d: &BigInt) -> BigInt {
    let zero = BigInt::from(0);
    let q = n / d;
    let r = n - &q * d;
    if r < zero {
        if *d > zero {
            q - 1
        } else {
            q + 1
        }
    } else {
        q
    }
}

impl AYEncoder {
    /// Encode a binary operation.
    ///
    /// `eq_sort` is retained for equality-sort bookkeeping and fallback
    /// unsoundness tracking. High-level Bool formula equality still routes
    /// through `eq_or_iff()` to preserve completeness on complex verification
    /// formulas, while lower-level callers can use `eq_term()` directly. (#1179)
    #[allow(clippy::unnecessary_wraps)] // Consistent with other encode_* methods
    pub(super) fn encode_binop(
        &mut self,
        l: Term,
        op: BinOp,
        r: Term,
        eq_sort: Option<&Sort>,
    ) -> Result<Term, EncodingError> {
        self.encode_binop_with_bv_hint(l, op, r, eq_sort, None)
    }

    /// [`Self::encode_binop`] with an optional signed narrow-width hint for
    /// bitwise operators (see [`Self::signed_narrow_bitwise_hint`]).
    #[allow(clippy::unnecessary_wraps)] // Consistent with other encode_* methods
    pub(super) fn encode_binop_with_bv_hint(
        &mut self,
        l: Term,
        op: BinOp,
        r: Term,
        eq_sort: Option<&Sort>,
        signed_narrow: Option<u32>,
    ) -> Result<Term, EncodingError> {
        self.refuse_float_binop(l, op, r)?;
        Ok(match op {
            BinOp::Add => {
                let (l, r) =
                    coerce_to_numeric(&mut self.solver, l, r, NumericOperandMode::IntOrReal);
                self.solver.add(l, r)
            }
            BinOp::Sub => {
                let (l, r) =
                    coerce_to_numeric(&mut self.solver, l, r, NumericOperandMode::IntOrReal);
                self.solver.sub(l, r)
            }
            BinOp::Mul => {
                let (l, r) =
                    coerce_to_numeric(&mut self.solver, l, r, NumericOperandMode::IntOrReal);
                // Genuinely nonlinear integer products (`x * y` where neither
                // operand is an integer literal) are not supported by ay's
                // linear arithmetic core: a native `(* x y)` term taints the
                // whole query, forcing the LRA bridge to return Unknown. Such a
                // term is already effectively unconstrained, so we lose nothing
                // by routing it through an *uninterpreted* Int function instead.
                // The opaque UF keeps the query inside the supported linear
                // fragment, and the nonlinear-product-bound completeness pass
                // (`assert_nonlinear_product_bounds`) can then attach the SOUND
                // monotonicity bound `0<=x<=kx && 0<=y<=ky ==> nlmul(x,y) <= kx*ky`
                // when constant operand bounds are derivable. Linear products
                // (`2 * x`, `x * 1000`) keep the native, fully-supported
                // `*` encoding. (#knights-tour nonlinear product bound)
                if self.solver.get_sort(l) == Sort::Int
                    && self.solver.get_sort(r) == Sort::Int
                    && self.term_int_literal_for_arithmetic(l).is_none()
                    && self.term_int_literal_for_arithmetic(r).is_none()
                {
                    self.encode_nonlinear_mul_uf(l, r)
                } else {
                    self.solver.mul(l, r)
                }
            }
            BinOp::Div => {
                let (l, r) =
                    coerce_to_numeric(&mut self.solver, l, r, NumericOperandMode::IntOrReal);
                // Both-literal integer division folds to its exact Euclidean
                // quotient constant (mirrors the BinOp::Mod literal/literal fold
                // below). This keeps ground `c1/c2` a concrete Int — the linear
                // Euclidean axiom alone only pins the UF quotient up to integer
                // tightening, which can leave a ground UF result unconstrained
                // when the solver does not interpret the UF application.
                if self.solver.get_sort(l) == Sort::Int {
                    if let (Some(dividend), Some(divisor)) = (
                        self.term_int_literal_for_arithmetic(l),
                        self.term_int_literal_for_arithmetic(r),
                    ) {
                        if divisor != BigInt::from(0) {
                            let quotient = euclidean_div_bigint(&dividend, &divisor);
                            if let Some(value) = quotient.to_i64() {
                                return Ok(self.solver.int_const(value));
                            }
                            return Ok(self.solver.int_const_bigint(&quotient));
                        }
                    }
                }
                self.assert_nonzero_divisor(r);
                if self.solver.get_sort(l) == Sort::Real {
                    self.solver.div(l, r)
                } else if let Some(divisor_literal) = self.term_int_literal_for_arithmetic(r) {
                    // Literal divisor: encode the quotient as a UF result and pin it
                    // with the EXACT linear Euclidean defining axiom (no native
                    // div/mod token, which the LRA bridge marks unsupported -> Unknown).
                    // (fix4-nia-div FIX 2)
                    let quotient = self.int_div_uf(l, r);
                    self.assert_int_div_linear_euclidean_axiom(l, &divisor_literal, quotient);
                    self.assert_int_div_ground_congruence(l, r, quotient);
                    quotient
                } else {
                    let quotient = self.int_div_uf(l, r);
                    self.assert_int_div_ground_congruence(l, r, quotient);
                    self.assert_int_div_euclidean_identity(l, r, quotient);
                    quotient
                }
            }
            BinOp::Mod => {
                let (l, r) = coerce_to_numeric(&mut self.solver, l, r, NumericOperandMode::IntOnly);
                if let (Some(dividend), Some(divisor)) = (
                    self.term_int_literal_for_arithmetic(l),
                    self.term_int_literal_for_arithmetic(r),
                ) {
                    if divisor > BigInt::from(0) {
                        let modulo = ((dividend % &divisor) + &divisor) % &divisor;
                        if let Some(value) = modulo.to_i64() {
                            return Ok(self.solver.int_const(value));
                        }
                    }
                }
                self.assert_nonzero_divisor(r);
                if self.term_is_nonzero_int_literal(r) {
                    self.solver.modulo(l, r)
                } else {
                    self.int_mod_uf(l, r)
                }
            }
            BinOp::DivTrunc => {
                // Rust's `/` on SIGNED MACHINE integers: TRUNCATED toward zero
                // (`-7 / 2 == -3`). Distinct from `BinOp::Div` (Euclidean), with
                // a SEPARATE quotient UF so the two can never share a term and
                // contradict each other's defining axioms.
                let (l, r) =
                    coerce_to_numeric(&mut self.solver, l, r, NumericOperandMode::IntOrReal);
                // Both-literal: `BigInt`'s `/` already truncates toward zero.
                if self.solver.get_sort(l) == Sort::Int {
                    if let (Some(dividend), Some(divisor)) = (
                        self.term_int_literal_for_arithmetic(l),
                        self.term_int_literal_for_arithmetic(r),
                    ) {
                        if divisor != BigInt::from(0) {
                            let quotient = &dividend / &divisor;
                            if let Some(value) = quotient.to_i64() {
                                return Ok(self.solver.int_const(value));
                            }
                            return Ok(self.solver.int_const_bigint(&quotient));
                        }
                    }
                }
                self.assert_nonzero_divisor(r);
                if self.solver.get_sort(l) == Sort::Real {
                    // Real division is exact; truncation only applies to integers.
                    self.solver.div(l, r)
                } else if let Some(divisor_literal) = self.term_int_literal_for_arithmetic(r) {
                    let quotient = self.int_div_uf_truncated(l, r);
                    self.assert_int_div_linear_truncated_axiom(l, &divisor_literal, quotient);
                    quotient
                } else {
                    let quotient = self.int_div_uf_truncated(l, r);
                    self.assert_int_div_truncated_identity(l, r, quotient);
                    self.assert_int_div_truncated_quotient_bounds(l, r, quotient);
                    quotient
                }
            }
            BinOp::RemTrunc => {
                // Rust's `%` on SIGNED MACHINE integers: the remainder TRUNCATES
                // toward zero and takes the SIGN OF THE DIVIDEND (`-1 % 5 == -1`).
                // Distinct from `BinOp::Mod` (Euclidean, non-negative).
                let (l, r) = coerce_to_numeric(&mut self.solver, l, r, NumericOperandMode::IntOnly);
                // Both-literal: `BigInt`'s `%` already truncates (sign of dividend).
                if let (Some(dividend), Some(divisor)) = (
                    self.term_int_literal_for_arithmetic(l),
                    self.term_int_literal_for_arithmetic(r),
                ) {
                    if divisor != BigInt::from(0) {
                        let modulo = &dividend % &divisor;
                        if let Some(value) = modulo.to_i64() {
                            return Ok(self.solver.int_const(value));
                        }
                        return Ok(self.solver.int_const_bigint(&modulo));
                    }
                }
                self.assert_nonzero_divisor(r);
                // Literal divisor: derive the exact truncated remainder `l - c*q`
                // from the truncated quotient (exact value + the div/mod identity,
                // sharing the truncated div UF). Symbolic divisor: bounded
                // truncated remainder UF.
                match self.term_int_literal_for_arithmetic(r) {
                    Some(divisor_literal) if divisor_literal != BigInt::from(0) => {
                        let quotient = self.int_div_uf_truncated(l, r);
                        self.assert_int_div_linear_truncated_axiom(l, &divisor_literal, quotient);
                        let c_q = self.solver.mul(r, quotient);
                        self.solver.sub(l, c_q)
                    }
                    _ => self.int_mod_uf_truncated(l, r),
                }
            }
            BinOp::Shl => {
                if self.arithmetic_mode.bitwise_proof_mode() {
                    self.encode_int_binop_bv(l, r, BitwiseBvOp::Shl)
                } else {
                    self.encode_int_binop_uf("__trust_wp_bit_shl", l, r)
                }
            }
            BinOp::Shr => {
                if self.arithmetic_mode.bitwise_proof_mode() {
                    self.encode_int_binop_bv(l, r, BitwiseBvOp::Shr)
                } else {
                    self.encode_int_binop_uf("__trust_wp_bit_shr", l, r)
                }
            }
            BinOp::BitAnd => {
                if self.arithmetic_mode.bitwise_proof_mode() {
                    self.encode_int_binop_bv_hinted(l, r, BitwiseBvOp::And, signed_narrow)
                } else {
                    self.encode_int_binop_uf("__trust_wp_bit_and", l, r)
                }
            }
            BinOp::BitXor => {
                if self.arithmetic_mode.bitwise_proof_mode() {
                    self.encode_int_binop_bv_hinted(l, r, BitwiseBvOp::Xor, signed_narrow)
                } else {
                    self.encode_int_binop_uf("__trust_wp_bit_xor", l, r)
                }
            }
            BinOp::BitOr => {
                if self.arithmetic_mode.bitwise_proof_mode() {
                    self.encode_int_binop_bv_hinted(l, r, BitwiseBvOp::Or, signed_narrow)
                } else {
                    self.encode_int_binop_uf("__trust_wp_bit_or", l, r)
                }
            }
            BinOp::Eq => {
                let resolved_sort = eq_sort.cloned().unwrap_or_else(|| {
                    let l_sort = self.solver.get_sort(l);
                    let r_sort = self.solver.get_sort(r);
                    super::select_structural_sort_target(&l_sort, &r_sort).unwrap_or_else(|| {
                        // AUDIT(#2663): GENUINE fallback — both operand sorts are
                        // known but `select_structural_sort_target` could not
                        // reconcile them. Bool→Int causes `eq` instead of `iff`,
                        // making equality unconstrained. This is a real unsoundness
                        // vector and correctly classified HIGH.
                        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToInt);
                        Sort::Int
                    })
                });
                self.eq_or_iff(l, r, &resolved_sort)
            }
            BinOp::Ne => {
                let resolved_sort = eq_sort.cloned().unwrap_or_else(|| {
                    let l_sort = self.solver.get_sort(l);
                    let r_sort = self.solver.get_sort(r);
                    super::select_structural_sort_target(&l_sort, &r_sort).unwrap_or_else(|| {
                        // AUDIT(#2663): GENUINE fallback — see BinOp::Eq comment.
                        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToInt);
                        Sort::Int
                    })
                });
                let eq = self.eq_or_iff(l, r, &resolved_sort);
                self.solver.not(eq)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (l, r) =
                    coerce_to_numeric(&mut self.solver, l, r, NumericOperandMode::IntOrReal);
                match op {
                    BinOp::Lt => self.solver.lt(l, r),
                    BinOp::Le => self.solver.le(l, r),
                    BinOp::Gt => self.solver.gt(l, r),
                    BinOp::Ge => self.solver.ge(l, r),
                    _ => unreachable!(),
                }
            }
            BinOp::And => {
                let (l, r) = self.coerce_bool_operands(l, r);
                self.solver.and(l, r)
            }
            BinOp::Or => {
                let (l, r) = self.coerce_bool_operands(l, r);
                self.solver.or(l, r)
            }
            // p ==> q is equivalent to !p || q
            BinOp::Implies => {
                let (l, r) = self.coerce_bool_operands(l, r);
                let not_l = self.solver.not(l);
                self.solver.or(not_l, r)
            }
            // BinOp is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns)]
            _ => {
                return Err(EncodingError::unsupported(format!(
                    "unknown BinOp variant: {op:?}"
                )))
            }
        })
    }

    /// Encode an operand in Bool context.
    ///
    /// Mapping-like lookups (`index`, `index_logic`, `lookup`) are value-polymorphic
    /// in source specs. When they appear in Bool contexts, keep the normal
    /// receiver-aware method encoding first, then coerce the resulting value into
    /// Bool. This preserves Mapping/FMap semantics for predicate lookups such as
    /// `self@[x]` instead of replacing them with a disconnected Bool UF. (#2316)
    pub(crate) fn encode_bool_context_operand(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Seed Bool hints at encode time as a safety net for call paths that
        // bypass verifier pre-scan registration. This prevents first use in a
        // Bool context from silently declaring Int-sorted placeholders. (#1608)
        self.seed_bool_context_hints(expr);
        match expr {
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let seq_like_lookup_key = args.first().is_some_and(|arg| {
                    let arg_sort = self.infer_encoded_sort(arg, prefix);
                    is_seq_family_sort(&arg_sort)
                });
                let seq_int_index_lookup = matches!(method.as_str(), "index" | "index_logic")
                    && args
                        .first()
                        .is_some_and(expr_is_known_int_key_for_bool_context)
                    && self.is_seq_receiver(receiver, prefix);
                let use_semantic_lookup = if method == "get" {
                    !self.is_seq_receiver(receiver, prefix) && !seq_like_lookup_key
                } else if matches!(method.as_str(), "index" | "index_logic" | "lookup") {
                    !seq_like_lookup_key
                        && (self.is_mapping_receiver(receiver, prefix)
                            || self.is_fmap_receiver(receiver, prefix))
                } else {
                    false
                };
                if use_semantic_lookup {
                    // Suppress the receiver-qualified Bool hint while encoding
                    // the lookup value to prevent nested lookups from being
                    // re-encoded as predicates (#2316, #2245).
                    let qualified_key = crate::encoder::sort_context::hint_collection::receiver_qualified_method_hint_key(receiver, method);
                    let saved_hint = self.sort_hint_cloned(&qualified_key);
                    if saved_hint == Some(ExprSort::Bool) {
                        self.remove_sort_hint(&qualified_key);
                    }
                    let value_term = self.encode_method_call_impl(receiver, method, args, prefix);
                    if let Some(hint) = saved_hint {
                        self.record_sort_hint(qualified_key, hint);
                    }
                    let value_term = value_term?;
                    Ok(self.coerce_bool_operand(value_term))
                } else if seq_int_index_lookup {
                    let qualified_key = crate::encoder::sort_context::hint_collection::receiver_qualified_method_hint_key(receiver, method);
                    let saved_hint = self.sort_hint_cloned(&qualified_key);
                    if saved_hint == Some(ExprSort::Bool) {
                        self.remove_sort_hint(&qualified_key);
                    }
                    let value_term = self.encode_method_call_impl(receiver, method, args, prefix);
                    if let Some(hint) = saved_hint {
                        self.record_sort_hint(qualified_key, hint);
                    }
                    Ok(self.coerce_bool_operand(value_term?))
                } else if matches!(method.as_str(), "get" | "index" | "index_logic" | "lookup") {
                    // Keep Seq-keyed predicate lookups on the Bool-UF path.
                    // `PredCell<[T]>` preconditions use shapes like `cell@[*s]`,
                    // where the key is a logical Seq rather than an Int.
                    // The current `mapping_get` encoding is monomorphic on
                    // `(Mapping, Int)`, so forcing semantic Mapping dispatch
                    // here reintroduces the original sort panic. (#1805, #2316)
                    self.encode_bool_method_predicate(receiver, method, args, prefix)
                } else {
                    self.encode_pure_impl(expr, prefix)
                }
            }
            _ => self.encode_pure_impl(expr, prefix),
        }
    }

    pub(super) fn seed_bool_context_hints(&mut self, expr: &PureExpr) {
        let mut bool_var_names = HashSet::new();
        let mut bool_fn_names = HashSet::new();
        collect_names_as_bool(expr, &mut bool_var_names, &mut bool_fn_names);
        collect_bool_hints(expr, &mut bool_var_names, &mut bool_fn_names);
        for name in bool_var_names {
            self.record_sort_hint(name, ExprSort::Bool);
        }
        for name in bool_fn_names {
            self.record_sort_hint(name, ExprSort::Bool);
        }
    }

    /// Coerce a single operand to Bool sort for logical operators.
    ///
    /// ay-dpll's `not`, `and`, `or` require Bool-sorted operands. When sort
    /// inference falls back to Int (the universal default for unresolved
    /// variables), logical operators panic with "sort mismatch: expected Bool,
    /// got Int". This converts Int-sorted terms to Bool via `!= 0`, which is
    /// semantically sound for the C/Rust convention where 0 is false.
    ///
    /// (#994: Bool/Int confusion in postconditions — `02_fib`, `such_that`)
    pub(crate) fn coerce_bool_operand(&mut self, term: Term) -> Term {
        let sort = self.solver.get_sort(term);
        if sort == Sort::Bool {
            return term;
        }
        unsoundness::increment(unsoundness::UnsoundnessCategory::BoolCoercionFromNonBool);
        if sort == Sort::Int {
            let zero = self.solver.int_const(0);
            self.solver.neq(term, zero)
        } else {
            // Non-Int, non-Bool sort (Seq, Uninterpreted, etc.): replace with
            // a fresh Bool constant to avoid cascading sort mismatch in neq.
            use std::sync::atomic::{AtomicU64, Ordering};
            static BOOL_COERCE_COUNTER: AtomicU64 = AtomicU64::new(0);
            let id = BOOL_COERCE_COUNTER.fetch_add(1, Ordering::Relaxed);
            self.solver
                .declare_const(&format!("__trust_wp_bool_coerce_{id}"), Sort::Bool)
        }
    }

    /// Coerce both operands to Bool for binary logical operators.
    pub(crate) fn coerce_bool_operands(&mut self, l: Term, r: Term) -> (Term, Term) {
        (self.coerce_bool_operand(l), self.coerce_bool_operand(r))
    }

    /// Encode integer-valued operators with an uninterpreted-function fallback.
    ///
    /// Bitwise operators are approximated as uninterpreted functions with basic
    /// identity axioms until native bitvector modeling is introduced. The axioms
    /// make the approximation sound for common patterns (identity, idempotence,
    /// self-inverse) but bitwise reasoning beyond these axioms may produce
    /// `Unknown` or false confidence. (#1814)
    fn encode_int_binop_uf(&mut self, name: &str, left: Term, right: Term) -> Term {
        let (left, right) =
            coerce_to_numeric(&mut self.solver, left, right, NumericOperandMode::IntOnly);
        unsoundness::increment(unsoundness::UnsoundnessCategory::BitwiseUfApproximation);
        let decl = if let Some(decl) = self.spec_func_decl_cloned(name) {
            decl
        } else {
            let decl = self
                .solver
                .declare_fun(name, &[Sort::Int, Sort::Int], Sort::Int);
            self.register_spec_func(name.to_string(), decl.clone());
            // Assert quantified axioms only when the selected solver logic
            // supports quantifiers. QF modes get ground instances per UF
            // application below, avoiding Unknown on satisfiable UF queries.
            if self.supports_quantifiers() {
                self.assert_bitwise_axioms(name, &decl);
            }
            // Emit a once-per-operator warning so users get a direct diagnostic
            // through tracing. (#1814 AC-1)
            let warning = Self::bitwise_uf_warning(name);
            debug!("{warning}");
            tracing::warn!(op = name, "{warning}");
            decl
        };
        let result = self.solver.apply(&decl, &[left, right]);
        self.assert_bitwise_ground_axioms(name, &decl, left, right, result);
        result
    }

    /// Encode a bitwise operation using ay's native BV theory (#2666).
    ///
    /// This is the default encoding path for bitwise operations. Int-sorted
    /// operands are converted to bitvectors via `int2bv`, the BV operation is
    /// applied, and the result is converted back to Int via `bv2int`. This gives
    /// exact bit-level semantics instead of the legacy UF approximation.
    ///
    /// The BV width is determined by the operand sort: if either operand is
    /// already a BV term, its width is used; otherwise [`DEFAULT_BV_WIDTH`] (64)
    /// is used.
    fn encode_int_binop_bv(&mut self, left: Term, right: Term, op: BitwiseBvOp) -> Term {
        self.encode_int_binop_bv_hinted(left, right, op, None)
    }

    /// [`Self::encode_int_binop_bv`] with an optional SIGNED source-type
    /// width hint (#route-100 rightmostbit latent false-reject).
    ///
    /// Without the hint, an `i8` operation like `x & y` is encoded at width
    /// 64 with an UNSIGNED `bv2int` wrap-back: for negative operands the
    /// 64-bit patterns are sign-extensions (bitwise-correct), but the
    /// unsigned conversion returns e.g. `2^64 - 128` where the source value
    /// is `-128` — a latent FALSE-REJECT on signed types (decoded in the
    /// rightmostbit replays). With `signed_narrow = Some(W)` — derived by
    /// [`Self::signed_narrow_bitwise_hint`] ONLY when BOTH operands are
    /// pinned into the signed W-window by asserted premises — the operation
    /// is encoded exactly at width W: `int2bv(W)` of an in-window value is
    /// its two's-complement pattern, the BV op is the bitwise op on those
    /// patterns, and the SIGNED conversion returns the exact result (which
    /// is in-window again for `&`/`|`/`^`). This is exact in every model
    /// where the hint-source premises hold, and those premises are asserted
    /// in the same VC — so the refinement can never manufacture a wrong
    /// verdict.
    fn encode_int_binop_bv_hinted(
        &mut self,
        left: Term,
        right: Term,
        op: BitwiseBvOp,
        signed_narrow: Option<u32>,
    ) -> Term {
        let (left, right) =
            coerce_to_numeric(&mut self.solver, left, right, NumericOperandMode::IntOnly);

        // Exact signed-width path: only for &, |, ^ (shifts have separate
        // width semantics) and only when both operands are Int-sorted.
        if let Some(w) = signed_narrow {
            if matches!(op, BitwiseBvOp::And | BitwiseBvOp::Or | BitwiseBvOp::Xor)
                && self.solver.get_sort(left) == Sort::Int
                && self.solver.get_sort(right) == Sort::Int
            {
                if let (Ok(bv_l), Ok(bv_r)) = (
                    self.solver.try_int2bv(left, w),
                    self.solver.try_int2bv(right, w),
                ) {
                    let bv_result = match op {
                        BitwiseBvOp::And => self.solver.bvand(bv_l, bv_r),
                        BitwiseBvOp::Or => self.solver.bvor(bv_l, bv_r),
                        _ => self.solver.bvxor(bv_l, bv_r),
                    };
                    return self.solver.bv2int_signed(bv_result);
                }
            }
        }

        // Determine the BV width from operand sorts, or use the default.
        let width = match self.solver.get_sort(left) {
            Sort::BitVec(bv) => bv.width,
            _ => match self.solver.get_sort(right) {
                Sort::BitVec(bv) => bv.width,
                _ => DEFAULT_BV_WIDTH,
            },
        };

        // Convert Int operands to BV. If already BV-sorted, these are no-ops
        // at the sort level (int2bv panics on non-Int, so guard).
        let bv_left = if self.solver.get_sort(left) == Sort::Int {
            self.solver.try_int2bv(left, width).unwrap_or_else(|_| left)
        } else {
            left
        };
        let bv_right = if self.solver.get_sort(right) == Sort::Int {
            self.solver
                .try_int2bv(right, width)
                .unwrap_or_else(|_| right)
        } else {
            right
        };

        // Apply the native BV operation.
        let bv_result = match op {
            BitwiseBvOp::And => self.solver.bvand(bv_left, bv_right),
            BitwiseBvOp::Or => self.solver.bvor(bv_left, bv_right),
            BitwiseBvOp::Xor => self.solver.bvxor(bv_left, bv_right),
            BitwiseBvOp::Shl => self.solver.bvshl(bv_left, bv_right),
            BitwiseBvOp::Shr => self.solver.bvlshr(bv_left, bv_right),
        };

        // Convert the BV result back to Int for the rest of the encoding.
        self.solver.bv2int(bv_result)
    }

    /// Encode a machine-integer bit operation AT ITS TYPE: `bits` wide, with
    /// the type's signedness (the `__trust_wp_int_bitop_*` marker, D-242).
    ///
    /// Each Int operand (an in-range value of the type) is taken to its
    /// `bits`-wide two's-complement pattern with `int2bv`, the operation is
    /// the BV operation on those patterns, and the pattern is read back
    /// signed or unsigned. That is the Rust operation exactly: `<<` keeps the
    /// low `bits` bits (`200u8 << 1 == 144`), `!` complements within the type,
    /// `&`/`|`/`^` of `u128` operands keep their high half, a signed result is
    /// its two's-complement value, and a signed `>>` is ARITHMETIC (`bvashr`).
    /// The shift amount is the `bits`-wide pattern of its value, exact for
    /// every amount the shift's range obligation admits (`0 <= s < bits`).
    /// `right` is `None` for `!`.
    pub(crate) fn encode_int_bitop_at_type(
        &mut self,
        op: MachineBitOp,
        left: Term,
        right: Option<Term>,
        bits: u32,
        signed: bool,
    ) -> Result<Term, EncodingError> {
        let pattern = |encoder: &mut Self, term: Term| -> Result<Term, EncodingError> {
            let term = match encoder.solver.get_sort(term) {
                // A BV-sorted operand carries its unsigned value.
                Sort::BitVec(_) => encoder.solver.bv2int(term),
                Sort::Int => term,
                _ => {
                    let zero = encoder.solver.int_const(0);
                    coerce_to_numeric(&mut encoder.solver, term, zero, NumericOperandMode::IntOnly)
                        .0
                }
            };
            encoder.solver.try_int2bv(term, bits).map_err(|error| {
                EncodingError::unsupported(format!(
                    "machine bit operation at {bits} bits: operand not convertible: {error}"
                ))
            })
        };
        let l = pattern(self, left)?;
        let result = match (op, right) {
            (MachineBitOp::And, Some(r)) => {
                let r = pattern(self, r)?;
                self.solver.bvand(l, r)
            }
            (MachineBitOp::Or, Some(r)) => {
                let r = pattern(self, r)?;
                self.solver.bvor(l, r)
            }
            (MachineBitOp::Xor, Some(r)) => {
                let r = pattern(self, r)?;
                self.solver.bvxor(l, r)
            }
            (MachineBitOp::Shl, Some(r)) => {
                let r = pattern(self, r)?;
                self.solver.bvshl(l, r)
            }
            (MachineBitOp::Shr, Some(r)) => {
                let r = pattern(self, r)?;
                if signed {
                    self.solver.bvashr(l, r)
                } else {
                    self.solver.bvlshr(l, r)
                }
            }
            (MachineBitOp::Not, None) => self.solver.bvnot(l),
            _ => {
                return Err(EncodingError::unsupported(
                    "machine bit operation marker with the wrong operand count",
                ))
            }
        };
        Ok(if signed {
            self.solver.bv2int_signed(result)
        } else {
            self.solver.bv2int(result)
        })
    }

    /// Encode a machine `value >> shift` by a literal `0 <= shift < bits`
    /// (D-242). Its Rust value is `floor(value / 2^shift)` for either
    /// signedness (an arithmetic shift is the floor).
    ///
    /// * Up to 64 bits it is the Euclidean quotient by the positive literal
    ///   `2^shift`, a linear definition shared with a clause's machine `>>`
    ///   by a literal (D-232 reads it as that quotient), plus the lemma that
    ///   a quotient of a value in the type lies in the shifted range
    ///   (monotonicity of the floor; it holds wherever the definition does,
    ///   and is guarded by the active path as the definition is).
    /// * Above 64 bits the type's bounds reach `2^128`, and a proof through
    ///   them (`2^64 * q <= x <= 2^128 - 1`, so `q <= 2^64 - 1`) is beyond
    ///   what the strict certificate admits. The shift is then the
    ///   bit-vector shift at the type, whose result range is a THEOREM of
    ///   the encoding (a logical shift of a 128-bit pattern by `k` is below
    ///   `2^(128-k)`; an arithmetic one lies in `[-2^(127-k), 2^(127-k))`),
    ///   asserted without premise.
    pub(crate) fn encode_machine_shr_by_literal(
        &mut self,
        value: Term,
        bits: u32,
        signed: bool,
        shift: u32,
    ) -> Result<Term, EncodingError> {
        let one = BigInt::from(1u8);
        let (min, max) = if signed {
            let half = &one << (bits - 1);
            (-half.clone(), half - &one)
        } else {
            (BigInt::from(0u8), (&one << bits) - &one)
        };
        let divisor = &one << shift;
        let range_lo = euclidean_div_bigint(&min, &divisor);
        let range_hi = euclidean_div_bigint(&max, &divisor);
        let in_quantifier = self.quantifier_state.quantifier_depth() != 0;
        if bits <= 64 {
            let divisor = self.solver.int_const_bigint(&divisor);
            let quotient = self.encode_binop(value, BinOp::Div, divisor, None)?;
            if !in_quantifier && self.solver.get_sort(quotient) == Sort::Int {
                let min = self.solver.int_const_bigint(&min);
                let max = self.solver.int_const_bigint(&max);
                let ge_min = self.solver.ge(value, min);
                let le_max = self.solver.le(value, max);
                let in_type = self.solver.and(ge_min, le_max);
                let lo = self.solver.int_const_bigint(&range_lo);
                let hi = self.solver.int_const_bigint(&range_hi);
                let ge_lo = self.solver.ge(quotient, lo);
                let le_hi = self.solver.le(quotient, hi);
                let in_range = self.solver.and(ge_lo, le_hi);
                let lemma = self.solver.implies(in_type, in_range);
                let guarded = self.guard_with_active_path(lemma);
                self.assert_solver_term("machine_shr/quotient_range", guarded);
            }
            return Ok(quotient);
        }
        let amount = self.solver.int_const(i64::from(shift));
        let result =
            self.encode_int_bitop_at_type(MachineBitOp::Shr, value, Some(amount), bits, signed)?;
        if !in_quantifier {
            let lo = self.solver.int_const_bigint(&range_lo);
            let hi = self.solver.int_const_bigint(&range_hi);
            let ge_lo = self.solver.ge(result, lo);
            let le_hi = self.solver.le(result, hi);
            let in_range = self.solver.and(ge_lo, le_hi);
            self.assert_solver_term("machine_shr/pattern_range", in_range);
        }
        Ok(result)
    }

    /// Encode an integer narrowing cast using BV truncation (#2666, #938).
    ///
    /// Models Rust's `value as target_type` when `target_type` is narrower than
    /// the source. The semantics are:
    /// 1. Convert the Int value to BV of source width (or 64 if unknown)
    /// 2. Extract the lower `target_bits` via BV extract
    /// 3. Convert back to Int via `bv2int`
    ///
    /// For unsigned targets, this gives `value % 2^target_bits` (modular truncation).
    /// For signed targets, the BV→Int conversion interprets the result as signed
    /// (two's complement) — i.e., if the high bit of the target width is set, the
    /// result is negative.
    ///
    /// # Arguments
    /// - `value`: the Int-sorted term to truncate
    /// - `target_bits`: the bit width of the target type (8, 16, 32, 64)
    /// - `signed`: whether the target type is signed (for signed BV→Int conversion)
    ///
    /// # Returns
    /// An Int-sorted term representing the truncated value.
    pub(crate) fn encode_int_truncation_bv(
        &mut self,
        value: Term,
        target_bits: u32,
        signed: bool,
    ) -> Term {
        // Coerce to Int if not already (safety net for non-Int inputs).
        let int_value = if self.solver.get_sort(value) != Sort::Int {
            let zero = self.solver.int_const(0);
            let (v, _) =
                coerce_to_numeric(&mut self.solver, value, zero, NumericOperandMode::IntOnly);
            v
        } else {
            value
        };

        // Step 1: Convert Int → BV of sufficient width for the source.
        // We use the maximum of target_bits and DEFAULT_BV_WIDTH to ensure
        // no information is lost before truncation.
        let source_width = DEFAULT_BV_WIDTH.max(target_bits);
        let bv_value = self
            .solver
            .try_int2bv(int_value, source_width)
            .unwrap_or_else(|_| {
                // Fallback: if int2bv fails, return the original value unchanged.
                // This preserves the identity-cast behavior as a safe degradation.
                return int_value;
            });

        // If int2bv failed (fallback returned Int), skip BV extract.
        if self.solver.get_sort(bv_value) == Sort::Int {
            return int_value;
        }

        // Step 2: Extract lower target_bits via BV extract (bits [target_bits-1:0]).
        let truncated = if target_bits < source_width {
            self.solver.bvextract(bv_value, target_bits - 1, 0)
        } else {
            // No truncation needed — target width >= source width.
            bv_value
        };

        // Step 3: Convert back to Int. For signed targets, use signed BV→Int
        // conversion so negative values are preserved.
        let result = if signed {
            self.solver.bv2int_signed(truncated)
        } else {
            self.solver.bv2int(truncated)
        };
        self.assert_int_truncation_identity_when_in_range(int_value, result, target_bits, signed);
        result
    }

    fn assert_int_truncation_identity_when_in_range(
        &mut self,
        value: Term,
        truncated: Term,
        target_bits: u32,
        signed: bool,
    ) {
        if self.quantifier_state.quantifier_depth() != 0
            || target_bits == 0
            || self.solver.get_sort(value) != Sort::Int
            || self.solver.get_sort(truncated) != Sort::Int
        {
            return;
        }

        let (lower, upper) = if signed {
            let sign_bit = BigInt::from(1u8) << (target_bits - 1);
            (-sign_bit.clone(), sign_bit - BigInt::from(1u8))
        } else {
            (
                BigInt::from(0u8),
                (BigInt::from(1u8) << target_bits) - BigInt::from(1u8),
            )
        };
        let lower_term = self.solver.int_const_bigint(&lower);
        let upper_term = self.solver.int_const_bigint(&upper);
        let ge_lower = self.solver.ge(value, lower_term);
        let le_upper = self.solver.le(value, upper_term);
        let in_range = self.solver.and(ge_lower, le_upper);
        let identity = self.eq_term(truncated, value);
        let implication = self.solver.implies(in_range, identity);
        self.assert_solver_term("int_truncation/identity_in_range", implication);
    }

    /// Encode same-width unsigned-to-signed integer casts without BV terms.
    ///
    /// For an N-bit unsigned source reinterpreted as an N-bit signed target,
    /// Rust keeps values in the signed positive range unchanged and subtracts
    /// 2^N for values with the sign bit set. The driver only emits this form
    /// when source and target widths match, e.g. `usize as isize`.
    pub(crate) fn encode_unsigned_to_signed_same_width(&mut self, value: Term, bits: u32) -> Term {
        if bits == 0 {
            return value;
        }

        let max_signed = (BigInt::from(1u8) << (bits - 1)) - BigInt::from(1u8);
        let modulus = BigInt::from(1u8) << bits;
        let max_signed_term = self.solver.int_const_bigint(&max_signed);
        let modulus_term = self.solver.int_const_bigint(&modulus);
        let in_positive_range = self.solver.le(value, max_signed_term);
        let wraps_signed = self.solver.gt(value, max_signed_term);
        let wrapped = self.solver.sub(value, modulus_term);

        let name = format!("__trust_wp_int_cast_u{bits}_to_s{bits}");
        let decl = self.solver.declare_fun(&name, &[Sort::Int], Sort::Int);
        let casted = self.solver.apply(&decl, &[value]);
        let positive_equality = self.solver.eq(casted, value);
        let positive_definition = self.solver.implies(in_positive_range, positive_equality);
        self.assert_solver_term(
            "same_width_unsigned_to_signed_cast/positive",
            positive_definition,
        );
        let wrapped_equality = self.solver.eq(casted, wrapped);
        let wrapped_definition = self.solver.implies(wraps_signed, wrapped_equality);
        self.assert_solver_term(
            "same_width_unsigned_to_signed_cast/wrapped",
            wrapped_definition,
        );
        casted
    }

    fn bitwise_uf_warning(name: &str) -> String {
        let op = name.trim_start_matches("__trust_wp_bit_");
        format!(
            "trust-wp: warning: bitwise operator `{op}` is approximated as an \
             uninterpreted function with partial axioms; verification may be \
             incomplete (#1814)"
        )
    }

    /// Assert identity, commutativity, non-negativity, and bound axioms for
    /// bitwise UFs (#1814, #2666).
    ///
    /// These axioms provide sound (but incomplete) semantics for bitwise operations
    /// encoded as UFs. Each axiom is universally quantified with a trigger on the
    /// UF application to enable E-matching.
    ///
    /// Axioms per operator:
    /// - BitAnd: `x & 0 = 0`, `x & x = x`, `x & y = y & x`,
    ///           `x >= 0 /\ y >= 0 => x & y >= 0`,
    ///           `x >= 0 /\ y >= 0 => x & y <= x`,
    ///           `x >= 0 /\ y >= 0 => x & y <= y`
    /// - BitOr: `x | 0 = x`, `x | x = x`, `x | y = y | x`,
    ///          `x >= 0 /\ y >= 0 => x | y >= x`,
    ///          `x >= 0 /\ y >= 0 => x | y >= y`,
    ///          `x >= 0 /\ y >= 0 => x | y >= 0`
    /// - BitXor: `x ^ 0 = x`, `x ^ x = 0`, `x ^ y = y ^ x`,
    ///           `x >= 0 /\ y >= 0 => x ^ y >= 0`
    /// - Shl: `x << 0 = x`, `x >= 0 /\ y >= 0 => x << y >= 0`,
    ///        `x >= 0 /\ y >= 0 => x << y >= x`
    /// - Shr: `x >> 0 = x`, `x >= 0 /\ y >= 0 => x >> y >= 0`,
    ///        `x >= 0 /\ y >= 0 => x >> y <= x`
    fn assert_bitwise_axioms(&mut self, name: &str, decl: &ay_dpll::api::FuncDecl) {
        let x = self.solver.fresh_var("bw_x", Sort::Int);
        let zero = self.solver.int_const(0);

        // f(x, 0) — used as trigger and in axiom bodies
        let fx0 = self.solver.apply(decl, &[x, zero]);
        // f(x, x) — used as trigger and in axiom bodies
        let fxx = self.solver.apply(decl, &[x, x]);

        match name {
            "__trust_wp_bit_and" => {
                // x & 0 = 0
                let eq_zero = self.eq_term(fx0, zero);
                let axiom = self.solver.forall_with_triggers(&[x], eq_zero, &[&[fx0]]);
                self.assert_solver_term("bitwise_axiom/and_zero", axiom);
                // x & x = x
                let eq_self = self.eq_term(fxx, x);
                let axiom = self.solver.forall_with_triggers(&[x], eq_self, &[&[fxx]]);
                self.assert_solver_term("bitwise_axiom/and_idem", axiom);
                // x & y = y & x (commutativity)
                self.assert_bitwise_commutativity(name, decl);
                // Bound axioms for non-negative inputs (#2666):
                // x >= 0 /\ y >= 0 => x & y >= 0
                // x >= 0 /\ y >= 0 => x & y <= x
                // x >= 0 /\ y >= 0 => x & y <= y
                self.assert_bitwise_nonneg_bounds(name, decl, BitwiseBoundKind::AndBounds);
            }
            "__trust_wp_bit_or" => {
                // x | 0 = x
                let eq_x = self.eq_term(fx0, x);
                let axiom = self.solver.forall_with_triggers(&[x], eq_x, &[&[fx0]]);
                self.assert_solver_term("bitwise_axiom/or_identity", axiom);
                // x | x = x
                let eq_self = self.eq_term(fxx, x);
                let axiom = self.solver.forall_with_triggers(&[x], eq_self, &[&[fxx]]);
                self.assert_solver_term("bitwise_axiom/or_idem", axiom);
                // x | y = y | x (commutativity)
                self.assert_bitwise_commutativity(name, decl);
                // Bound axioms for non-negative inputs (#2666):
                // x >= 0 /\ y >= 0 => x | y >= x
                // x >= 0 /\ y >= 0 => x | y >= y
                // x >= 0 /\ y >= 0 => x | y >= 0
                self.assert_bitwise_nonneg_bounds(name, decl, BitwiseBoundKind::OrBounds);
            }
            "__trust_wp_bit_xor" => {
                // x ^ 0 = x
                let eq_x = self.eq_term(fx0, x);
                let axiom = self.solver.forall_with_triggers(&[x], eq_x, &[&[fx0]]);
                self.assert_solver_term("bitwise_axiom/xor_identity", axiom);
                // x ^ x = 0
                let eq_zero = self.eq_term(fxx, zero);
                let axiom = self.solver.forall_with_triggers(&[x], eq_zero, &[&[fxx]]);
                self.assert_solver_term("bitwise_axiom/xor_self", axiom);
                // x ^ y = y ^ x (commutativity)
                self.assert_bitwise_commutativity(name, decl);
                // Non-negativity for non-negative inputs (#2666):
                // x >= 0 /\ y >= 0 => x ^ y >= 0
                self.assert_bitwise_nonneg_bounds(name, decl, BitwiseBoundKind::NonNegOnly);
            }
            "__trust_wp_bit_shl" => {
                // x << 0 = x
                let eq_x = self.eq_term(fx0, x);
                let axiom = self.solver.forall_with_triggers(&[x], eq_x, &[&[fx0]]);
                self.assert_solver_term("bitwise_axiom/shift_identity", axiom);
                // Bound axioms for non-negative inputs (#2666):
                // x >= 0 /\ y >= 0 => x << y >= x
                // x >= 0 /\ y >= 0 => x << y >= 0
                self.assert_bitwise_nonneg_bounds(name, decl, BitwiseBoundKind::ShlBounds);
            }
            "__trust_wp_bit_shr" => {
                // x >> 0 = x
                let eq_x = self.eq_term(fx0, x);
                let axiom = self.solver.forall_with_triggers(&[x], eq_x, &[&[fx0]]);
                self.assert_solver_term("bitwise_axiom/shift_identity", axiom);
                // Bound axioms for non-negative inputs (#2666):
                // x >= 0 /\ y >= 0 => x >> y <= x
                // x >= 0 /\ y >= 0 => x >> y >= 0
                self.assert_bitwise_nonneg_bounds(name, decl, BitwiseBoundKind::ShrBounds);
            }
            _ => {}
        }
    }

    fn assert_bitwise_ground_axioms(
        &mut self,
        name: &str,
        decl: &ay_dpll::api::FuncDecl,
        left: Term,
        right: Term,
        result: Term,
    ) {
        let zero = self.solver.int_const(0);
        let right_is_zero = self.eq_term(right, zero);
        let left_is_zero = self.eq_term(left, zero);
        let args_equal = self.eq_term(left, right);

        match name {
            "__trust_wp_bit_and" => {
                let result_is_zero = self.eq_term(result, zero);
                let right_zero = self.solver.implies(right_is_zero, result_is_zero);
                self.assert_solver_term("bitwise_ground/and_zero_rhs", right_zero);

                let result_is_zero = self.eq_term(result, zero);
                let left_zero = self.solver.implies(left_is_zero, result_is_zero);
                self.assert_solver_term("bitwise_ground/and_zero_lhs", left_zero);

                let result_is_left = self.eq_term(result, left);
                let idem = self.solver.implies(args_equal, result_is_left);
                self.assert_solver_term("bitwise_ground/and_idem", idem);

                self.assert_bitwise_ground_commutativity(name, decl, left, right, result);
                self.assert_bitwise_ground_nonneg_bounds(
                    name,
                    left,
                    right,
                    result,
                    BitwiseBoundKind::AndBounds,
                );
            }
            "__trust_wp_bit_or" => {
                let result_is_left = self.eq_term(result, left);
                let right_zero = self.solver.implies(right_is_zero, result_is_left);
                self.assert_solver_term("bitwise_ground/or_zero_rhs", right_zero);

                let result_is_right = self.eq_term(result, right);
                let left_zero = self.solver.implies(left_is_zero, result_is_right);
                self.assert_solver_term("bitwise_ground/or_zero_lhs", left_zero);

                let result_is_left = self.eq_term(result, left);
                let idem = self.solver.implies(args_equal, result_is_left);
                self.assert_solver_term("bitwise_ground/or_idem", idem);

                self.assert_bitwise_ground_commutativity(name, decl, left, right, result);
                self.assert_bitwise_ground_nonneg_bounds(
                    name,
                    left,
                    right,
                    result,
                    BitwiseBoundKind::OrBounds,
                );
            }
            "__trust_wp_bit_xor" => {
                let result_is_left = self.eq_term(result, left);
                let right_zero = self.solver.implies(right_is_zero, result_is_left);
                self.assert_solver_term("bitwise_ground/xor_zero_rhs", right_zero);

                let result_is_right = self.eq_term(result, right);
                let left_zero = self.solver.implies(left_is_zero, result_is_right);
                self.assert_solver_term("bitwise_ground/xor_zero_lhs", left_zero);

                let result_is_zero = self.eq_term(result, zero);
                let self_inverse = self.solver.implies(args_equal, result_is_zero);
                self.assert_solver_term("bitwise_ground/xor_self", self_inverse);

                self.assert_bitwise_ground_commutativity(name, decl, left, right, result);
                self.assert_bitwise_ground_nonneg_bounds(
                    name,
                    left,
                    right,
                    result,
                    BitwiseBoundKind::NonNegOnly,
                );
            }
            "__trust_wp_bit_shl" => {
                let result_is_left = self.eq_term(result, left);
                let right_zero = self.solver.implies(right_is_zero, result_is_left);
                self.assert_solver_term("bitwise_ground/shl_zero_rhs", right_zero);
                self.assert_bitwise_ground_nonneg_bounds(
                    name,
                    left,
                    right,
                    result,
                    BitwiseBoundKind::ShlBounds,
                );
            }
            "__trust_wp_bit_shr" => {
                let result_is_left = self.eq_term(result, left);
                let right_zero = self.solver.implies(right_is_zero, result_is_left);
                self.assert_solver_term("bitwise_ground/shr_zero_rhs", right_zero);
                self.assert_bitwise_ground_nonneg_bounds(
                    name,
                    left,
                    right,
                    result,
                    BitwiseBoundKind::ShrBounds,
                );
            }
            _ => {}
        }
    }

    fn assert_bitwise_ground_commutativity(
        &mut self,
        name: &str,
        decl: &ay_dpll::api::FuncDecl,
        left: Term,
        right: Term,
        result: Term,
    ) {
        let swapped = self.solver.apply(decl, &[right, left]);
        let eq = self.eq_term(result, swapped);
        let label = format!(
            "bitwise_ground/{}_commutative",
            name.trim_start_matches("__trust_wp_bit_")
        );
        self.assert_solver_term(&label, eq);
    }

    fn assert_bitwise_ground_nonneg_bounds(
        &mut self,
        name: &str,
        left: Term,
        right: Term,
        result: Term,
        kind: BitwiseBoundKind,
    ) {
        let zero = self.solver.int_const(0);
        let left_nonneg = self.solver.ge(left, zero);
        let right_nonneg = self.solver.ge(right, zero);
        let premise = self.solver.and(left_nonneg, right_nonneg);
        let op_name = name.trim_start_matches("__trust_wp_bit_");

        let result_nonneg = self.solver.ge(result, zero);
        let implication = self.solver.implies(premise, result_nonneg);
        self.assert_solver_term(&format!("bitwise_ground/{op_name}_nonneg"), implication);

        match kind {
            BitwiseBoundKind::AndBounds => {
                let le_left = self.solver.le(result, left);
                let implication = self.solver.implies(premise, le_left);
                self.assert_solver_term(&format!("bitwise_ground/{op_name}_le_left"), implication);

                let le_right = self.solver.le(result, right);
                let implication = self.solver.implies(premise, le_right);
                self.assert_solver_term(&format!("bitwise_ground/{op_name}_le_right"), implication);
            }
            BitwiseBoundKind::OrBounds => {
                let ge_left = self.solver.ge(result, left);
                let implication = self.solver.implies(premise, ge_left);
                self.assert_solver_term(&format!("bitwise_ground/{op_name}_ge_left"), implication);

                let ge_right = self.solver.ge(result, right);
                let implication = self.solver.implies(premise, ge_right);
                self.assert_solver_term(&format!("bitwise_ground/{op_name}_ge_right"), implication);
            }
            BitwiseBoundKind::ShlBounds => {
                let ge_left = self.solver.ge(result, left);
                let implication = self.solver.implies(premise, ge_left);
                self.assert_solver_term(&format!("bitwise_ground/{op_name}_ge_left"), implication);
            }
            BitwiseBoundKind::ShrBounds => {
                let le_left = self.solver.le(result, left);
                let implication = self.solver.implies(premise, le_left);
                self.assert_solver_term(&format!("bitwise_ground/{op_name}_le_left"), implication);
            }
            BitwiseBoundKind::NonNegOnly => {}
        }
    }

    /// Assert commutativity axiom: `forall x y. f(x, y) = f(y, x)`.
    ///
    /// Triggered on `f(x, y)` so E-matching fires when the UF is applied.
    /// Only valid for commutative bitwise operators (AND, OR, XOR). (#1814)
    fn assert_bitwise_commutativity(&mut self, name: &str, decl: &ay_dpll::api::FuncDecl) {
        let x = self.solver.fresh_var("bw_comm_x", Sort::Int);
        let y = self.solver.fresh_var("bw_comm_y", Sort::Int);
        let fxy = self.solver.apply(decl, &[x, y]);
        let fyx = self.solver.apply(decl, &[y, x]);
        let eq = self.eq_term(fxy, fyx);
        let axiom = self.solver.forall_with_triggers(&[x, y], eq, &[&[fxy]]);
        let label = format!(
            "bitwise_axiom/{}_commutative",
            name.trim_start_matches("__trust_wp_bit_")
        );
        self.assert_solver_term(&label, axiom);
    }

    /// Assert non-negativity and bound axioms for a bitwise UF (#2666).
    ///
    /// All bitwise operations preserve non-negativity for unsigned (non-negative)
    /// integer inputs. These axioms are sound for `x >= 0, y >= 0` and help the
    /// UF approximation prove common patterns involving unsigned integer bitwise
    /// operations without needing full BV theory.
    ///
    /// The premise `x >= 0 /\ y >= 0` is guarded via implication so the axioms
    /// do not constrain behavior for negative (signed) inputs, where the UF
    /// abstraction is intentionally loose.
    fn assert_bitwise_nonneg_bounds(
        &mut self,
        name: &str,
        decl: &ay_dpll::api::FuncDecl,
        kind: BitwiseBoundKind,
    ) {
        let x = self.solver.fresh_var("bw_bound_x", Sort::Int);
        let y = self.solver.fresh_var("bw_bound_y", Sort::Int);
        let zero = self.solver.int_const(0);
        let fxy = self.solver.apply(decl, &[x, y]);

        // Premise: x >= 0 /\ y >= 0
        let x_nonneg = self.solver.ge(x, zero);
        let y_nonneg = self.solver.ge(y, zero);
        let premise = self.solver.and(x_nonneg, y_nonneg);

        let op_name = name.trim_start_matches("__trust_wp_bit_");

        // All kinds get non-negativity: premise => f(x, y) >= 0
        let result_nonneg = self.solver.ge(fxy, zero);
        let nonneg_implication = self.solver.implies(premise, result_nonneg);
        let axiom = self
            .solver
            .forall_with_triggers(&[x, y], nonneg_implication, &[&[fxy]]);
        self.assert_solver_term(&format!("bitwise_axiom/{op_name}_nonneg"), axiom);

        // Additional bound axioms per kind.
        match kind {
            BitwiseBoundKind::AndBounds => {
                // x & y <= x (AND can only clear bits)
                let le_x = self.solver.le(fxy, x);
                let impl_le_x = self.solver.implies(premise, le_x);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x, y], impl_le_x, &[&[fxy]]);
                self.assert_solver_term(&format!("bitwise_axiom/{op_name}_le_x"), axiom);
                // x & y <= y
                let le_y = self.solver.le(fxy, y);
                let impl_le_y = self.solver.implies(premise, le_y);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x, y], impl_le_y, &[&[fxy]]);
                self.assert_solver_term(&format!("bitwise_axiom/{op_name}_le_y"), axiom);
            }
            BitwiseBoundKind::OrBounds => {
                // x | y >= x (OR can only set bits)
                let ge_x = self.solver.ge(fxy, x);
                let impl_ge_x = self.solver.implies(premise, ge_x);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x, y], impl_ge_x, &[&[fxy]]);
                self.assert_solver_term(&format!("bitwise_axiom/{op_name}_ge_x"), axiom);
                // x | y >= y
                let ge_y = self.solver.ge(fxy, y);
                let impl_ge_y = self.solver.implies(premise, ge_y);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x, y], impl_ge_y, &[&[fxy]]);
                self.assert_solver_term(&format!("bitwise_axiom/{op_name}_ge_y"), axiom);
            }
            BitwiseBoundKind::NonNegOnly => {
                // Non-negativity axiom already asserted above — nothing extra.
            }
            BitwiseBoundKind::ShlBounds => {
                // x << y >= x (left shift grows the value for non-negative x, y)
                let ge_x = self.solver.ge(fxy, x);
                let impl_ge_x = self.solver.implies(premise, ge_x);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x, y], impl_ge_x, &[&[fxy]]);
                self.assert_solver_term(&format!("bitwise_axiom/{op_name}_ge_x"), axiom);
            }
            BitwiseBoundKind::ShrBounds => {
                // x >> y <= x (right shift shrinks the value for non-negative x, y)
                let le_x = self.solver.le(fxy, x);
                let impl_le_x = self.solver.implies(premise, le_x);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x, y], impl_le_x, &[&[fxy]]);
                self.assert_solver_term(&format!("bitwise_axiom/{op_name}_le_x"), axiom);
            }
        }
    }

    /// Collect division/modulo proof obligation: divisor != 0.
    ///
    /// The quotient and remainder encodings are total functions whose value at
    /// a zero divisor is left unconstrained, so no background assumption is
    /// needed for well-formedness. Instead, we collect path-guarded
    /// `divisor != 0` obligations that the verification layer asserts
    /// alongside negated postconditions. This makes the verifier detect
    /// division-by-zero as a verification failure. (#1629)
    ///
    /// Path-guarded so dead branches (e.g., `if false { x / y }`) don't trigger.
    fn assert_nonzero_divisor(&mut self, divisor: Term) {
        // Division obligations are asserted later at the surrounding VC level.
        // Terms built while encoding quantified definitions mention bound
        // variables, so recording them here would let those variables escape
        // their quantifier and become unconstrained globals in the negated goal.
        if self.quantifier_state.quantifier_depth() > 0 {
            return;
        }
        // An assumed formula owes no divisor check, by the rule the shift range
        // obligation follows (`ArithmeticModeState::assumption_position`). A
        // callee's `ensures` or a `requires` fact is Pearlite, where division is
        // total; a division the program executes is charged at its own MIR
        // assert. Collected here, `(rhs@ != 0) ==> r@ == x@ / rhs@` assumed at
        // `rhs == 0` became the unguarded goal `0 != 0` and refuted a true
        // contract (D-114, div_in_assumed_callee_spec_control.rs).
        if self.arithmetic_mode.assumption_position() {
            return;
        }
        if self.solver.get_sort(divisor) == Sort::Int && self.term_is_nonzero_int_literal(divisor) {
            return;
        }
        // In total integer arithmetic mode, SMT-LIB div/mod are total functions
        // and division by zero is well-defined. Skip obligations for ghost
        // functions operating on mathematical Int. Real division stays guarded
        // because SMT real `/` is underspecified at zero. (#1756, #1802)
        if self.arithmetic_mode.total_int_arithmetic() && self.solver.get_sort(divisor) == Sort::Int
        {
            return;
        }
        let zero = if self.solver.get_sort(divisor) == Sort::Real {
            self.solver.rational_const(0, 1)
        } else {
            self.solver.int_const(0)
        };
        let nonzero = self.solver.neq(divisor, zero);
        let guarded_nonzero = self.guard_with_active_path(nonzero);
        self.arithmetic_mode
            .push_division_obligation(guarded_nonzero);
    }

    /// Collect the machine-int shift proof obligation: `0 <= amount < bits`.
    ///
    /// Rust's `<<`/`>>` on a machine integer is only defined when the shift
    /// amount is inside the bit width of the SHIFTED operand's type; an
    /// over-wide (or negative) amount is an overflow panic. The Int/BV shift
    /// encodings are total, so — exactly like `divisor != 0` for `/`/`%`
    /// ([`Self::assert_nonzero_divisor`], #1629) — we collect a path-guarded
    /// range obligation that the verification layer asserts alongside negated
    /// postconditions, making an unproven shift range a verification failure.
    /// (ledger int-shift-full)
    ///
    /// Returns the amount term value-unchanged (Int-coerced on the Int path,
    /// untouched on the BV path): the marker this is invoked for is the
    /// identity on its argument.
    ///
    /// Path-guarded so dead branches (e.g., `if false { x >> y }`) don't
    /// trigger. Skipped inside quantified definitions for the same
    /// bound-variable-escape reason as division obligations, for literal
    /// amounts already inside `[0, bits)` (nothing to prove), and in
    /// ASSUMPTION position (preconditions / `LetAssume` facts re-encode the
    /// already-verified body, where the obligation was collected with its
    /// execution-path guard — re-collecting it unguarded would spuriously
    /// fail foreign goals such as the bitwalker `poke` proof_assert VC).
    pub(super) fn collect_shift_amount_range_obligation(
        &mut self,
        amount: Term,
        bits: u32,
    ) -> Term {
        // BV-SORTED amount (bitwise_proof BV encodings): emit the range check
        // NATIVELY in the BV theory on the amount term itself. Routing a BV
        // term through `coerce_to_numeric(IntOnly)` would bridge it to a
        // FRESH UNCONSTRAINED Int constant (`__trust_wp_num_coerce_*`), and
        // an obligation over an unconstrained Int is falsifiable in every
        // model — a guaranteed spurious counterexample. No Int-sort
        // round-trip, no aux constants: the check stays in the same theory
        // as the shift that consumes the amount. (bits.rs bitwise_proof
        // regression, ledger int-shift-full)
        if let Sort::BitVec(bv) = self.solver.get_sort(amount) {
            if self.quantifier_state.quantifier_depth() > 0
                || self.arithmetic_mode.assumption_position()
            {
                return amount;
            }
            let in_range = self.bv_shift_amount_in_range_check(amount, bv.width, bits);
            let guarded_in_range = self.guard_with_active_path(in_range);
            self.arithmetic_mode
                .push_division_obligation(guarded_in_range);
            return amount;
        }
        let zero = self.solver.int_const(0);
        let (amount, zero) =
            coerce_to_numeric(&mut self.solver, amount, zero, NumericOperandMode::IntOnly);
        if self.quantifier_state.quantifier_depth() > 0 {
            return amount;
        }
        if self.arithmetic_mode.assumption_position() {
            return amount;
        }
        if let Some(value) = self.term_int_literal_for_arithmetic(amount) {
            if value >= BigInt::from(0) && value < BigInt::from(bits) {
                return amount;
            }
        }
        let width = self.solver.int_const(i64::from(bits));
        let ge_zero = self.solver.ge(amount, zero);
        let lt_width = self.solver.lt(amount, width);
        let in_range = self.solver.and(ge_zero, lt_width);
        let guarded_in_range = self.guard_with_active_path(in_range);
        self.arithmetic_mode
            .push_division_obligation(guarded_in_range);
        amount
    }

    /// Native-BV form of the shift-amount range check `0 <= amount < bits`
    /// for a `BitVec(width)`-sorted amount term (ledger int-shift-full).
    ///
    /// The general encoder's BV bridge builds amount patterns with UNSIGNED
    /// `int2bv`/`bv2int` conversions (see [`Self::encode_int_binop_bv`]), so
    /// the amount's value is its unsigned interpretation: `>= 0` is
    /// intrinsic and the upper bound is a single `bvult amount, bits`
    /// (mirroring the unsigned comparison form of the native QF_BV lane).
    /// When `bits` does not fit in `width` unsigned bits, every pattern is
    /// below `bits` and the check is the constant `true`.
    fn bv_shift_amount_in_range_check(&mut self, amount: Term, width: u32, bits: u32) -> Term {
        if width < 64 && u64::from(bits) > (1u64 << width) - 1 {
            // `bits` exceeds the maximum unsigned value of the amount's
            // width: every representable amount is in range.
            return self.solver.bool_const(true);
        }
        let bits_const = self.solver.bv_const_u64(u64::from(bits), width);
        self.solver.bvult(amount, bits_const)
    }

    fn int_div_uf(&mut self, dividend: Term, divisor: Term) -> Term {
        let func = if let Some(func) = self.arithmetic_mode.int_div_func() {
            func.clone()
        } else {
            let func =
                self.solver
                    .declare_fun("__trust_wp_int_div", &[Sort::Int, Sort::Int], Sort::Int);
            self.arithmetic_mode.set_int_div_func(func.clone());
            func
        };
        self.solver.apply(&func, &[dividend, divisor])
    }

    /// Quotient UF for TRUNCATED (Rust signed `/`) division — a SEPARATE symbol
    /// from `int_div_uf` (Euclidean) so the two semantics never share a term and
    /// contradict each other's defining axioms.
    fn int_div_uf_truncated(&mut self, dividend: Term, divisor: Term) -> Term {
        let func = if let Some(func) = self.spec_func_decl_cloned("__trust_wp_int_div_trunc") {
            func
        } else {
            let func = self.solver.declare_fun(
                "__trust_wp_int_div_trunc",
                &[Sort::Int, Sort::Int],
                Sort::Int,
            );
            self.register_spec_func("__trust_wp_int_div_trunc".to_string(), func.clone());
            func
        };
        self.solver.apply(&func, &[dividend, divisor])
    }

    /// Remainder UF for TRUNCATED (Rust signed `%`) modulo with a SYMBOLIC
    /// divisor. Asserts the truncated sign-of-dividend bounds for a positive
    /// divisor. Separate symbol from `int_mod_uf` (Euclidean).
    fn int_mod_uf_truncated(&mut self, dividend: Term, divisor: Term) -> Term {
        let func = if let Some(func) = self.spec_func_decl_cloned("__trust_wp_int_rem_trunc") {
            func
        } else {
            let func = self.solver.declare_fun(
                "__trust_wp_int_rem_trunc",
                &[Sort::Int, Sort::Int],
                Sort::Int,
            );
            self.register_spec_func("__trust_wp_int_rem_trunc".to_string(), func.clone());
            func
        };
        let result = self.solver.apply(&func, &[dividend, divisor]);

        // Truncated bounds for a POSITIVE divisor: the remainder takes the sign
        // of the dividend with magnitude strictly < divisor.
        //   dividend >= 0  ==>  0 <= result < divisor
        //   dividend <  0  ==>  -divisor < result <= 0
        let zero = self.solver.int_const(0);
        let divisor_positive = self.solver.lt(zero, divisor);
        let neg_divisor = self.solver.sub(zero, divisor);
        let dividend_nonneg = self.solver.le(zero, dividend);
        let dividend_neg = self.solver.lt(dividend, zero);
        let nn_lower = self.solver.le(zero, result);
        let nn_upper = self.solver.lt(result, divisor);
        let nn_bounds = self.solver.and(nn_lower, nn_upper);
        let nn_case = self.solver.implies(dividend_nonneg, nn_bounds);
        let neg_lower = self.solver.lt(neg_divisor, result);
        let neg_upper = self.solver.le(result, zero);
        let neg_bounds = self.solver.and(neg_lower, neg_upper);
        let neg_case = self.solver.implies(dividend_neg, neg_bounds);
        let bounds = self.solver.and(nn_case, neg_case);
        let guarded_bounds = self.solver.implies(divisor_positive, bounds);
        let guarded_bounds = self.guard_with_active_path(guarded_bounds);
        self.assert_solver_term(
            "int_rem_trunc/truncated_positive_divisor_bounds",
            guarded_bounds,
        );

        result
    }

    /// Pin a literal-divisor TRUNCATED quotient via the linear sign-split axiom.
    ///
    /// Rust's `/` truncates toward zero, so `r = l - c*q` takes the sign of the
    /// dividend with `|r| < |c|`. For a literal divisor `c` this is the linear,
    /// fully-LRA-decidable characterization
    ///   * `l >= 0`:  `0 <= r < |c|`
    ///   * `l <  0`:  `-|c| < r <= 0`
    /// which uniquely determines `q` for every sign combination (`-7/2=-3`,
    /// `-7/-2=3`, `7/-2=-3`, `7/2=3`). `c` is a compile-time literal so `c*q` is
    /// linear. Definitional identity (adds no unsound hypothesis); path-guarded.
    fn assert_int_div_linear_truncated_axiom(
        &mut self,
        dividend: Term,
        divisor_literal: &BigInt,
        quotient: Term,
    ) {
        let zero_big = BigInt::from(0);
        if *divisor_literal == zero_big {
            return;
        }
        let abs_c_big = if *divisor_literal > zero_big {
            divisor_literal.clone()
        } else {
            -divisor_literal
        };
        let c_term = self.solver.int_const_bigint(divisor_literal);
        let abs_c = self.solver.int_const_bigint(&abs_c_big);
        let c_q = self.solver.mul(c_term, quotient);
        let r = self.solver.sub(dividend, c_q); // r = l - c*q
        let zero = self.solver.int_const(0);
        let neg_abs_c = self.solver.sub(zero, abs_c);
        let dividend_nonneg = self.solver.le(zero, dividend);
        let dividend_neg = self.solver.lt(dividend, zero);
        // l >= 0  ==>  0 <= r < |c|
        let nn_lower = self.solver.le(zero, r);
        let nn_upper = self.solver.lt(r, abs_c);
        let nn = self.solver.and(nn_lower, nn_upper);
        let nn_case = self.solver.implies(dividend_nonneg, nn);
        // l < 0  ==>  -|c| < r <= 0
        let neg_lower = self.solver.lt(neg_abs_c, r);
        let neg_upper = self.solver.le(r, zero);
        let neg = self.solver.and(neg_lower, neg_upper);
        let neg_case = self.solver.implies(dividend_neg, neg);
        let axiom = self.solver.and(nn_case, neg_case);
        let guarded = self.guard_with_active_path(axiom);
        self.assert_solver_term("int_div/truncated_literal_divisor", guarded);
    }

    /// Euclidean defining identity for a SYMBOLIC divisor:
    ///
    ///   divisor != 0  ==>  dividend == nlmul(divisor, quotient) + mod(dividend, divisor)
    ///
    /// where `quotient = __trust_wp_int_div(dividend, divisor)`, `nlmul` is the
    /// shared opaque nonlinear-product UF and `mod` the Euclidean remainder UF.
    /// The atom is LINEAR over the opaque UF applications, so it stays inside
    /// ay's supported fragment. Definitional identity of Euclidean division —
    /// a theorem of integer arithmetic under the intended interpretation of
    /// these UFs — so it adds no unsound hypothesis (same class as the
    /// `int_mod/euclidean_positive_divisor_bounds` axiom); path-guarded.
    ///
    /// Without it the div/mod pair is under-axiomatized: ay finds a genuine
    /// model of the WEAK encoding for obligations like
    /// `result == b*(a/b) + a%b ==> result == a` (e.g. `a=1, b=1, result=0`
    /// with `int_div(1,1)=0`), which trust-wp would report as a counterexample
    /// that is spurious for Rust semantics.
    fn assert_int_div_euclidean_identity(&mut self, dividend: Term, divisor: Term, quotient: Term) {
        let mod_term = self.int_mod_uf(dividend, divisor);
        let prod = self.encode_nonlinear_mul_uf(divisor, quotient);
        let sum = self.solver.add(prod, mod_term);
        let identity = self.solver.eq(dividend, sum);
        let zero = self.solver.int_const(0);
        let nonzero = self.solver.neq(divisor, zero);
        let guarded = self.solver.implies(nonzero, identity);
        let guarded = self.guard_with_active_path(guarded);
        self.assert_solver_term("int_div/euclidean_identity_symbolic_divisor", guarded);
    }

    /// Truncated defining identity for a SYMBOLIC divisor:
    ///
    ///   divisor != 0  ==>  dividend == nlmul(divisor, quotient) + rem_trunc(dividend, divisor)
    ///
    /// where `quotient = __trust_wp_int_div_trunc(dividend, divisor)`, `nlmul`
    /// is the shared opaque nonlinear-product UF and `rem_trunc` the truncated
    /// remainder UF (which carries its own sign-of-dividend bounds for a
    /// positive divisor). The atom is LINEAR over the opaque UF applications,
    /// so it stays inside ay's supported fragment. Definitional identity of
    /// truncated division — a theorem of integer arithmetic under the intended
    /// interpretation of these UFs — so it adds no unsound hypothesis; the
    /// exact analogue of `assert_int_div_euclidean_identity`, which it mirrors
    /// line for line.
    ///
    /// Without it the symbolic-divisor truncated quotient is a COMPLETELY FREE
    /// integer: nothing anywhere constrained `__trust_wp_int_div_trunc`, so
    /// `a / b` with a non-literal `b` could take any value at all. That is not
    /// a sign corner, it is the whole function, and it made even
    /// `requires(a >= 0 && b > 0) ensures(result * b <= a)` unprovable — the
    /// query is genuinely satisfiable under the weak encoding. It is the same
    /// class of gap, and the same fix, as the Euclidean identity above.
    ///
    /// Sharing `rem_trunc` also ties `/` and `%` on the same operands together,
    /// which is what makes `a == (a / b) * b + a % b` provable.
    fn assert_int_div_truncated_identity(&mut self, dividend: Term, divisor: Term, quotient: Term) {
        let remainder = self.int_mod_uf_truncated(dividend, divisor);
        let prod = self.encode_nonlinear_mul_uf(divisor, quotient);
        let sum = self.solver.add(prod, remainder);
        let identity = self.solver.eq(dividend, sum);
        let zero = self.solver.int_const(0);
        let nonzero = self.solver.neq(divisor, zero);
        let guarded = self.solver.implies(nonzero, identity);
        let guarded = self.guard_with_active_path(guarded);
        self.assert_solver_term("int_div/truncated_identity_symbolic_divisor", guarded);
    }

    /// Linear SIGN and MAGNITUDE bounds for a SYMBOLIC-divisor truncated quotient.
    ///
    /// The defining identity above pins the quotient only *through* the opaque
    /// `nlmul` product, so on its own it leaves the quotient itself free: with
    /// only the identity asserted, `0 / 1 == 3` is still a model of the
    /// encoding. That is not merely incomplete — it is how
    /// `requires(a == 0 && b > 0) ensures(result == 0)` came back FAILED with a
    /// counterexample, a verifier telling the reader their correct code is
    /// wrong.
    ///
    /// These four implications are linear in (dividend, divisor, quotient),
    /// are theorems of truncated division for every sign combination, and are
    /// tight — each bound is attained at `|divisor| == 1`:
    ///
    ///   a >= 0 && b > 0  ==>   0 <= q <= a
    ///   a <= 0 && b > 0  ==>   a <= q <= 0
    ///   a >= 0 && b < 0  ==>  -a <= q <= 0
    ///   a <= 0 && b < 0  ==>   0 <= q <= -a
    ///
    /// Definitional consequences, so they add no unsound hypothesis;
    /// path-guarded. No `divisor != 0` guard is needed — every antecedent
    /// already excludes it.
    fn assert_int_div_truncated_quotient_bounds(
        &mut self,
        dividend: Term,
        divisor: Term,
        quotient: Term,
    ) {
        let zero = self.solver.int_const(0);
        let neg_dividend = self.solver.sub(zero, dividend);

        let dividend_nonneg = self.solver.le(zero, dividend);
        let dividend_nonpos = self.solver.le(dividend, zero);
        let divisor_pos = self.solver.lt(zero, divisor);
        let divisor_neg = self.solver.lt(divisor, zero);

        // Each arm is `antecedent ==> lo <= q <= hi`.
        let arms = [
            (dividend_nonneg, divisor_pos, zero, dividend),
            (dividend_nonpos, divisor_pos, dividend, zero),
            (dividend_nonneg, divisor_neg, neg_dividend, zero),
            (dividend_nonpos, divisor_neg, zero, neg_dividend),
        ];
        for (dividend_sign, divisor_sign, low, high) in arms {
            let antecedent = self.solver.and(dividend_sign, divisor_sign);
            let lower = self.solver.le(low, quotient);
            let upper = self.solver.le(quotient, high);
            let bounds = self.solver.and(lower, upper);
            let implication = self.solver.implies(antecedent, bounds);
            let guarded = self.guard_with_active_path(implication);
            self.assert_solver_term("int_div/truncated_symbolic_quotient_bounds", guarded);
        }
    }

    fn int_mod_uf(&mut self, dividend: Term, divisor: Term) -> Term {
        let func = if let Some(func) = self.spec_func_decl_cloned("__trust_wp_int_mod") {
            func
        } else {
            let func =
                self.solver
                    .declare_fun("__trust_wp_int_mod", &[Sort::Int, Sort::Int], Sort::Int);
            self.register_spec_func("__trust_wp_int_mod".to_string(), func.clone());
            func
        };
        let result = self.solver.apply(&func, &[dividend, divisor]);

        let zero = self.solver.int_const(0);
        let divisor_positive = self.solver.lt(zero, divisor);
        let lower_bound = self.solver.le(zero, result);
        let upper_bound = self.solver.lt(result, divisor);
        let bounds = self.solver.and(lower_bound, upper_bound);
        let guarded_bounds = self.solver.implies(divisor_positive, bounds);
        let guarded_bounds = self.guard_with_active_path(guarded_bounds);
        self.assert_solver_term("int_mod/euclidean_positive_divisor_bounds", guarded_bounds);

        result
    }

    /// Encode a genuinely-nonlinear integer product `x * y` (neither operand a
    /// literal) as an *uninterpreted* Int function application instead of a
    /// native `(* x y)` term.
    ///
    /// ay's linear-arithmetic core cannot reason about a native nonlinear
    /// product: the term is flagged unsupported and forces the whole query to
    /// Unknown. The UF abstraction is fully sound — an uninterpreted function
    /// is *less* constrained than `*`, so it cannot prove anything `*` would
    /// not — while keeping the query inside the supported linear fragment. The
    /// nonlinear-product-bound completeness pass attaches the SOUND
    /// monotonicity bound to the resulting opaque term when constant operand
    /// bounds are derivable.
    ///
    /// We do not assert any nonlinear defining axiom for this UF (that would
    /// reintroduce unsupported reasoning). The only facts ever attached to it
    /// are guarded monotonicity bounds, which are theorems of integer
    /// arithmetic. The UF symbol is shared (commutative-canonicalized by
    /// argument-handle ordering) so `x*y` and `y*x` map to the same term.
    fn encode_nonlinear_mul_uf(&mut self, left: Term, right: Term) -> Term {
        const NLMUL: &str = "__trust_wp_nonlinear_mul";
        let func = if let Some(func) = self.spec_func_decl_cloned(NLMUL) {
            func
        } else {
            let func = self
                .solver
                .declare_fun(NLMUL, &[Sort::Int, Sort::Int], Sort::Int);
            self.register_spec_func(NLMUL.to_string(), func.clone());
            func
        };
        // Canonicalize operand order so that `x*y` and `y*x` share one term.
        // Ordering on the opaque Term debug handle is arbitrary but stable
        // within a solve, which is all commutativity canonicalization needs.
        let (a, b) = if format!("{left:?}") <= format!("{right:?}") {
            (left, right)
        } else {
            (right, left)
        };
        self.solver.apply(&func, &[a, b])
    }

    fn term_is_nonzero_int_literal(&self, term: Term) -> bool {
        self.term_int_literal_for_arithmetic(term)
            .is_some_and(|value| value != BigInt::from(0))
    }

    pub(in crate::encoder) fn term_int_literal_for_arithmetic(&self, term: Term) -> Option<BigInt> {
        if self.solver.get_sort(term) != Sort::Int {
            return None;
        }
        match self.solver.term_kind(term) {
            TermKind::Const => {
                let rendered = self.solver.format_term(term);
                // Non-negative int constants render as `N`; negative constants
                // render in SMT prefix form `(- N)`. Normalize the latter so the
                // helper recognizes negative literals too (needed for the
                // literal-divisor div fold and nonzero-divisor checks).
                if let Ok(value) = rendered.parse::<BigInt>() {
                    Some(value)
                } else {
                    let inner = rendered
                        .strip_prefix("(- ")
                        .and_then(|s| s.strip_suffix(')'))?;
                    inner.trim().parse::<BigInt>().ok().map(|v| -v)
                }
            }
            TermKind::App { name, num_args: 2 } if matches!(name.as_str(), "+" | "-" | "*") => {
                let children = self.solver.term_children(term);
                let [lhs, rhs] = children.as_slice() else {
                    return None;
                };
                let lhs = self.term_int_literal_for_arithmetic(*lhs)?;
                let rhs = self.term_int_literal_for_arithmetic(*rhs)?;
                match name.as_str() {
                    "+" => Some(lhs + rhs),
                    "-" => Some(lhs - rhs),
                    "*" => Some(lhs * rhs),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// ay-dpll's native integer division currently does not participate in
    /// ground congruence through equalities. Bridge only encoded ground `div`
    /// applications, so checked-division specs can connect `self/rhs` aliases
    /// with user expressions such as `a / b`.
    fn assert_int_div_ground_congruence(&mut self, dividend: Term, divisor: Term, quotient: Term) {
        let existing = self.arithmetic_mode.int_div_terms().to_vec();
        for (prev_dividend, prev_divisor, prev_quotient) in existing {
            if prev_quotient == quotient {
                continue;
            }
            let same_dividend = self.eq_term(dividend, prev_dividend);
            let same_divisor = self.eq_term(divisor, prev_divisor);
            let same_args = self.solver.and(same_dividend, same_divisor);
            let same_quotient = self.eq_term(quotient, prev_quotient);
            let congruence = self.solver.implies(same_args, same_quotient);
            self.assert_solver_term("int_div_ground_congruence", congruence);

            let same_divisor = self.eq_term(divisor, prev_divisor);
            let zero = self.solver.int_const(0);
            let divisor_nonzero = self.solver.neq(divisor, zero);
            let prev_divisor_nonzero = self.solver.neq(prev_divisor, zero);
            let nonzero_fwd = self.solver.implies(divisor_nonzero, prev_divisor_nonzero);
            let nonzero_rev = self.solver.implies(prev_divisor_nonzero, divisor_nonzero);
            let nonzero_iff = self.solver.and(nonzero_fwd, nonzero_rev);
            let nonzero_bridge = self.solver.implies(same_divisor, nonzero_iff);
            self.assert_solver_term("int_div_divisor_nonzero_congruence", nonzero_bridge);
        }
        self.arithmetic_mode
            .push_int_div_term(dividend, divisor, quotient);
    }

    /// Pin the UF quotient of a literal-divisor integer division to its exact
    /// value via the linear Euclidean defining axiom (fix4-nia-div FIX 2).
    ///
    /// SMT-LIB Euclidean division `q = (div l c)` for literal `c != 0` is
    /// uniquely characterised by `0 <= l - c*q < |c|`, equivalently:
    ///   * `c > 0`: `c*q <= l < c*(q+1)`
    ///   * `c < 0`: `c*q <= l < c*(q-1)`
    ///
    /// Because `c` is a compile-time literal, `c*q` is a *linear* term — fully
    /// LRA-decidable — so this replaces the previous native `(div l c)` token
    /// (which the LRA bridge marks unsupported, degrading SAT to Unknown). The
    /// axiom is a definitional identity (always true), so it adds no unsound
    /// hypothesis; it pins the UF result to exactly the value the removed native
    /// bridge pinned, preserving provability. The axiom is path-guarded
    /// (no-op at top level, strictly correct under a branch).
    fn assert_int_div_linear_euclidean_axiom(
        &mut self,
        dividend: Term,
        divisor_literal: &BigInt,
        quotient: Term,
    ) {
        // `c == 0` cannot occur: this is only reached for literal divisors, and
        // `assert_nonzero_divisor` plus the well-formedness of the source program
        // exclude zero. Guard defensively anyway.
        let zero = BigInt::from(0);
        if *divisor_literal == zero {
            return;
        }
        let c_term = self.solver.int_const_bigint(divisor_literal);
        let c_q = self.solver.mul(c_term, quotient);
        let lower = self.solver.le(c_q, dividend);
        let upper = if *divisor_literal > zero {
            // c > 0: l < c*(q+1) = c*q + c
            let c_q_plus = self.solver.add(c_q, c_term);
            self.solver.lt(dividend, c_q_plus)
        } else {
            // c < 0: l < c*(q-1) = c*q - c  (note: -c = |c| > 0)
            let c_q_minus = self.solver.sub(c_q, c_term);
            self.solver.lt(dividend, c_q_minus)
        };
        let axiom = self.solver.and(lower, upper);
        let guarded = self.guard_with_active_path(axiom);
        self.assert_solver_term("int_div/euclidean_literal_divisor", guarded);
    }

    /// A float reaches a `BinOp` only as an operand of logical `==`/`!=`
    /// (equality of values: NaN equals itself, `0.0` and `-0.0` differ).
    /// Rust's arithmetic and comparisons on floats arrive as reserved IEEE
    /// calls (`trust_wp_core::formula::ieee`); a `BinOp` spelling of one would
    /// be read by the integer/real branches below, whose coercions replace a
    /// float by a fresh number and can make `x <= x` hold of NaN.
    fn refuse_float_binop(&self, l: Term, op: BinOp, r: Term) -> Result<(), EncodingError> {
        let l_sort = self.solver.get_sort(l);
        let r_sort = self.solver.get_sort(r);
        let is_float = crate::encoder::pure_encoding::ieee::is_float_value_sort;
        if !is_float(&l_sort) && !is_float(&r_sort) {
            return Ok(());
        }
        if matches!(op, BinOp::Eq | BinOp::Ne) && l_sort == r_sort {
            return Ok(());
        }
        Err(EncodingError::unsupported(format!(
            "`{op:?}` over a float operand ({l_sort:?}, {r_sort:?}): only logical equality \
             of two values of one float format is a relation on floats"
        )))
    }

    /// Encode a unary operation. A float operand is refused: its negation
    /// arrives as the reserved IEEE call, never as a `UnOp`.
    pub(super) fn encode_unop(&mut self, op: UnOp, inner: Term) -> Result<Term, EncodingError> {
        let inner_sort = self.solver.get_sort(inner);
        if crate::encoder::pure_encoding::ieee::is_float_value_sort(&inner_sort) {
            return Err(EncodingError::unsupported(format!(
                "`{op:?}` over a float operand: float negation arrives as its reserved IEEE call"
            )));
        }
        Ok(match op {
            UnOp::Not => {
                if self.solver.get_sort(inner) == Sort::Int {
                    if self.arithmetic_mode.bitwise_proof_mode() {
                        self.encode_int_unop_bv_not(inner)
                    } else {
                        let uf_name = "__trust_wp_bit_not";
                        let func = self.get_or_declare_logic_func(uf_name, &[Sort::Int], Sort::Int);
                        self.solver.apply(&func, &[inner])
                    }
                } else {
                    let inner = self.coerce_bool_operand(inner);
                    self.solver.not(inner)
                }
            }
            UnOp::Neg => self.solver.neg(inner),
            // Integer bitwise complement via BV-NOT (#2697).
            // Same conversion strategy as bitwise binops: Int -> BV -> bvnot -> Int.
            UnOp::BitNot => {
                if self.arithmetic_mode.bitwise_proof_mode() {
                    self.encode_int_unop_bv_not(inner)
                } else {
                    // Legacy UF path: encode as uninterpreted function.
                    let uf_name = "__trust_wp_bit_not";
                    let func = self.get_or_declare_logic_func(uf_name, &[Sort::Int], Sort::Int);
                    self.solver.apply(&func, &[inner])
                }
            }
            // UnOp is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns)]
            _ => {
                return Err(EncodingError::unsupported(format!(
                    "unknown UnOp variant: {op:?}"
                )))
            }
        })
    }

    /// Register signed W-window hints from function premises (#route-100
    /// rightmostbit latent false-reject; see `encode_int_binop_bv_hinted`).
    ///
    /// Recognizes the paired driver-injected range preconditions
    /// `v@ >= -2^(W-1)` and `v@ <= 2^(W-1)-1` (plain integer-literal bounds,
    /// exactly as the driver emits them). SOUNDNESS: the hints may only be
    /// consumed in a VC that ASSERTS the scanned premises — the hint's
    /// exactness argument quantifies over premise-satisfying models only.
    /// The registration call sites therefore live in verification pipelines
    /// that assert `requires` wholesale.
    pub(crate) fn register_signed_window_hints(&mut self, requires: &[PureExpr]) {
        use std::collections::HashMap;
        let mut lows: HashMap<&str, i128> = HashMap::new();
        let mut highs: HashMap<&str, i128> = HashMap::new();
        for require in requires {
            let PureExpr::BinOp(lhs, op, rhs) = require else {
                continue;
            };
            let Some(var) = int_view_var_name(lhs) else {
                continue;
            };
            let PureExpr::Int(c) = rhs.as_ref() else {
                continue;
            };
            let c = i128::from(*c);
            match op {
                BinOp::Ge => {
                    lows.entry(var)
                        .and_modify(|v| *v = (*v).max(c))
                        .or_insert(c);
                }
                BinOp::Le => {
                    highs
                        .entry(var)
                        .and_modify(|v| *v = (*v).min(c))
                        .or_insert(c);
                }
                _ => {}
            }
        }
        for (var, &lo) in &lows {
            let Some(&hi) = highs.get(var) else { continue };
            // Signed window: lo = -(hi+1) and hi+1 = 2^(W-1), W <= 64.
            if lo >= 0 || lo != -(hi + 1) {
                continue;
            }
            let Ok(half) = u128::try_from(hi + 1) else {
                continue;
            };
            if !half.is_power_of_two() {
                continue;
            }
            let width = half.trailing_zeros() + 1;
            if (2..=64).contains(&width) {
                self.arithmetic_mode
                    .insert_signed_window_hint((*var).to_string(), width);
            }
        }
    }

    /// Derive the signed narrow-width hint for a bitwise binop from its
    /// operand EXPRESSIONS: both operands must be pinned into the SAME
    /// signed W-window — either a premise-hinted variable (under `@`/`old`
    /// wrappers) or an integer literal that fits the window. Anything else
    /// returns `None` (keep the sound default encoding).
    pub(super) fn signed_narrow_bitwise_hint(&self, l: &PureExpr, r: &PureExpr) -> Option<u32> {
        let (wl, ll) = self.operand_signed_window(l)?;
        let (wr, rl) = self.operand_signed_window(r)?;
        match (wl, wr) {
            (Some(w1), Some(w2)) if w1 == w2 => Some(w1),
            (Some(w), None) => literal_fits_signed_window(rl?, w).then_some(w),
            (None, Some(w)) => literal_fits_signed_window(ll?, w).then_some(w),
            _ => None,
        }
    }

    /// `(premise hint, literal value)` of a bitwise operand expression.
    #[allow(clippy::option_option)] // (hint, literal): exactly one side is Some
    fn operand_signed_window(&self, expr: &PureExpr) -> Option<(Option<u32>, Option<i128>)> {
        if let PureExpr::Int(c) = expr {
            return Some((None, Some(i128::from(*c))));
        }
        let var = int_view_var_name(expr)?;
        let width = self.arithmetic_mode.signed_window_hint(var)?;
        Some((Some(width), None))
    }

    /// Encode integer bitwise NOT via BV-NOT (#2697).
    ///
    /// Mirrors `encode_int_binop_bv` but for a unary operation:
    /// Int -> BV(width) -> bvnot -> bv2int.
    fn encode_int_unop_bv_not(&mut self, operand: Term) -> Term {
        let width = match self.solver.get_sort(operand) {
            Sort::BitVec(bv) => bv.width,
            _ => DEFAULT_BV_WIDTH,
        };
        let bv_operand = if self.solver.get_sort(operand) == Sort::Int {
            self.solver
                .try_int2bv(operand, width)
                .unwrap_or_else(|_| operand)
        } else {
            operand
        };
        let bv_result = self.solver.bvnot(bv_operand);
        self.solver.bv2int(bv_result)
    }
}

/// Variable name under `@`/`old` wrappers (the view/entry value of a machine
/// integer IS the integer). `*v`/`^v` are different values — not conflated.
fn int_view_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::View(inner) | PureExpr::Old(inner) => int_view_var_name(inner),
        _ => None,
    }
}

/// Whether literal `c` lies in the signed W-bit window.
fn literal_fits_signed_window(c: i128, width: u32) -> bool {
    let half: i128 = 1i128 << (width - 1);
    c >= -half && c < half
}
