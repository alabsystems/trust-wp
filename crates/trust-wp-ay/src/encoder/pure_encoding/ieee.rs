// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IEEE-754 floats: literals, the reserved `__trust_wp_ieee_*` operations and
//! the one logical relation a float has (equality of values).
//!
//! A float is a term of ay's floating-point sort of its format, so NaN, the
//! infinities and the two zeros are values and every operation rounds exactly
//! as Rust's does (round-to-nearest-even). Nothing here reads a float as a
//! real number. Every operand must already carry the exact float sort the
//! operation names: a term of any other sort (an `Int` carrier, a fresh
//! coercion constant) is refused, because bridging it would compare values
//! the program never computed.

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{
    ieee::{IeeeFn, IeeeOp, OpaqueFloatFn, OpaqueFormat},
    ExprSort, FloatBits, FloatWidth, PureExpr,
};

use crate::{
    encoder::{sort_context::DerivedKind, AYEncoder},
    error::EncodingError,
};

/// ay's sort for a float format.
pub(crate) fn float_sort(width: FloatWidth) -> Sort {
    Sort::FloatingPoint(width.exponent_bits(), width.significand_bits())
}

/// A sort whose values are floats: an IEEE format's, or the uninterpreted
/// sort of `f16`/`f128`. No integer, real or logical operator but `==` reads
/// a value of one.
pub(crate) fn is_float_value_sort(sort: &Sort) -> bool {
    match sort {
        Sort::FloatingPoint(..) => true,
        Sort::Uninterpreted(name) => OpaqueFormat::from_sort_name(name).is_some(),
        _ => false,
    }
}

/// The float format of an ay sort, when it is one of Rust's two.
pub(crate) fn sort_float_width(sort: &Sort) -> Option<FloatWidth> {
    [FloatWidth::F32, FloatWidth::F64]
        .into_iter()
        .find(|width| float_sort(*width) == *sort)
}

fn solver_err(what: &str, err: impl std::fmt::Display) -> EncodingError {
    EncodingError::solver_error(format!("IEEE {what}: {err}"))
}

impl AYEncoder {
    /// A float literal in `width`, or the refusal that an unsuffixed contract
    /// literal cannot be exactly that format.
    pub(in crate::encoder) fn encode_float_literal_in(
        &mut self,
        bits: FloatBits,
        width: FloatWidth,
    ) -> Result<Term, EncodingError> {
        let literal = bits.in_width(width).ok_or_else(|| {
            EncodingError::unsupported(format!(
                "float literal {bits} is not exactly a {} value",
                width.rust_name()
            ))
        })?;
        let raw = literal
            .ieee_bits()
            .ok_or_else(|| EncodingError::unsupported("float literal without a format"))?;
        self.solver
            .try_fp_const_from_bits(raw, width.exponent_bits(), width.significand_bits())
            .map_err(|e| solver_err("literal", e))
    }

    /// A float literal in its own format; an unsuffixed contract literal with
    /// no context to decide it is read as `f64`, the format Rust gives an
    /// unconstrained float literal.
    pub(in crate::encoder) fn encode_float_literal(
        &mut self,
        bits: FloatBits,
    ) -> Result<Term, EncodingError> {
        self.encode_float_literal_in(bits, bits.width().unwrap_or(FloatWidth::F64))
    }

    /// Re-encode an unsuffixed float literal operand of a logical `==`/`!=`
    /// in its peer's format, so `result == 0.5` over an `f32` result compares
    /// `f32` values. Any other operand keeps its term.
    pub(in crate::encoder) fn fit_unsuffixed_float_literal(
        &mut self,
        expr: &PureExpr,
        term: Term,
        peer: Term,
    ) -> Result<Term, EncodingError> {
        let PureExpr::Float(bits) = expr else {
            return Ok(term);
        };
        if bits.width().is_some() {
            return Ok(term);
        }
        let peer_sort = self.solver.get_sort(peer);
        match sort_float_width(&peer_sort) {
            Some(width) => self.encode_float_literal_in(*bits, width),
            None => Ok(term),
        }
    }

    /// Encode one float operand of `f`: it must be a term of `width`'s sort.
    fn encode_ieee_float_operand(
        &mut self,
        f: IeeeFn,
        arg: &PureExpr,
        width: FloatWidth,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let PureExpr::Float(bits) = arg {
            return self.encode_float_literal_in(*bits, width);
        }
        let term = self.encode_pure_impl(arg, prefix)?;
        let sort = self.solver.get_sort(term);
        if sort == float_sort(width) {
            Ok(term)
        } else {
            Err(EncodingError::unsupported(format!(
                "{}: operand is {sort:?}, not {}; a float is never read at another sort",
                f.name(),
                width.rust_name()
            )))
        }
    }

    /// Encode a reserved IEEE call (see `trust_wp_core::formula::ieee`).
    pub(in crate::encoder) fn encode_ieee_call(
        &mut self,
        f: IeeeFn,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if args.len() != f.arity() {
            return Err(EncodingError::unsupported(format!(
                "{} takes {} argument(s), got {}",
                f.name(),
                f.arity(),
                args.len()
            )));
        }
        let width = f.width;
        match f.op {
            IeeeOp::Add | IeeeOp::Sub | IeeeOp::Mul | IeeeOp::Div => {
                let a = self.encode_ieee_float_operand(f, &args[0], width, prefix)?;
                let b = self.encode_ieee_float_operand(f, &args[1], width, prefix)?;
                let rne = self.rounding_mode("RNE")?;
                let result = match f.op {
                    IeeeOp::Add => self.solver.try_fp_add(rne, a, b),
                    IeeeOp::Sub => self.solver.try_fp_sub(rne, a, b),
                    IeeeOp::Mul => self.solver.try_fp_mul(rne, a, b),
                    _ => self.solver.try_fp_div(rne, a, b),
                };
                result.map_err(|e| solver_err("arithmetic", e))
            }
            IeeeOp::Eq | IeeeOp::Lt | IeeeOp::Le | IeeeOp::Gt | IeeeOp::Ge => {
                let a = self.encode_ieee_float_operand(f, &args[0], width, prefix)?;
                let b = self.encode_ieee_float_operand(f, &args[1], width, prefix)?;
                let result = match f.op {
                    IeeeOp::Eq => self.solver.try_fp_eq(a, b),
                    IeeeOp::Lt => self.solver.try_fp_lt(a, b),
                    IeeeOp::Le => self.solver.try_fp_le(a, b),
                    IeeeOp::Gt => self.solver.try_fp_gt(a, b),
                    _ => self.solver.try_fp_ge(a, b),
                };
                result.map_err(|e| solver_err("comparison", e))
            }
            // Rust's `%` truncates the quotient and SMT-LIB's `fp.rem` rounds
            // it to nearest: an application of an uninterpreted function of
            // the two operands, sound because Rust's remainder IS a function
            // of them, and complete only through congruence.
            IeeeOp::Rem => {
                let a = self.encode_ieee_float_operand(f, &args[0], width, prefix)?;
                let b = self.encode_ieee_float_operand(f, &args[1], width, prefix)?;
                let fs = float_sort(width);
                let func = self.get_or_declare_logic_func(&f.name(), &[fs.clone(), fs.clone()], fs);
                Ok(self.solver.apply(&func, &[a, b]))
            }
            IeeeOp::Neg => {
                let a = self.encode_ieee_float_operand(f, &args[0], width, prefix)?;
                self.solver.try_fp_neg(a).map_err(|e| solver_err("neg", e))
            }
            IeeeOp::IsNan => {
                let a = self.encode_ieee_float_operand(f, &args[0], width, prefix)?;
                self.solver
                    .try_fp_is_nan(a)
                    .map_err(|e| solver_err("is_nan", e))
            }
            IeeeOp::ToFloat(target) => {
                let a = self.encode_ieee_float_operand(f, &args[0], width, prefix)?;
                let rne = self.rounding_mode("RNE")?;
                self.solver
                    .try_fp_to_fp(rne, a, target.exponent_bits(), target.significand_bits())
                    .map_err(|e| solver_err("float conversion", e))
            }
            // `as` between a float and an integer is an application of an
            // uninterpreted function of its operand: Rust's conversion IS a
            // function of the operand, so this only forgets which one. ay
            // decides none of these conversions exactly (its `fp.to_sbv`
            // lane is incomplete and panics on 64-bit and wider targets), so
            // an exact encoding would buy no proof and could crash the run.
            IeeeOp::ToInt { .. } => {
                let a = self.encode_ieee_float_operand(f, &args[0], width, prefix)?;
                let func =
                    self.get_or_declare_logic_func(&f.name(), &[float_sort(width)], Sort::Int);
                Ok(self.solver.apply(&func, &[a]))
            }
            IeeeOp::FromInt { .. } => {
                let value = self.encode_pure_impl(&args[0], prefix)?;
                let sort = self.solver.get_sort(value);
                if sort != Sort::Int {
                    return Err(EncodingError::unsupported(format!(
                        "{}: operand is {sort:?}, not an integer",
                        f.name()
                    )));
                }
                let func =
                    self.get_or_declare_logic_func(&f.name(), &[Sort::Int], float_sort(width));
                Ok(self.solver.apply(&func, &[value]))
            }
        }
    }

    /// Encode a reserved `f16`/`f128` operation: an application of an
    /// uninterpreted function whose signature the name fixes. An argument of
    /// any other sort is refused, never bridged: the function would then be
    /// applied to a value the program never passed it.
    pub(in crate::encoder) fn encode_opaque_float_call(
        &mut self,
        f: OpaqueFloatFn,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let arg_sorts = f.arg_sorts();
        if args.len() != arg_sorts.len() {
            return Err(EncodingError::unsupported(format!(
                "{} takes {} argument(s), got {}",
                f.name(),
                arg_sorts.len(),
                args.len()
            )));
        }
        let mut terms = Vec::with_capacity(args.len());
        let mut domain = Vec::with_capacity(args.len());
        for (arg, expected) in args.iter().zip(&arg_sorts) {
            let term = match (arg, expected) {
                (PureExpr::Float(bits), ExprSort::Float(width)) => {
                    self.encode_float_literal_in(*bits, *width)?
                }
                _ => self.encode_pure_impl(arg, prefix)?,
            };
            let sort = self.solver.get_sort(term);
            let want = crate::encoder::sort_context::expr_sort_to_ay_sort(expected);
            if sort != want {
                return Err(EncodingError::unsupported(format!(
                    "{}: operand is {sort:?}, not {want:?}",
                    f.name()
                )));
            }
            terms.push(term);
            domain.push(want);
        }
        let range = crate::encoder::sort_context::expr_sort_to_ay_sort(&f.result_sort());
        let func = self.get_or_declare_logic_func(&f.name(), &domain, range);
        Ok(self.solver.apply(&func, &terms))
    }

    fn rounding_mode(&mut self, name: &str) -> Result<Term, EncodingError> {
        self.solver
            .try_fp_rounding_mode(name)
            .map_err(|e| solver_err("rounding mode", e))
    }
}
