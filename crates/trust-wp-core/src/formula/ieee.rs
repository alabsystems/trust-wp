// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The IEEE-754 operations of Rust's `f32`/`f64`, as reserved logic-function
//! names the driver emits and the solver backend interprets, and the
//! operations of `f16`/`f128`, which it leaves uninterpreted.
//!
//! Why a call and not a `BinOp`: `BinOp::Eq` is LOGICAL equality everywhere in
//! the pipeline (definitions, bindings, a contract's `==`), and `BinOp`s are
//! rewritten by passes that assume integer algebra (reflexivity of `==`/`<=`,
//! `!(a < b)` as `a >= b`, interval reasoning). None of that holds of IEEE
//! comparisons, which are false whenever an operand is NaN, and IEEE `==`
//! equates `0.0` with `-0.0`, which logical equality does not. A reserved call
//! is opaque to every such pass; only the backend gives it meaning, and it
//! gives exactly the IEEE-754 meaning (round-to-nearest-even arithmetic, which
//! is what Rust's operators do).

use super::{float_bits::FloatWidth, pure_expr::ExprSort, sort_intern::intern_sort_name};

const PREFIX: &str = "__trust_wp_ieee_";

/// One IEEE-754 operation of Rust's float primitives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IeeeOp {
    /// `a + b`, rounded to nearest-even.
    Add,
    /// `a - b`, rounded to nearest-even.
    Sub,
    /// `a * b`, rounded to nearest-even.
    Mul,
    /// `a / b`, rounded to nearest-even.
    Div,
    /// `a % b`: Rust's remainder, which truncates the quotient (C's `fmod`)
    /// and is exact. An uninterpreted function of its operands: SMT-LIB's
    /// `fp.rem` rounds the quotient to nearest, a different function, so the
    /// model forgets which value it is rather than guess.
    Rem,
    /// `-a` (flips the sign bit; `-NaN` is NaN).
    Neg,
    /// `a == b`: false if either is NaN, true for `0.0 == -0.0`.
    Eq,
    /// `a < b`: false if either is NaN.
    Lt,
    /// `a <= b`: false if either is NaN.
    Le,
    /// `a > b`: false if either is NaN.
    Gt,
    /// `a >= b`: false if either is NaN.
    Ge,
    /// `a.is_nan()`.
    IsNan,
    /// `a as <float of width>`: rounded to nearest-even; NaN stays NaN.
    ToFloat(FloatWidth),
    /// `a as <integer>`: truncated toward zero, saturated at the bounds, and
    /// NaN is `0`.
    ToInt {
        /// The target integer is signed.
        signed: bool,
        /// The target integer's width in bits.
        bits: u32,
    },
    /// `<integer> as <float>` (the call's width is the TARGET format),
    /// rounded to nearest-even.
    FromInt {
        /// The source integer is signed.
        signed: bool,
        /// The source integer's width in bits.
        bits: u32,
    },
}

/// A reserved IEEE logic function: an operation and the format it works in.
///
/// For [`IeeeOp::FromInt`] `width` is the format produced; for every other
/// operation it is the format of the float operand(s).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IeeeFn {
    /// The operation.
    pub op: IeeeOp,
    /// The float format the operation works in.
    pub width: FloatWidth,
}

impl IeeeFn {
    /// A reserved IEEE function.
    #[must_use]
    pub const fn new(op: IeeeOp, width: FloatWidth) -> Self {
        Self { op, width }
    }

    /// The reserved logic-function name.
    #[must_use]
    pub fn name(self) -> String {
        let op = match self.op {
            IeeeOp::Add => "add".to_string(),
            IeeeOp::Sub => "sub".to_string(),
            IeeeOp::Mul => "mul".to_string(),
            IeeeOp::Div => "div".to_string(),
            IeeeOp::Rem => "rem".to_string(),
            IeeeOp::Neg => "neg".to_string(),
            IeeeOp::Eq => "eq".to_string(),
            IeeeOp::Lt => "lt".to_string(),
            IeeeOp::Le => "le".to_string(),
            IeeeOp::Gt => "gt".to_string(),
            IeeeOp::Ge => "ge".to_string(),
            IeeeOp::IsNan => "is_nan".to_string(),
            IeeeOp::ToFloat(target) => format!("to_{}", target.rust_name()),
            IeeeOp::ToInt { signed, bits } => format!("to_{}{bits}", sign_tag(signed)),
            IeeeOp::FromInt { signed, bits } => format!("from_{}{bits}", sign_tag(signed)),
        };
        format!("{PREFIX}{}_{op}", self.width.rust_name())
    }

    /// Parse a reserved IEEE name; `None` for every other name.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        let rest = name.strip_prefix(PREFIX)?;
        let (width, op) = rest.split_once('_')?;
        let width = FloatWidth::from_rust_name(width)?;
        let op = match op {
            "add" => IeeeOp::Add,
            "sub" => IeeeOp::Sub,
            "mul" => IeeeOp::Mul,
            "div" => IeeeOp::Div,
            "rem" => IeeeOp::Rem,
            "neg" => IeeeOp::Neg,
            "eq" => IeeeOp::Eq,
            "lt" => IeeeOp::Lt,
            "le" => IeeeOp::Le,
            "gt" => IeeeOp::Gt,
            "ge" => IeeeOp::Ge,
            "is_nan" => IeeeOp::IsNan,
            other => {
                if let Some(target) = other.strip_prefix("to_") {
                    if let Some(target) = FloatWidth::from_rust_name(target) {
                        IeeeOp::ToFloat(target)
                    } else {
                        let (signed, bits) = parse_int_tag(target)?;
                        IeeeOp::ToInt { signed, bits }
                    }
                } else {
                    let (signed, bits) = parse_int_tag(other.strip_prefix("from_")?)?;
                    IeeeOp::FromInt { signed, bits }
                }
            }
        };
        let parsed = Self { op, width };
        // One spelling per function: a name that does not print back is not
        // reserved (for example `from_u08`).
        (parsed.name() == name).then_some(parsed)
    }

    /// Number of arguments the function takes.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self.op {
            IeeeOp::Add
            | IeeeOp::Sub
            | IeeeOp::Mul
            | IeeeOp::Div
            | IeeeOp::Rem
            | IeeeOp::Eq
            | IeeeOp::Lt
            | IeeeOp::Le
            | IeeeOp::Gt
            | IeeeOp::Ge => 2,
            IeeeOp::Neg
            | IeeeOp::IsNan
            | IeeeOp::ToFloat(_)
            | IeeeOp::ToInt { .. }
            | IeeeOp::FromInt { .. } => 1,
        }
    }

    /// The sort of the function's result.
    #[must_use]
    pub const fn result_sort(self) -> ExprSort {
        match self.op {
            IeeeOp::Add | IeeeOp::Sub | IeeeOp::Mul | IeeeOp::Div | IeeeOp::Rem | IeeeOp::Neg => {
                ExprSort::Float(self.width)
            }
            IeeeOp::FromInt { .. } => ExprSort::Float(self.width),
            IeeeOp::ToFloat(target) => ExprSort::Float(target),
            IeeeOp::Eq | IeeeOp::Lt | IeeeOp::Le | IeeeOp::Gt | IeeeOp::Ge | IeeeOp::IsNan => {
                ExprSort::Bool
            }
            IeeeOp::ToInt { .. } => ExprSort::Int,
        }
    }
}

const OPAQUE_PREFIX: &str = "__trust_wp_opaque_float_";

/// A Rust float format with no IEEE-754 model here: `f16` and `f128`.
///
/// A value of one is an element of an uninterpreted sort of its format
/// ([`OpaqueFormat::sort`]), so no integer or real operator reads it and its
/// only relation is logical equality. Every operation on one is an
/// application of an uninterpreted function of its operands
/// ([`OpaqueFloatFn`]), never its operand and never left untranslated: Rust's
/// operation IS a function of its operands, so the model only forgets which
/// one, whereas a lane that cannot translate an assignment may read the
/// destination at the value it held before (D-217).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpaqueFormat {
    /// `f16`.
    F16,
    /// `f128`.
    F128,
}

impl OpaqueFormat {
    /// The Rust type name, also the spelling inside the reserved names.
    #[must_use]
    pub const fn rust_name(self) -> &'static str {
        match self {
            Self::F16 => "f16",
            Self::F128 => "f128",
        }
    }

    /// The format named by a Rust type name.
    #[must_use]
    pub fn from_rust_name(name: &str) -> Option<Self> {
        match name {
            "f16" => Some(Self::F16),
            "f128" => Some(Self::F128),
            _ => None,
        }
    }

    /// The name of the uninterpreted sort a value of the format is; the
    /// reserved prefix keeps every user type off it.
    #[must_use]
    pub const fn sort_name(self) -> &'static str {
        match self {
            Self::F16 => "__trust_wp_f16",
            Self::F128 => "__trust_wp_f128",
        }
    }

    /// The format whose sort is named `name`.
    #[must_use]
    pub fn from_sort_name(name: &str) -> Option<Self> {
        [Self::F16, Self::F128]
            .into_iter()
            .find(|format| format.sort_name() == name)
    }

    /// The sort a value of the format is.
    #[must_use]
    pub fn sort(self) -> ExprSort {
        ExprSort::Datatype(intern_sort_name(self.sort_name()))
    }
}

/// The other side of an `as` cast to or from an [`OpaqueFormat`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpaquePeer {
    /// An `f32`/`f64`, at its IEEE sort.
    Float(FloatWidth),
    /// The other opaque format.
    Opaque(OpaqueFormat),
    /// An integer type.
    Int {
        /// The integer is signed.
        signed: bool,
        /// The integer's width in bits.
        bits: u32,
    },
}

impl OpaquePeer {
    fn tag(self) -> String {
        match self {
            Self::Float(width) => width.rust_name().to_string(),
            Self::Opaque(format) => format.rust_name().to_string(),
            Self::Int { signed, bits } => format!("{}{bits}", sign_tag(signed)),
        }
    }

    fn parse(tag: &str) -> Option<Self> {
        if let Some(width) = FloatWidth::from_rust_name(tag) {
            return Some(Self::Float(width));
        }
        if let Some(format) = OpaqueFormat::from_rust_name(tag) {
            return Some(Self::Opaque(format));
        }
        let (signed, bits) = parse_int_tag(tag)?;
        Some(Self::Int { signed, bits })
    }

    /// The sort a value of the peer type is read at.
    fn sort(self) -> ExprSort {
        match self {
            Self::Float(width) => ExprSort::Float(width),
            Self::Opaque(format) => format.sort(),
            Self::Int { .. } => ExprSort::Int,
        }
    }
}

/// One operation of an [`OpaqueFormat`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpaqueOp {
    /// A literal, as a function of its bit pattern (an integer).
    Literal,
    /// `a + b`.
    Add,
    /// `a - b`.
    Sub,
    /// `a * b`.
    Mul,
    /// `a / b`.
    Div,
    /// `a % b`.
    Rem,
    /// `-a`.
    Neg,
    /// `a == b` (`a != b` is its negation, as for every IEEE format).
    Eq,
    /// `a < b`.
    Lt,
    /// `a <= b`.
    Le,
    /// `a > b`.
    Gt,
    /// `a >= b`.
    Ge,
    /// `a as <peer>`.
    To(OpaquePeer),
    /// `<peer> as <format>`.
    From(OpaquePeer),
}

/// A reserved uninterpreted function of an [`OpaqueFormat`] operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OpaqueFloatFn {
    /// The operation.
    pub op: OpaqueOp,
    /// The format it works in (the format produced, for [`OpaqueOp::From`]).
    pub format: OpaqueFormat,
}

impl OpaqueFloatFn {
    /// A reserved opaque-format function.
    #[must_use]
    pub const fn new(op: OpaqueOp, format: OpaqueFormat) -> Self {
        Self { op, format }
    }

    /// The reserved logic-function name.
    #[must_use]
    pub fn name(self) -> String {
        let op = match self.op {
            OpaqueOp::Literal => "lit".to_string(),
            OpaqueOp::Add => "add".to_string(),
            OpaqueOp::Sub => "sub".to_string(),
            OpaqueOp::Mul => "mul".to_string(),
            OpaqueOp::Div => "div".to_string(),
            OpaqueOp::Rem => "rem".to_string(),
            OpaqueOp::Neg => "neg".to_string(),
            OpaqueOp::Eq => "eq".to_string(),
            OpaqueOp::Lt => "lt".to_string(),
            OpaqueOp::Le => "le".to_string(),
            OpaqueOp::Gt => "gt".to_string(),
            OpaqueOp::Ge => "ge".to_string(),
            OpaqueOp::To(peer) => format!("to_{}", peer.tag()),
            OpaqueOp::From(peer) => format!("from_{}", peer.tag()),
        };
        format!("{OPAQUE_PREFIX}{}_{op}", self.format.rust_name())
    }

    /// Parse a reserved opaque-format name; `None` for every other name.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        let rest = name.strip_prefix(OPAQUE_PREFIX)?;
        let (format, op) = rest.split_once('_')?;
        let format = OpaqueFormat::from_rust_name(format)?;
        let op = match op {
            "lit" => OpaqueOp::Literal,
            "add" => OpaqueOp::Add,
            "sub" => OpaqueOp::Sub,
            "mul" => OpaqueOp::Mul,
            "div" => OpaqueOp::Div,
            "rem" => OpaqueOp::Rem,
            "neg" => OpaqueOp::Neg,
            "eq" => OpaqueOp::Eq,
            "lt" => OpaqueOp::Lt,
            "le" => OpaqueOp::Le,
            "gt" => OpaqueOp::Gt,
            "ge" => OpaqueOp::Ge,
            other => {
                if let Some(peer) = other.strip_prefix("to_") {
                    OpaqueOp::To(OpaquePeer::parse(peer)?)
                } else {
                    OpaqueOp::From(OpaquePeer::parse(other.strip_prefix("from_")?)?)
                }
            }
        };
        // A cast within one format is the identity and has no function.
        if let OpaqueOp::To(OpaquePeer::Opaque(peer)) | OpaqueOp::From(OpaquePeer::Opaque(peer)) =
            op
        {
            if peer == format {
                return None;
            }
        }
        let parsed = Self { op, format };
        (parsed.name() == name).then_some(parsed)
    }

    /// The sorts of the function's arguments, in order.
    #[must_use]
    pub fn arg_sorts(self) -> Vec<ExprSort> {
        let own = self.format.sort();
        match self.op {
            OpaqueOp::Literal => vec![ExprSort::Int],
            OpaqueOp::Add
            | OpaqueOp::Sub
            | OpaqueOp::Mul
            | OpaqueOp::Div
            | OpaqueOp::Rem
            | OpaqueOp::Eq
            | OpaqueOp::Lt
            | OpaqueOp::Le
            | OpaqueOp::Gt
            | OpaqueOp::Ge => vec![own.clone(), own],
            OpaqueOp::Neg | OpaqueOp::To(_) => vec![own],
            OpaqueOp::From(peer) => vec![peer.sort()],
        }
    }

    /// The sort of the function's result.
    #[must_use]
    pub fn result_sort(self) -> ExprSort {
        match self.op {
            OpaqueOp::Eq | OpaqueOp::Lt | OpaqueOp::Le | OpaqueOp::Gt | OpaqueOp::Ge => {
                ExprSort::Bool
            }
            OpaqueOp::To(peer) => peer.sort(),
            OpaqueOp::Literal
            | OpaqueOp::Add
            | OpaqueOp::Sub
            | OpaqueOp::Mul
            | OpaqueOp::Div
            | OpaqueOp::Rem
            | OpaqueOp::Neg
            | OpaqueOp::From(_) => self.format.sort(),
        }
    }

    /// The result is a float value (of either an opaque or an IEEE format),
    /// which no integer or logical operator may read.
    #[must_use]
    pub const fn yields_float_value(self) -> bool {
        match self.op {
            OpaqueOp::Eq | OpaqueOp::Lt | OpaqueOp::Le | OpaqueOp::Gt | OpaqueOp::Ge => false,
            OpaqueOp::To(OpaquePeer::Int { .. }) => false,
            _ => true,
        }
    }

    /// An argument or the result is at an IEEE float sort.
    #[must_use]
    pub const fn mentions_ieee_sort(self) -> bool {
        matches!(
            self.op,
            OpaqueOp::To(OpaquePeer::Float(_)) | OpaqueOp::From(OpaquePeer::Float(_))
        )
    }
}

const fn sign_tag(signed: bool) -> &'static str {
    if signed {
        "s"
    } else {
        "u"
    }
}

fn parse_int_tag(tag: &str) -> Option<(bool, u32)> {
    let (signed, digits) = if let Some(rest) = tag.strip_prefix('s') {
        (true, rest)
    } else {
        (false, tag.strip_prefix('u')?)
    };
    let bits: u32 = digits.parse().ok()?;
    matches!(bits, 8 | 16 | 32 | 64 | 128).then_some((signed, bits))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_name_parses_back_to_its_function() {
        let widths = [FloatWidth::F32, FloatWidth::F64];
        let mut ops = vec![
            IeeeOp::Add,
            IeeeOp::Sub,
            IeeeOp::Mul,
            IeeeOp::Div,
            IeeeOp::Rem,
            IeeeOp::Neg,
            IeeeOp::Eq,
            IeeeOp::Lt,
            IeeeOp::Le,
            IeeeOp::Gt,
            IeeeOp::Ge,
            IeeeOp::IsNan,
            IeeeOp::ToFloat(FloatWidth::F32),
            IeeeOp::ToFloat(FloatWidth::F64),
        ];
        for bits in [8, 16, 32, 64, 128] {
            for signed in [false, true] {
                ops.push(IeeeOp::ToInt { signed, bits });
                ops.push(IeeeOp::FromInt { signed, bits });
            }
        }
        for width in widths {
            for op in &ops {
                let f = IeeeFn::new(*op, width);
                assert_eq!(IeeeFn::parse(&f.name()), Some(f), "{}", f.name());
            }
        }
    }

    #[test]
    fn foreign_and_non_canonical_names_are_not_reserved() {
        for name in [
            "__trust_wp_ieee_f16_add",
            "__trust_wp_ieee_f64_sqrt",
            "__trust_wp_ieee_f64_to_u7",
            "__trust_wp_ieee_f64_from_u08",
            "__trust_wp_ieee_f64_to_f16",
            "__trust_wp_ieee_f64",
            "__trust_wp_int_truncate_u8",
            "add",
        ] {
            assert_eq!(IeeeFn::parse(name), None, "{name}");
        }
    }

    #[test]
    fn every_opaque_name_parses_back_to_its_function() {
        let mut ops = vec![
            OpaqueOp::Literal,
            OpaqueOp::Add,
            OpaqueOp::Sub,
            OpaqueOp::Mul,
            OpaqueOp::Div,
            OpaqueOp::Rem,
            OpaqueOp::Neg,
            OpaqueOp::Eq,
            OpaqueOp::Lt,
            OpaqueOp::Le,
            OpaqueOp::Gt,
            OpaqueOp::Ge,
        ];
        let mut peers = vec![
            OpaquePeer::Float(FloatWidth::F32),
            OpaquePeer::Float(FloatWidth::F64),
        ];
        for bits in [8, 16, 32, 64, 128] {
            for signed in [false, true] {
                peers.push(OpaquePeer::Int { signed, bits });
            }
        }
        for peer in peers {
            ops.push(OpaqueOp::To(peer));
            ops.push(OpaqueOp::From(peer));
        }
        for (format, other) in [
            (OpaqueFormat::F16, OpaqueFormat::F128),
            (OpaqueFormat::F128, OpaqueFormat::F16),
        ] {
            let mut format_ops = ops.clone();
            format_ops.push(OpaqueOp::To(OpaquePeer::Opaque(other)));
            format_ops.push(OpaqueOp::From(OpaquePeer::Opaque(other)));
            for op in format_ops {
                let f = OpaqueFloatFn::new(op, format);
                assert_eq!(OpaqueFloatFn::parse(&f.name()), Some(f), "{}", f.name());
                assert_eq!(IeeeFn::parse(&f.name()), None, "{}", f.name());
                let binary = matches!(
                    op,
                    OpaqueOp::Add
                        | OpaqueOp::Sub
                        | OpaqueOp::Mul
                        | OpaqueOp::Div
                        | OpaqueOp::Rem
                        | OpaqueOp::Eq
                        | OpaqueOp::Lt
                        | OpaqueOp::Le
                        | OpaqueOp::Gt
                        | OpaqueOp::Ge
                );
                let arity = if binary { 2 } else { 1 };
                assert_eq!(f.arg_sorts().len(), arity, "{}", f.name());
            }
        }
    }

    #[test]
    fn opaque_identity_casts_and_foreign_names_are_not_reserved() {
        for name in [
            "__trust_wp_opaque_float_f16_to_f16",
            "__trust_wp_opaque_float_f128_from_f128",
            "__trust_wp_opaque_float_f32_add",
            "__trust_wp_opaque_float_f16_sqrt",
            "__trust_wp_opaque_float_f16_to_u7",
            "__trust_wp_opaque_float_f16",
            "__trust_wp_ieee_f16_add",
        ] {
            assert_eq!(OpaqueFloatFn::parse(name), None, "{name}");
        }
    }

    #[test]
    fn opaque_values_are_their_format_sort() {
        let f16 = OpaqueFormat::F16;
        let own = f16.sort();
        assert_ne!(own, OpaqueFormat::F128.sort());
        assert_eq!(OpaqueFormat::from_sort_name("__trust_wp_f16"), Some(f16));
        assert_eq!(OpaqueFormat::from_sort_name("f16"), None);
        let add = OpaqueFloatFn::new(OpaqueOp::Add, f16);
        assert_eq!(add.arg_sorts(), vec![own.clone(), own.clone()]);
        assert_eq!(add.result_sort(), own);
        let lit = OpaqueFloatFn::new(OpaqueOp::Literal, f16);
        assert_eq!(lit.arg_sorts(), vec![ExprSort::Int]);
        assert_eq!(lit.result_sort(), own);
        assert!(add.yields_float_value());
        let lt = OpaqueFloatFn::new(OpaqueOp::Lt, f16);
        assert_eq!(lt.result_sort(), ExprSort::Bool);
        assert!(!lt.yields_float_value());
        let widen = OpaqueFloatFn::new(OpaqueOp::To(OpaquePeer::Float(FloatWidth::F32)), f16);
        assert_eq!(widen.arg_sorts(), vec![own.clone()]);
        assert_eq!(widen.result_sort(), ExprSort::Float(FloatWidth::F32));
        assert!(widen.mentions_ieee_sort());
        let narrow = OpaqueFloatFn::new(OpaqueOp::From(OpaquePeer::Float(FloatWidth::F64)), f16);
        assert_eq!(narrow.arg_sorts(), vec![ExprSort::Float(FloatWidth::F64)]);
        assert_eq!(narrow.result_sort(), own);
        let to_f128 = OpaqueFloatFn::new(OpaqueOp::To(OpaquePeer::Opaque(OpaqueFormat::F128)), f16);
        assert_eq!(to_f128.result_sort(), OpaqueFormat::F128.sort());
        let to_int = OpaqueFloatFn::new(
            OpaqueOp::To(OpaquePeer::Int {
                signed: false,
                bits: 32,
            }),
            f16,
        );
        assert_eq!(to_int.result_sort(), ExprSort::Int);
        assert!(!to_int.yields_float_value());
        assert!(!to_int.mentions_ieee_sort());
    }

    #[test]
    fn result_sorts() {
        let f64_add = IeeeFn::new(IeeeOp::Add, FloatWidth::F64);
        assert_eq!(f64_add.result_sort(), ExprSort::Float(FloatWidth::F64));
        let narrow = IeeeFn::new(IeeeOp::ToFloat(FloatWidth::F32), FloatWidth::F64);
        assert_eq!(narrow.result_sort(), ExprSort::Float(FloatWidth::F32));
        let from = IeeeFn::new(
            IeeeOp::FromInt {
                signed: true,
                bits: 64,
            },
            FloatWidth::F32,
        );
        assert_eq!(from.result_sort(), ExprSort::Float(FloatWidth::F32));
        let lt = IeeeFn::new(IeeeOp::Lt, FloatWidth::F32);
        assert_eq!(lt.result_sort(), ExprSort::Bool);
        let to_int = IeeeFn::new(
            IeeeOp::ToInt {
                signed: false,
                bits: 8,
            },
            FloatWidth::F64,
        );
        assert_eq!(to_int.result_sort(), ExprSort::Int);
    }
}
