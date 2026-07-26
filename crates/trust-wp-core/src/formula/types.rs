// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Support types for the formula module.
//!
//! Contains operator enums, memory location, value, permission types,
//! and tuple helper functions.

use super::PureExpr;

/// Binary operators
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    /// Modulo (remainder after division): `a % b`
    ///
    /// SMT encoding: `(mod a b)` - always returns non-negative result when divisor is positive.
    /// Note: SMT-LIB mod semantics differ from Rust's `%` for negative operands.
    /// This is the EUCLIDEAN remainder, used for mathematical `Int`, unsigned
    /// machine integers (where Euclidean == truncated), and the contract `%`.
    Mod,
    /// Truncated (toward-zero) integer division: Rust's `/` on **signed machine**
    /// integers (`-7 / 2 == -3`, not the Euclidean `-4`).
    ///
    /// Produced only by MIR/HIR lowering of signed machine `Div`. Distinct from
    /// [`BinOp::Div`] (Euclidean) so the model faithfully matches Rust runtime
    /// for negative operands. See `trust-wp-divmod-semantics`.
    DivTrunc,
    /// Truncated (toward-zero) remainder: Rust's `%` on **signed machine**
    /// integers — the remainder takes the SIGN OF THE DIVIDEND (`-1 % 5 == -1`,
    /// not the Euclidean `4`).
    ///
    /// Produced only by MIR/HIR lowering of signed machine `Rem`. Distinct from
    /// [`BinOp::Mod`] (Euclidean) so the model faithfully matches Rust runtime
    /// for negative operands.
    RemTrunc,
    /// Shift-left (`a << b`)
    Shl,
    /// Shift-right (`a >> b`)
    Shr,
    /// Bitwise AND (`a & b`)
    BitAnd,
    /// Bitwise XOR (`a ^ b`)
    BitXor,
    /// Bitwise OR (`a | b`)
    BitOr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    /// Logical implication: `p ==> q` (equivalent to `!p || q`)
    ///
    /// Used in quantifier bodies and specification predicates.
    /// Has lowest precedence (below `||`).
    Implies,
}

impl BinOp {
    /// Return the SMT-LIB UF symbol used for integer bitwise operators.
    #[must_use]
    pub const fn smt_int_uf_name(self) -> Option<&'static str> {
        match self {
            Self::Shl => Some("__trust_wp_bit_shl"),
            Self::Shr => Some("__trust_wp_bit_shr"),
            Self::BitAnd => Some("__trust_wp_bit_and"),
            Self::BitXor => Some("__trust_wp_bit_xor"),
            Self::BitOr => Some("__trust_wp_bit_or"),
            _ => None,
        }
    }
}

/// Unary operators
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
    /// Integer bitwise complement (`!x` on integer types).
    ///
    /// Distinct from `Not` which is boolean negation. In MIR, `UnOp::Not` on
    /// non-boolean operands is bitwise complement; we separate it here so the
    /// encoder can route to BV-NOT instead of boolean NOT. (#2697)
    BitNot,
}

/// Whether a mutable reborrow is final (source borrow never used afterward).
///
/// Produced by the `NotFinalPlaces` backward dataflow analysis (#2181).
/// Final borrows inherit the parent's prophecy variable instead of allocating
/// a fresh one, reducing quantifier load on the SMT solver.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BorrowFinality {
    /// The source borrow may be used after this reborrow — allocate a fresh
    /// prophecy variable (`x_final`).
    Fresh,
    /// The source borrow is NOT used after this reborrow — inherit the parent's
    /// prophecy variable. `deref_pos` is the projection index of the mutable
    /// dereference in the reborrowed place.
    Final { deref_pos: usize },
}

/// Borrow-id propagation for reborrows of `&mut` values. (#2141)
///
/// A fresh reborrow gets a distinct id. Final same-place reborrows inherit the
/// parent id directly. Final projected reborrows derive a stable child id via
/// `inherit_id(parent_id, step_kind, step_value)` in the ay layer.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BorrowIdOrigin {
    /// Fresh/non-final reborrow — allocate a distinct child id.
    Fresh { parent: String },
    /// Final reborrow of the same borrow value (`&mut *x`) — reuse the parent id.
    SameParent { parent: String },
    /// Final projected reborrow (`&mut x.field`, `&mut x[i]`) — derive a child id.
    Derived {
        parent: String,
        steps: Vec<BorrowIdStep>,
    },
}

/// A single projection step used when deriving a child borrow id from a parent id.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BorrowIdStep {
    /// Field projection by index.
    Field(u32),
    /// Index projection with the translated index expression.
    Index(PureExpr),
}

/// A memory location
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location(pub String);

/// A value
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Expr(PureExpr),
    Unknown,
}

/// Fractional permission (for shared references).
///
/// Permissions are represented as fractions where the denominator must be non-zero.
/// Use `Permission::FULL` for exclusive ownership (1/1) and `Permission::HALF`
/// for shared references (1/2).
///
/// # Type Safety
///
/// The `denominator` field uses `NonZeroU32` to enforce at the type level that
/// a zero denominator is impossible. This eliminates the need for runtime checks
/// and prevents invalid permission states from being constructed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Permission {
    pub numerator: u32,
    pub denominator: std::num::NonZeroU32,
}

impl Permission {
    /// Scale factor for encoding permissions as integers.
    ///
    /// Permissions are stored as integers on a `0..PERM_SCALE` scale where
    /// `PERM_SCALE` represents full (1/1) ownership. The value `2520 = LCM(1..10)`
    /// ensures that fractions with denominators up to 10 divide evenly,
    /// avoiding integer truncation errors (#741).
    pub const PERM_SCALE: i64 = 2520;

    /// Full permission (exclusive ownership)
    pub const FULL: Self = Self {
        numerator: 1,
        denominator: std::num::NonZeroU32::new(1).unwrap(),
    };

    /// Half permission (shared reference)
    pub const HALF: Self = Self {
        numerator: 1,
        denominator: std::num::NonZeroU32::new(2).unwrap(),
    };

    /// Create a new permission with the given numerator and denominator.
    ///
    /// Returns `None` if `denominator` is zero.
    ///
    /// # Example
    ///
    /// ```
    /// use trust_wp_core::formula::Permission;
    ///
    /// let quarter = Permission::new(1, 4).expect("4 is non-zero");
    /// assert_eq!(quarter.numerator, 1);
    /// assert_eq!(quarter.denominator.get(), 4);
    /// ```
    #[must_use]
    pub const fn new(numerator: u32, denominator: u32) -> Option<Self> {
        match std::num::NonZeroU32::new(denominator) {
            Some(d) => Some(Self {
                numerator,
                denominator: d,
            }),
            None => None,
        }
    }

    /// Compute the scaled integer value of this permission.
    ///
    /// Returns `numerator * PERM_SCALE / denominator`. This is exact for
    /// denominators that divide `PERM_SCALE` (i.e., denominators 1..10).
    #[must_use]
    pub const fn scaled_value(&self) -> i64 {
        (self.numerator as i64) * Self::PERM_SCALE / (self.denominator.get() as i64)
    }
}

/// Prefix used for synthetic logic-function encodings of tuple literals.
pub(crate) const TUPLE_LOGIC_FN_PREFIX: &str = "__trust_wp_tuple";

/// Build the synthetic logic-function name for an N-ary tuple literal.
///
/// Tuple literals in contracts are currently lowered to logic-function calls
/// (e.g., `(x, y)` -> `__trust_wp_tuple2(x, y)`) so they can flow through the
/// existing `PureExpr` pipeline without introducing a dedicated tuple AST node.
#[must_use]
pub(crate) fn tuple_logic_fn_name(arity: usize) -> String {
    format!("{TUPLE_LOGIC_FN_PREFIX}{arity}")
}

/// Parse a synthetic tuple logic-function name and recover its arity.
#[must_use]
pub(crate) fn tuple_logic_fn_arity(name: &str) -> Option<usize> {
    let suffix = name.strip_prefix(TUPLE_LOGIC_FN_PREFIX)?;
    if suffix.is_empty() {
        return None;
    }
    // Arity 0 is invalid (unit type has no fields to decompose).
    // Arity 1 is valid: used for newtype structs wrapping `&mut T` where the
    // driver needs `tuple1(v)` so postconditions like `^x.0` can decompose
    // via `tuple_get_0(tuple1(v)) = v`. Multi-item tuples (arity >= 2) are
    // the standard case from tuple literal lowering.
    let arity = suffix.parse::<usize>().ok()?;
    (arity >= 1).then_some(arity)
}

/// Prefix used for synthetic logic-function encodings of tuple field access.
pub(crate) const TUPLE_FIELD_LOGIC_FN_PREFIX: &str = "__trust_wp_tuple_get_";

/// Prefix used for synthetic logic-function encodings of named struct field access.
///
/// Named field access `expr.field` in contracts is lowered to a logic function call:
/// `x.inner` -> `__trust_wp_field_inner(x)`, `p.x` -> `__trust_wp_field_x(p)`.
pub(crate) const NAMED_FIELD_LOGIC_FN_PREFIX: &str = "__trust_wp_field_";

/// Synthetic logic-function name for the floor primitive (`real_to_int`).
///
/// Used by the driver to lower `FloatToInt` casts into a `LogicFnCall` node,
/// and by the encoder to dispatch to ay's `real_to_int` builtin. (#1802)
pub(crate) const REAL_TO_INT_FLOOR_LOGIC_FN: &str = "__trust_wp_real_to_int_floor";

/// Build the synthetic logic-function name for tuple field access.
///
/// Tuple field access `expr.N` in contracts is lowered to a logic function call:
/// `x.0` -> `__trust_wp_tuple_get_0(x)`, `x.1` -> `__trust_wp_tuple_get_1(x)`.
#[must_use]
pub(crate) fn tuple_field_logic_fn_name(index: usize) -> String {
    format!("{TUPLE_FIELD_LOGIC_FN_PREFIX}{index}")
}

/// Parse a synthetic tuple field logic-function name and recover its field index.
#[must_use]
pub(crate) fn tuple_field_logic_fn_index(name: &str) -> Option<usize> {
    let suffix = name.strip_prefix(TUPLE_FIELD_LOGIC_FN_PREFIX)?;
    suffix.parse::<usize>().ok()
}

/// Separator used to delimit the struct type name from the field name list
/// in named struct constructor encoding.
const NAMED_CTOR_FIELD_OPEN: char = '{';
const NAMED_CTOR_FIELD_CLOSE: char = '}';
const NAMED_CTOR_FIELD_SEP: char = ',';

/// Build a synthetic logic-function name for a named struct constructor.
///
/// Struct literals `TypeName { y: 1, x: 0 }` are lowered to
/// `LogicFnCall { name: "TypeName{y,x}", args: [1, 0] }` so that field names
/// are preserved for the driver's rewrite pass, which reorders args to match
/// the struct definition's canonical field order using `TyCtxt`. (#1819)
#[doc(hidden)]
#[must_use]
pub fn named_struct_ctor_name(type_name: &str, field_names: &[String]) -> String {
    use std::fmt::Write;
    let mut name = type_name.to_string();
    name.push(NAMED_CTOR_FIELD_OPEN);
    for (i, field) in field_names.iter().enumerate() {
        if i > 0 {
            name.push(NAMED_CTOR_FIELD_SEP);
        }
        let _ = write!(name, "{field}");
    }
    name.push(NAMED_CTOR_FIELD_CLOSE);
    name
}

/// Parse a named struct constructor name, returning the type name and field names.
///
/// Returns `Some((type_name, field_names))` if the name matches the
/// `TypeName{field1,field2,...}` convention, `None` otherwise.
#[doc(hidden)]
#[must_use]
pub fn parse_named_struct_ctor(name: &str) -> Option<(&str, Vec<&str>)> {
    let open = name.find(NAMED_CTOR_FIELD_OPEN)?;
    if !name.ends_with(NAMED_CTOR_FIELD_CLOSE) {
        return None;
    }
    let type_name = &name[..open];
    let fields_str = &name[open + 1..name.len() - 1];
    if fields_str.is_empty() {
        return Some((type_name, Vec::new()));
    }
    let field_names: Vec<&str> = fields_str.split(NAMED_CTOR_FIELD_SEP).collect();
    Some((type_name, field_names))
}
