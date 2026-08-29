// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Layout intrinsic axioms for `size_of_logic` and `align_of_logic`.
//!
//! These functions are declared as uninterpreted functions (UFs) by the
//! placeholder path in `logic_fn/call_encoding/placeholder.rs`. Without
//! constraining axioms, the solver can assign arbitrary values (including
//! negative sizes or zero alignment), producing spurious counterexamples
//! for layout-related specifications.
//!
//! This module asserts three categories of axioms:
//!
//! **Generic layout laws** (apply to all `size_of_logic` / `align_of_logic` UFs):
//! - `size_of_logic() >= 0`
//! - `align_of_logic() >= 1`
//! - `align_of_logic()` is a power of 2 (i.e., one of 1, 2, 4, ..., 2^30)
//! - `size_of_logic() mod align_of_logic() == 0` (when both are present)
//!
//! **Concrete primitive axioms** (for type-specialized UFs like
//! `size_of_logic__u32`, `align_of_logic__bool`):
//! - `size_of_logic__u8() == 1`, `align_of_logic__u8() == 1`
//! - `size_of_logic__u16() == 2`, `align_of_logic__u16() == 2`
//! - `size_of_logic__u32() == 4`, `align_of_logic__u32() == 4`
//! - `size_of_logic__u64() == 8`, `align_of_logic__u64() == 8`
//! - Same for i8, i16, i32, i64
//! - `size_of_logic__bool() == 1`, `align_of_logic__bool() == 1`
//! - `size_of_logic__usize() == 8`, `align_of_logic__usize() == 8` (64-bit)
//! - `size_of_logic__isize() == 8`, `align_of_logic__isize() == 8` (64-bit)
//!
//! **Generic type-relational axioms** (relate size_of_logic across types):
//! - `size_of_logic__&T() == size_of_logic__usize()` (references are pointer-sized)
//! - `size_of_logic__*const T() == size_of_logic__usize()` (raw pointers)
//! - `size_of_logic__Box<T>() == size_of_logic__usize()` (Box is pointer-sized)
//! - `size_of_logic__Option<&T>() == size_of_logic__usize()` (niche optimization)
//! - `size_of_logic__Option<Box<T>>() == size_of_logic__usize()` (niche optimization)
//! - `size_of_logic__()() == 0` (unit type is zero-sized)
//! - `size_of_logic__[T; N]() == N * size_of_logic__T()` (array size formula)
//! - `size_of_logic__[T; 0]() == 0` (zero-length arrays)
//!
//! **Generic container relational axioms** (relate container size to element sizes):
//! - `size_of_logic__Option<T>() >= size_of_logic__T()` (must hold T; equal when
//!   niche-optimized, e.g. `Option<bool>`, `Option<NonZero<T>>`)
//! - `size_of_logic__Result<T, E>() >= size_of_logic__T()` (must hold T variant)
//! - `size_of_logic__Result<T, E>() >= size_of_logic__E()` (must hold E variant)
//! - `size_of_logic__Vec<T>() >= 3 * size_of_logic__usize()` (ptr + len + cap)
//!
//! **Tuple relational axioms** (relate tuple size to field sizes):
//! - `size_of_logic__(A, B)() >= size_of_logic__A() + size_of_logic__B()`
//!   (tuple size is at least the sum of field sizes; difference is padding)
//! - Generalizes to N-tuples: `size_of((A, B, C)) >= A + B + C`
//! - Falls back to primitive layout table when field type UFs are absent
//!
//! **Transparent wrapper axioms** (`#[repr(transparent)]` types):
//! - `size_of_logic__NonZero<T>() == size_of_logic__T()`
//! - `size_of_logic__Wrapping<T>() == size_of_logic__T()`
//! - `size_of_logic__Saturating<T>() == size_of_logic__T()`
//! - `size_of_logic__ManuallyDrop<T>() == size_of_logic__T()`
//! - `size_of_logic__MaybeUninit<T>() == size_of_logic__T()`
//! - `size_of_logic__Pin<P>() == size_of_logic__P()`
//! - `size_of_logic__Cell<T>() == size_of_logic__T()`
//! - `size_of_logic__UnsafeCell<T>() == size_of_logic__T()`
//!
//! The driver encodes the type parameter into the function name during
//! turbofish normalization (e.g., `size_of_logic::<u32>()` becomes
//! `size_of_logic__u32()`), enabling type-specific axiom matching here.
//!
//! Issue: #2324, #2693

#[cfg(test)]
mod tests;

use super::super::AYEncoder;

/// SMT name prefix for `size_of_logic` placeholder UFs.
const SIZE_OF_LOGIC_PREFIX: &str = "logic_size__of__logic";

/// SMT name prefix for `align_of_logic` placeholder UFs.
const ALIGN_OF_LOGIC_PREFIX: &str = "logic_align__of__logic";

/// Maximum exponent for the power-of-2 alignment disjunction.
///
/// Reduced from 30 to 6 (#2674): Rust alignments in practice are almost always
/// 1, 2, 4, 8, 16, 32, or 64. The previous 31-disjunct clause (2^0 through
/// 2^30) added unnecessary solver complexity for every verification query that
/// uses layout intrinsics. 2^6 = 64 covers all standard primitive types,
/// SIMD vectors (up to 512-bit), and custom `#[repr(align(N))]` types up to
/// 64-byte cache-line alignment. Types with exotic alignment requirements
/// (e.g., `#[repr(align(4096))]` for page alignment) are extremely rare in
/// Creusot-verified code.
const MAX_ALIGN_EXPONENT: u32 = 6;

/// Concrete layout values for known primitive types. (#2324)
///
/// Each entry is `(smt_type_suffix, size_bytes, align_bytes)` where
/// `smt_type_suffix` is the SMT-encoded type name suffix that appears after
/// the base prefix (e.g., `"____u32"` for `size_of_logic__u32`).
///
/// The driver encodes `size_of_logic::<u32>()` as `size_of_logic__u32()`,
/// and `logic_fn_smt_name("size_of_logic__u32")` produces
/// `logic_size__of__logic____u32` — the base prefix plus `____u32`.
///
/// Layout values match Rust's guarantees on 64-bit platforms (the primary
/// target). `usize`/`isize` are 8 bytes; on 32-bit platforms these would
/// differ, but trust-wp currently targets 64-bit only.
const PRIMITIVE_LAYOUTS: &[(&str, i64, i64)] = &[
    // (smt_suffix, size, align)
    ("____u8", 1, 1),
    ("____u16", 2, 2),
    ("____u32", 4, 4),
    ("____u64", 8, 8),
    ("____u128", 16, 8),
    ("____i8", 1, 1),
    ("____i16", 2, 2),
    ("____i32", 4, 4),
    ("____i64", 8, 8),
    ("____i128", 16, 8),
    ("____bool", 1, 1),
    ("____char", 4, 4),
    ("____f32", 4, 4),
    ("____f64", 8, 8),
    ("____usize", 8, 8),
    ("____isize", 8, 8),
];

/// SMT-encoded type suffix for `usize` (used for pointer-sized relational
/// axioms).
const USIZE_TYPE_SUFFIX: &str = "____usize";

/// SMT-encoded type suffix for the unit type `()`. The function name
/// `size_of_logic__()` has the `__` separator (2 underscores, each encoded
/// as `__` -> 4 underscores) followed by `(` -> `_LP_`, `)` -> `_RP_`.
const UNIT_TYPE_SUFFIX: &str = "_____LP__RP_";

/// Type suffix prefix for reference types: `&T` encodes as `____` + `_R_...`.
/// `logic_fn_smt_name` maps `&` -> `_R_`.
const REF_TYPE_PREFIX: &str = "_____R_";

/// Type suffix prefix for raw pointer types: `*const T` / `*mut T` encode as
/// `____` + `_D_...`. `logic_fn_smt_name` maps `*` -> `_D_`.
const RAW_PTR_TYPE_PREFIX: &str = "_____D_";

/// Type suffix prefix for `Box<T>`: encodes as `____Box_LT_..._GT_`.
const BOX_TYPE_PREFIX: &str = "____Box_LT_";

/// Type suffix prefix for `Option<&T>`: niche-optimized to pointer size.
const OPTION_REF_TYPE_PREFIX: &str = "____Option_LT__R_";

/// Type suffix prefix for `Option<Box<T>>`: niche-optimized to pointer size.
const OPTION_BOX_TYPE_PREFIX: &str = "____Option_LT_Box_LT_";

/// Type suffix prefix for generic `Option<T>` (non-niche-optimized).
/// `Option<T>` encodes as `____Option_LT_..._GT_`.
/// Note: `Option<&T>` and `Option<Box<T>>` are handled separately as
/// pointer-sized via niche optimization. This prefix covers the general
/// case `Option<T>` where T is not a pointer type.
const OPTION_GENERIC_TYPE_PREFIX: &str = "____Option_LT_";

/// Type suffix prefix for `Result<T, E>`: encodes as
/// `____Result_LT_..._C_..._GT_`.
const RESULT_TYPE_PREFIX: &str = "____Result_LT_";

/// Type suffix prefix for `Vec<T>`: encodes as `____Vec_LT_..._GT_`.
const VEC_TYPE_PREFIX: &str = "____Vec_LT_";

/// Type suffix prefix for array types: `[T; N]` encodes as
/// `_____LB_..._x3B_..._RB_`. `logic_fn_smt_name` maps `[` -> `_LB_`,
/// `]` -> `_RB_`, `;` -> `_x3B_`.
const ARRAY_TYPE_PREFIX: &str = "_____LB_";

/// SMT-encoded semicolon separator in array type suffixes.
const ARRAY_SEMI_SEPARATOR: &str = "_x3B_";

/// SMT-encoded comma separator in generic type parameter lists (e.g.,
/// `Result<T, E>` encodes as `Result_LT_T_C__S_E_GT_` where `_C_` is
/// the comma and `_S_` is the space).
const COMMA_SEPARATOR: &str = "_C_";

/// Type suffix prefix for tuple types: `(A, B)` encodes as
/// `_____LP_<A>_C__S_<B>_RP_`. `logic_fn_smt_name` maps `(` -> `_LP_`,
/// `)` -> `_RP_`. The unit type `()` is handled separately by
/// [`UNIT_TYPE_SUFFIX`]. Non-unit tuples always have at least one `_C_`
/// (comma) separator between fields.
const TUPLE_TYPE_PREFIX: &str = "_____LP_";

/// Type suffix prefixes for `#[repr(transparent)]` wrapper types.
///
/// These types have the same size as their inner type parameter:
/// `size_of(Wrapper<T>) == size_of(T)`. Each constant is the SMT-encoded
/// prefix that appears after the `size_of_logic` base prefix.
///
/// The list covers the most common transparent wrappers in std:
/// - `NonZero<T>` / `NonZeroU32` etc. (num module)
/// - `Wrapping<T>` (num module)
/// - `Saturating<T>` (num module)
/// - `ManuallyDrop<T>` (mem module)
/// - `MaybeUninit<T>` (mem module)
/// - `Pin<P>` (pin module)
/// - `Cell<T>` (cell module)
/// - `UnsafeCell<T>` (cell module)
const TRANSPARENT_WRAPPER_PREFIXES: &[(&str, &str)] = &[
    // (prefix, human-readable name)
    ("____NonZero_LT_", "NonZero<T>"),
    ("____Wrapping_LT_", "Wrapping<T>"),
    ("____Saturating_LT_", "Saturating<T>"),
    ("____ManuallyDrop_LT_", "ManuallyDrop<T>"),
    ("____MaybeUninit_LT_", "MaybeUninit<T>"),
    ("____Pin_LT_", "Pin<P>"),
    ("____Cell_LT_", "Cell<T>"),
    ("____UnsafeCell_LT_", "UnsafeCell<T>"),
];

/// Type suffix prefix for `NonZero<T>`: encodes as `____NonZero_LT_..._GT_`.
/// `NonZero<T>` is `#[repr(transparent)]`, so size/align equals the inner T.
/// Covers both `core::num::NonZero<T>` (generic) and legacy `NonZeroU32` etc.
const NONZERO_GENERIC_PREFIX: &str = "____NonZero_LT_";

/// Type suffix prefix for the `_GT_` closing of generic NonZero types.
const GENERIC_CLOSE: &str = "_GT_";

/// Legacy NonZero type suffixes: `NonZeroU8`, `NonZeroI32`, etc.
/// These map directly to their inner primitive type's suffix.
const NONZERO_LEGACY_LAYOUTS: &[(&str, &str)] = &[
    ("____NonZeroU8", "____u8"),
    ("____NonZeroU16", "____u16"),
    ("____NonZeroU32", "____u32"),
    ("____NonZeroU64", "____u64"),
    ("____NonZeroU128", "____u128"),
    ("____NonZeroUsize", "____usize"),
    ("____NonZeroI8", "____i8"),
    ("____NonZeroI16", "____i16"),
    ("____NonZeroI32", "____i32"),
    ("____NonZeroI64", "____i64"),
    ("____NonZeroI128", "____i128"),
    ("____NonZeroIsize", "____isize"),
];

impl AYEncoder {
    /// Assert basic layout axioms for any declared `size_of_logic` and
    /// `align_of_logic` placeholder UFs.
    ///
    /// Called from `assert_standard_axioms()` after all expressions are encoded.
    /// Only asserts axioms for placeholders that were actually declared during
    /// encoding -- if neither `size_of_logic` nor `align_of_logic` appears in
    /// the verification query, this is a no-op.
    pub(crate) fn assert_layout_axioms(&mut self) {
        // Collect matching placeholder declarations. We need to snapshot the
        // names and func_decls before mutating through `self.solver`, so
        // collect into Vecs first.
        let size_decls: Vec<_> = self
            .logic_funcs_iter()
            .filter(|(name, decl)| {
                name.starts_with(SIZE_OF_LOGIC_PREFIX) && decl.domain().is_empty()
            })
            .map(|(name, decl)| (name.clone(), decl.clone()))
            .collect();

        let align_decls: Vec<_> = self
            .logic_funcs_iter()
            .filter(|(name, decl)| {
                name.starts_with(ALIGN_OF_LOGIC_PREFIX) && decl.domain().is_empty()
            })
            .map(|(name, decl)| (name.clone(), decl.clone()))
            .collect();

        // Assert size_of_logic() >= 0 for each size placeholder.
        let zero = self.solver.int_const(0);
        for (_name, decl) in &size_decls {
            let size_term = self.solver.apply(decl, &[]);
            let ge_zero = self.solver.ge(size_term, zero);
            self.solver.assert_term(ge_zero);
        }

        // Assert align_of_logic() >= 1 for each align placeholder.
        let one = self.solver.int_const(1);
        for (_name, decl) in &align_decls {
            let align_term = self.solver.apply(decl, &[]);
            let ge_one = self.solver.ge(align_term, one);
            self.solver.assert_term(ge_one);
        }

        // Assert align_of_logic() is a power of 2 for each align placeholder.
        // Valid alignments are 1, 2, 4, 8, ..., 2^MAX_ALIGN_EXPONENT.
        // Expressed as a finite disjunction: align == 2^0 || align == 2^1 || ...
        // This subsumes the >= 1 constraint above but we keep both for clarity
        // and because the >= 1 assertion is a cheap lower bound that helps the
        // solver prune early.
        for (_name, decl) in &align_decls {
            let align_term = self.solver.apply(decl, &[]);
            let mut power_of_two_options = Vec::with_capacity((MAX_ALIGN_EXPONENT + 1) as usize);
            for exp in 0..=MAX_ALIGN_EXPONENT {
                let pow2 = self.solver.int_const(1i64 << exp);
                let eq_pow2 = self.eq_term(align_term, pow2);
                power_of_two_options.push(eq_pow2);
            }
            let is_power_of_two = self.solver.or_many(&power_of_two_options);
            self.solver.assert_term(is_power_of_two);
        }

        // Assert size_of_logic() mod align_of_logic() == 0 for each
        // (size, align) pair. Since type parameters are erased, all
        // size_of_logic calls share one placeholder and all align_of_logic
        // calls share one placeholder. The cross-product is typically 1x1.
        for (_size_name, size_decl) in &size_decls {
            let size_term = self.solver.apply(size_decl, &[]);
            for (_align_name, align_decl) in &align_decls {
                let align_term = self.solver.apply(align_decl, &[]);
                let remainder = self.solver.modulo(size_term, align_term);
                let remainder_eq_zero = self.eq_term(remainder, zero);
                self.solver.assert_term(remainder_eq_zero);
            }
        }

        // Assert concrete layout values for type-specialized UFs. (#2324)
        // When the driver preserves the type parameter in the function name
        // (e.g., `size_of_logic__u32`), the SMT name includes a type suffix
        // (e.g., `logic_size__of__logic____u32`). Match these against the
        // known primitive layout table and assert exact equalities.
        for (name, decl) in &size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            // Strip the placeholder sort tag (everything from `__placeholder_` onward)
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);
            for &(smt_suffix, size, _align) in PRIMITIVE_LAYOUTS {
                if type_suffix == smt_suffix {
                    let size_term = self.solver.apply(decl, &[]);
                    let concrete_size = self.solver.int_const(size);
                    let eq = self.eq_term(size_term, concrete_size);
                    self.solver.assert_term(eq);
                    break;
                }
            }
        }

        for (name, decl) in &align_decls {
            let suffix = &name[ALIGN_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);
            for &(smt_suffix, _size, align) in PRIMITIVE_LAYOUTS {
                if type_suffix == smt_suffix {
                    let align_term = self.solver.apply(decl, &[]);
                    let concrete_align = self.solver.int_const(align);
                    let eq = self.eq_term(align_term, concrete_align);
                    self.solver.assert_term(eq);
                    break;
                }
            }
        }

        // Assert generic type-relational axioms for `size_of_logic`.
        //
        // Rust guarantees certain layout relationships between types:
        // - All references, raw pointers, and Box are pointer-sized (== usize)
        // - Option<&T> and Option<Box<T>> use niche optimization (== usize)
        // - The unit type () has size 0
        // - Arrays [T; N] have size N * size_of(T)
        //
        // These axioms relate `size_of_logic` applied to different type
        // arguments. The driver encodes the type parameter into the function
        // name (e.g., `size_of_logic__&T` -> SMT name with `_R_T` suffix),
        // so we match on the SMT-encoded type suffix pattern.
        self.assert_pointer_sized_axioms(&size_decls);
        self.assert_unit_type_axiom(&size_decls);
        self.assert_array_size_axioms(&size_decls);
        self.assert_generic_container_axioms(&size_decls);
        self.assert_tuple_size_axioms(&size_decls);
        self.assert_transparent_wrapper_axioms(&size_decls);

        // Assert transparent layout axioms for NonZero types (#2669).
        // `NonZero<T>` is `#[repr(transparent)]`, so:
        //   size_of_logic__NonZero<T>() == size_of_logic__T()
        //   align_of_logic__NonZero<T>() == align_of_logic__T()
        self.assert_nonzero_transparent_axioms(&size_decls, SIZE_OF_LOGIC_PREFIX);
        self.assert_nonzero_transparent_axioms(&align_decls, ALIGN_OF_LOGIC_PREFIX);
    }

    /// Assert that pointer-like types have the same size as `usize`.
    ///
    /// Matches `size_of_logic` declarations whose type suffix indicates:
    /// - `&T` (references)
    /// - `*const T` / `*mut T` (raw pointers)
    /// - `Box<T>`
    /// - `Option<&T>` (niche-optimized)
    /// - `Option<Box<T>>` (niche-optimized)
    ///
    /// For each match, asserts `size_of_logic__<type>() == size_of_logic__usize()`.
    /// If no `usize` declaration exists in the current query, falls back to
    /// asserting `size_of_logic__<type>() == 8` (64-bit pointer size).
    fn assert_pointer_sized_axioms(&mut self, size_decls: &[(String, ay_dpll::api::FuncDecl)]) {
        // Find the usize declaration's term, or use the concrete constant 8.
        let usize_term = self.find_usize_size_term(size_decls);

        for (name, decl) in size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);

            if is_pointer_sized_type_suffix(type_suffix) {
                let size_term = self.solver.apply(decl, &[]);
                let eq = self.eq_term(size_term, usize_term);
                self.solver.assert_term(eq);
            }
        }
    }

    /// Find the SMT term for `size_of_logic__usize()`, or create a constant 8
    /// if no usize declaration exists.
    fn find_usize_size_term(
        &mut self,
        size_decls: &[(String, ay_dpll::api::FuncDecl)],
    ) -> ay_dpll::api::Term {
        for (name, decl) in size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);
            if type_suffix == USIZE_TYPE_SUFFIX {
                return self.solver.apply(decl, &[]);
            }
        }
        // Fallback: 8 bytes on 64-bit
        self.solver.int_const(8)
    }

    /// Assert `size_of_logic__()() == 0` for the unit type.
    fn assert_unit_type_axiom(&mut self, size_decls: &[(String, ay_dpll::api::FuncDecl)]) {
        let zero = self.solver.int_const(0);
        for (name, decl) in size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);
            if type_suffix == UNIT_TYPE_SUFFIX {
                let size_term = self.solver.apply(decl, &[]);
                let eq = self.eq_term(size_term, zero);
                self.solver.assert_term(eq);
            }
        }
    }

    /// Assert array size axioms: `size_of_logic__[T; N]() == N * size_of_logic__T()`.
    ///
    /// Parses the SMT-encoded array type suffix to extract the element type
    /// suffix and the array length N. For `[T; 0]`, directly asserts size == 0.
    /// For other lengths, looks up the element type's `size_of_logic` declaration
    /// and asserts the multiplicative relationship.
    fn assert_array_size_axioms(&mut self, size_decls: &[(String, ay_dpll::api::FuncDecl)]) {
        // Collect array axiom data first to avoid borrow conflicts.
        let mut array_axioms: Vec<(ay_dpll::api::FuncDecl, String, i64)> = Vec::new();

        for (name, decl) in size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);

            if !type_suffix.starts_with(ARRAY_TYPE_PREFIX) {
                continue;
            }

            // Parse array suffix: `_____LB_<elem>_x3B_<space><N>_RB_`
            // The content between `_LB_` and `_RB_` is the array interior.
            let interior = &type_suffix[ARRAY_TYPE_PREFIX.len()..];
            let Some(rb_pos) = interior.rfind("_RB_") else {
                continue;
            };
            let interior = &interior[..rb_pos];

            // Split on `_x3B_` (semicolon) to get element type and length.
            let Some(semi_pos) = interior.rfind(ARRAY_SEMI_SEPARATOR) else {
                continue;
            };
            let elem_suffix = &interior[..semi_pos];
            let len_part = &interior[semi_pos + ARRAY_SEMI_SEPARATOR.len()..];

            // The length part may have a leading `_S_` (space) from `; N`.
            let len_str = len_part.strip_prefix("_S_").unwrap_or(len_part);

            let Ok(array_len) = len_str.parse::<i64>() else {
                continue;
            };

            // Reconstruct the element type's SMT suffix: `____<elem_suffix>`
            let elem_type_suffix = format!("____{elem_suffix}");
            array_axioms.push((decl.clone(), elem_type_suffix, array_len));
        }

        let zero = self.solver.int_const(0);
        for (array_decl, elem_type_suffix, array_len) in &array_axioms {
            let array_size = self.solver.apply(array_decl, &[]);

            if *array_len == 0 {
                // [T; 0] always has size 0
                let eq = self.eq_term(array_size, zero);
                self.solver.assert_term(eq);
                continue;
            }

            // Find the element type's size_of_logic declaration.
            let elem_decl = size_decls.iter().find(|(name, _)| {
                let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
                let type_suffix = suffix
                    .find("__placeholder_")
                    .map_or(suffix, |pos| &suffix[..pos]);
                type_suffix == elem_type_suffix.as_str()
            });

            if let Some((_name, elem_fd)) = elem_decl {
                let elem_size = self.solver.apply(elem_fd, &[]);
                let n = self.solver.int_const(*array_len);
                let expected = self.solver.mul(n, elem_size);
                let eq = self.eq_term(array_size, expected);
                self.solver.assert_term(eq);
            } else {
                // Fallback: if the element type UF doesn't exist in the current
                // query but the element type is a known primitive, compute the
                // array size directly from the primitive layout table. This
                // handles cases like `size_of_logic::<[u32; 5]>()` when
                // `size_of_logic::<u32>()` is never called separately.
                if let Some(elem_size) = lookup_primitive_size(elem_type_suffix) {
                    let concrete = self.solver.int_const(*array_len * elem_size);
                    let eq = self.eq_term(array_size, concrete);
                    self.solver.assert_term(eq);
                } else if is_unit_type_suffix(elem_type_suffix) {
                    // [(); N] has size 0 for all N
                    let eq = self.eq_term(array_size, zero);
                    self.solver.assert_term(eq);
                }
            }
        }
    }

    /// Assert relational layout axioms for generic container types. (#2693)
    ///
    /// These axioms encode Rust's layout guarantees for generic wrappers:
    ///
    /// - **`Option<T>`**: `size_of(Option<T>) >= size_of(T)`.
    ///   Option must hold T, so it is at least as large. For most types, the
    ///   discriminant makes it strictly larger. However, Rust's niche
    ///   optimization can make them equal (e.g., `Option<bool>` has size 1,
    ///   `Option<NonZeroU32>` has size 4 — same as their inner types).
    ///   Note: `Option<&T>` and `Option<Box<T>>` are handled by
    ///   `assert_pointer_sized_axioms` (niche optimization makes them exactly
    ///   pointer-sized).
    ///
    /// - **`Result<T, E>`**: `size_of(Result<T, E>) >= size_of(T)` and
    ///   `size_of(Result<T, E>) >= size_of(E)`. Result must hold either variant.
    ///   Niche optimization can make Result the same size as the larger variant
    ///   (e.g., `Result<NonZeroI32, ()>` has size 4, same as `i32`).
    ///
    /// - **`Vec<T>`**: `size_of(Vec<T>) >= 3 * size_of(usize)`. Vec stores
    ///   a pointer, length, and capacity — three `usize`-sized fields.
    fn assert_generic_container_axioms(&mut self, size_decls: &[(String, ay_dpll::api::FuncDecl)]) {
        // Collect axiom targets first to avoid borrow conflicts with self.
        let mut option_axioms: Vec<(ay_dpll::api::FuncDecl, String)> = Vec::new();
        let mut result_axioms: Vec<(ay_dpll::api::FuncDecl, String, String)> = Vec::new();
        let mut vec_axioms: Vec<ay_dpll::api::FuncDecl> = Vec::new();

        for (name, decl) in size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);

            // Skip niche-optimized Option types (already handled as pointer-sized).
            if type_suffix.starts_with(OPTION_REF_TYPE_PREFIX)
                || type_suffix.starts_with(OPTION_BOX_TYPE_PREFIX)
            {
                continue;
            }

            if type_suffix.starts_with(OPTION_GENERIC_TYPE_PREFIX) {
                // Extract inner type: Option<T> suffix is `____Option_LT_<T>_GT_`
                if let Some(inner) =
                    extract_generic_inner_type(type_suffix, OPTION_GENERIC_TYPE_PREFIX)
                {
                    let elem_type_suffix = format!("____{inner}");
                    option_axioms.push((decl.clone(), elem_type_suffix));
                }
            } else if type_suffix.starts_with(RESULT_TYPE_PREFIX) {
                // Extract T and E: Result<T, E> suffix is
                // `____Result_LT_<T>_C_<space><E>_GT_`
                if let Some((ok_inner, err_inner)) = extract_result_inner_types(type_suffix) {
                    let ok_suffix = format!("____{ok_inner}");
                    let err_suffix = format!("____{err_inner}");
                    result_axioms.push((decl.clone(), ok_suffix, err_suffix));
                }
            } else if type_suffix.starts_with(VEC_TYPE_PREFIX) {
                vec_axioms.push(decl.clone());
            }
        }

        // Assert Option<T> >= T (must hold T; may be equal due to niche optimization).
        for (option_decl, elem_type_suffix) in &option_axioms {
            let option_size = self.solver.apply(option_decl, &[]);

            let elem_term = self.find_size_decl_by_suffix(size_decls, elem_type_suffix);
            if let Some(elem_size) = elem_term {
                // size_of(Option<T>) >= size_of(T)
                let ge = self.solver.ge(option_size, elem_size);
                self.solver.assert_term(ge);
            }
        }

        // Assert Result<T, E> >= T and Result<T, E> >= E (niche optimization
        // can make Result equal in size to the larger variant).
        for (result_decl, ok_suffix, err_suffix) in &result_axioms {
            let result_size = self.solver.apply(result_decl, &[]);

            if let Some(ok_size) = self.find_size_decl_by_suffix(size_decls, ok_suffix) {
                let ge_ok = self.solver.ge(result_size, ok_size);
                self.solver.assert_term(ge_ok);
            }

            if let Some(err_size) = self.find_size_decl_by_suffix(size_decls, err_suffix) {
                let ge_err = self.solver.ge(result_size, err_size);
                self.solver.assert_term(ge_err);
            }
        }

        // Assert Vec<T> >= 3 * usize (ptr + len + cap).
        if !vec_axioms.is_empty() {
            let usize_term = self.find_usize_size_term(size_decls);
            let three = self.solver.int_const(3);
            let triple_usize = self.solver.mul(three, usize_term);

            for vec_decl in &vec_axioms {
                let vec_size = self.solver.apply(vec_decl, &[]);
                let ge = self.solver.ge(vec_size, triple_usize);
                self.solver.assert_term(ge);
            }
        }
    }

    /// Find the `size_of_logic` SMT term for a given type suffix, or `None`
    /// if no matching declaration exists in the current query.
    fn find_size_decl_by_suffix(
        &mut self,
        size_decls: &[(String, ay_dpll::api::FuncDecl)],
        target_suffix: &str,
    ) -> Option<ay_dpll::api::Term> {
        for (name, decl) in size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);
            if type_suffix == target_suffix {
                return Some(self.solver.apply(decl, &[]));
            }
        }
        None
    }

    /// Assert tuple size axioms: `size_of((A, B, ...)) >= size_of(A) + size_of(B) + ...`.
    ///
    /// Rust tuples have size at least the sum of their field sizes (the
    /// difference being alignment padding). This is a sound lower bound:
    /// `size_of::<(A, B)>() >= size_of::<A>() + size_of::<B>()`.
    ///
    /// Tuples are encoded as `(A, B)` -> suffix `_____LP_A_C__S_B_RP_`.
    /// The unit type `()` (suffix `_____LP__RP_`) is handled separately
    /// by [`assert_unit_type_axiom`] and skipped here.
    fn assert_tuple_size_axioms(&mut self, size_decls: &[(String, ay_dpll::api::FuncDecl)]) {
        // Collect tuple axiom data to avoid borrow conflicts.
        let mut tuple_axioms: Vec<(ay_dpll::api::FuncDecl, Vec<String>)> = Vec::new();

        for (name, decl) in size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);

            if !type_suffix.starts_with(TUPLE_TYPE_PREFIX) {
                continue;
            }

            // Skip the unit type `()` -- already handled.
            if type_suffix == UNIT_TYPE_SUFFIX || is_unit_type_suffix(type_suffix) {
                continue;
            }

            if let Some(field_names) = extract_tuple_field_types(type_suffix) {
                // Only assert if there are 2+ fields (a 1-tuple is unusual but
                // would degenerate to size >= size_of(A), which is always true).
                if field_names.len() >= 2 {
                    let field_suffixes: Vec<String> =
                        field_names.iter().map(|f| format!("____{f}")).collect();
                    tuple_axioms.push((decl.clone(), field_suffixes));
                }
            }
        }

        // Assert size_of((A, B, ...)) >= size_of(A) + size_of(B) + ...
        let zero = self.solver.int_const(0);
        for (tuple_decl, field_suffixes) in &tuple_axioms {
            let tuple_size = self.solver.apply(tuple_decl, &[]);

            // Build the sum of field sizes. For each field, try to find its
            // size_of_logic declaration or look it up in the primitive table.
            let mut sum_terms: Vec<ay_dpll::api::Term> = Vec::new();
            let mut concrete_sum: i64 = 0;
            let mut all_concrete = true;

            for field_suffix in field_suffixes {
                if let Some(field_size) = self.find_size_decl_by_suffix(size_decls, field_suffix) {
                    sum_terms.push(field_size);
                } else if let Some(prim_size) = lookup_primitive_size(field_suffix) {
                    concrete_sum += prim_size;
                } else if is_unit_type_suffix(field_suffix) {
                    // Unit field: size 0, contributes nothing.
                } else {
                    // Unknown field type with no declaration -- cannot form
                    // a complete sum, so skip this tuple.
                    all_concrete = false;
                    break;
                }
            }

            if !all_concrete {
                continue;
            }

            // Build the total sum: concrete_sum + sum of symbolic terms.
            let total_sum = if sum_terms.is_empty() {
                self.solver.int_const(concrete_sum)
            } else {
                let mut acc = if concrete_sum > 0 {
                    self.solver.int_const(concrete_sum)
                } else {
                    zero
                };
                for term in &sum_terms {
                    acc = self.solver.add(acc, *term);
                }
                acc
            };

            // Assert: size_of((A, B, ...)) >= sum(size_of(A), size_of(B), ...)
            let ge = self.solver.ge(tuple_size, total_sum);
            self.solver.assert_term(ge);
        }
    }

    /// Assert transparent wrapper axioms: `size_of(Wrapper<T>) == size_of(T)`.
    ///
    /// Rust's `#[repr(transparent)]` guarantees that the wrapper type has the
    /// same layout as its inner type. This covers common std wrappers:
    /// `NonZero<T>`, `Wrapping<T>`, `Saturating<T>`, `ManuallyDrop<T>`,
    /// `MaybeUninit<T>`, `Pin<P>`, `Cell<T>`, `UnsafeCell<T>`.
    ///
    /// For each matching declaration, if the inner type has a `size_of_logic`
    /// declaration or is a known primitive, asserts exact equality. Otherwise
    /// the axiom is silently skipped (the inner type's size is unknown).
    fn assert_transparent_wrapper_axioms(
        &mut self,
        size_decls: &[(String, ay_dpll::api::FuncDecl)],
    ) {
        // Collect axiom targets first to avoid borrow conflicts.
        let mut wrapper_axioms: Vec<(ay_dpll::api::FuncDecl, String)> = Vec::new();

        for (name, decl) in size_decls {
            let suffix = &name[SIZE_OF_LOGIC_PREFIX.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);

            for &(prefix, _human_name) in TRANSPARENT_WRAPPER_PREFIXES {
                if type_suffix.starts_with(prefix) {
                    if let Some(inner) = extract_generic_inner_type(type_suffix, prefix) {
                        let inner_suffix = format!("____{inner}");
                        wrapper_axioms.push((decl.clone(), inner_suffix));
                    }
                    break;
                }
            }
        }

        // Assert size_of(Wrapper<T>) == size_of(T).
        let zero = self.solver.int_const(0);
        for (wrapper_decl, inner_suffix) in &wrapper_axioms {
            let wrapper_size = self.solver.apply(wrapper_decl, &[]);

            if let Some(inner_size) = self.find_size_decl_by_suffix(size_decls, inner_suffix) {
                // Inner type has a size_of_logic declaration: assert equality.
                let eq = self.eq_term(wrapper_size, inner_size);
                self.solver.assert_term(eq);
            } else if let Some(prim_size) = lookup_primitive_size(inner_suffix) {
                // Inner type is a known primitive: assert concrete equality.
                let concrete = self.solver.int_const(prim_size);
                let eq = self.eq_term(wrapper_size, concrete);
                self.solver.assert_term(eq);
            } else if is_unit_type_suffix(inner_suffix) {
                // Inner type is unit: wrapper is ZST.
                let eq = self.eq_term(wrapper_size, zero);
                self.solver.assert_term(eq);
            }
            // Otherwise: inner type unknown, skip (no axiom).
        }
    }

    /// Assert transparent layout axioms for `NonZero<T>` types (#2669).
    ///
    /// `NonZero<T>` is `#[repr(transparent)]`, so its size and alignment
    /// equal those of the inner type `T`. This method handles two forms:
    ///
    /// 1. **Generic form** (`NonZero<u32>`): SMT suffix `____NonZero_LT_u32_GT_`.
    ///    Extracts the inner type suffix and equates the declarations.
    ///
    /// 2. **Legacy named form** (`NonZeroU32`): SMT suffix `____NonZeroU32`.
    ///    Uses the `NONZERO_LEGACY_LAYOUTS` table to map to inner type suffix.
    ///
    /// For each NonZero declaration found, if a matching inner type declaration
    /// exists, asserts `layout_fn__NonZero<T>() == layout_fn__T()`.
    /// If the inner type is a known primitive with a concrete value, falls back
    /// to asserting the concrete value directly.
    fn assert_nonzero_transparent_axioms(
        &mut self,
        decls: &[(String, ay_dpll::api::FuncDecl)],
        prefix: &str,
    ) {
        // Collect NonZero axiom data to avoid borrow conflicts.
        struct NonZeroAxiom {
            nonzero_decl: ay_dpll::api::FuncDecl,
            inner_type_suffix: String,
        }
        let mut axioms: Vec<NonZeroAxiom> = Vec::new();

        for (name, decl) in decls {
            let suffix = &name[prefix.len()..];
            let type_suffix = suffix
                .find("__placeholder_")
                .map_or(suffix, |pos| &suffix[..pos]);

            // Check generic form: NonZero<T> -> ____NonZero_LT_<T>_GT_
            if type_suffix.starts_with(NONZERO_GENERIC_PREFIX) {
                let inner_part = &type_suffix[NONZERO_GENERIC_PREFIX.len()..];
                if let Some(gt_pos) = inner_part.rfind(GENERIC_CLOSE) {
                    let inner_type = &inner_part[..gt_pos];
                    // Reconstruct the inner type's full suffix: ____<inner_type>
                    let inner_type_suffix = format!("____{inner_type}");
                    axioms.push(NonZeroAxiom {
                        nonzero_decl: decl.clone(),
                        inner_type_suffix,
                    });
                }
                continue;
            }

            // Check legacy named form: NonZeroU32 -> ____NonZeroU32
            for &(legacy_suffix, inner_suffix) in NONZERO_LEGACY_LAYOUTS {
                if type_suffix == legacy_suffix {
                    axioms.push(NonZeroAxiom {
                        nonzero_decl: decl.clone(),
                        inner_type_suffix: inner_suffix.to_string(),
                    });
                    break;
                }
            }
        }

        // Assert equalities.
        for axiom in &axioms {
            let nonzero_term = self.solver.apply(&axiom.nonzero_decl, &[]);

            // Try to find the inner type's declaration first.
            let inner_decl = decls.iter().find(|(name, _)| {
                let suffix = &name[prefix.len()..];
                let type_suffix = suffix
                    .find("__placeholder_")
                    .map_or(suffix, |pos| &suffix[..pos]);
                type_suffix == axiom.inner_type_suffix
            });

            if let Some((_name, inner_fd)) = inner_decl {
                // Inner type declaration exists — equate them.
                let inner_term = self.solver.apply(inner_fd, &[]);
                let eq = self.eq_term(nonzero_term, inner_term);
                self.solver.assert_term(eq);
            } else {
                // No inner type declaration. Check if the inner type is a
                // known primitive and assert the concrete value directly.
                let is_size = prefix == SIZE_OF_LOGIC_PREFIX;
                for &(smt_suffix, size, align) in PRIMITIVE_LAYOUTS {
                    if axiom.inner_type_suffix == smt_suffix {
                        let concrete_val = if is_size { size } else { align };
                        let concrete = self.solver.int_const(concrete_val);
                        let eq = self.eq_term(nonzero_term, concrete);
                        self.solver.assert_term(eq);
                        break;
                    }
                }
            }
        }
    }
}

/// Extract the inner type name from a generic type suffix.
///
/// For `Option<T>` with prefix `____Option_LT_`, the suffix is
/// `____Option_LT_T_GT_` and the inner type is `T`.
/// Returns `None` if the suffix does not end with `_GT_`.
fn extract_generic_inner_type<'a>(type_suffix: &'a str, prefix: &str) -> Option<&'a str> {
    let after_prefix = &type_suffix[prefix.len()..];
    let gt_suffix = "_GT_";
    if after_prefix.ends_with(gt_suffix) {
        Some(&after_prefix[..after_prefix.len() - gt_suffix.len()])
    } else {
        None
    }
}

/// Extract the Ok and Err inner type names from a `Result<T, E>` suffix.
///
/// `Result<T, E>` encodes as `____Result_LT_T_C__S_E_GT_`.
/// The comma-space separator is `_C__S_` (comma `_C_` + space `_S_`).
/// Returns `(T_suffix, E_suffix)` or `None` if parsing fails.
fn extract_result_inner_types(type_suffix: &str) -> Option<(&str, &str)> {
    let after_prefix = &type_suffix[RESULT_TYPE_PREFIX.len()..];
    let gt_suffix = "_GT_";
    if !after_prefix.ends_with(gt_suffix) {
        return None;
    }
    let interior = &after_prefix[..after_prefix.len() - gt_suffix.len()];

    // Split on `_C_` (comma). The first comma separates T from E.
    // After the comma there may be `_S_` (space) before E.
    let comma_pos = interior.find(COMMA_SEPARATOR)?;
    let ok_part = &interior[..comma_pos];
    let err_part = &interior[comma_pos + COMMA_SEPARATOR.len()..];
    // Strip leading `_S_` (space) from err_part if present.
    let err_part = err_part.strip_prefix("_S_").unwrap_or(err_part);

    Some((ok_part, err_part))
}

/// Look up a known primitive type's size from the [`PRIMITIVE_LAYOUTS`] table.
///
/// `elem_type_suffix` is the reconstructed element-type SMT suffix, e.g.
/// `"____u32"`. Returns the element size in bytes, or `None` if the type is
/// not a known primitive.
fn lookup_primitive_size(elem_type_suffix: &str) -> Option<i64> {
    PRIMITIVE_LAYOUTS
        .iter()
        .find(|(smt_suffix, _, _)| *smt_suffix == elem_type_suffix)
        .map(|&(_, size, _)| size)
}

/// Check if an SMT-encoded type suffix represents the unit type `()`.
fn is_unit_type_suffix(type_suffix: &str) -> bool {
    // The element suffix reconstructed from an array `[(); N]` is
    // `____` + the encoded `()` content.  The unit type encodes as
    // `_LP__RP_` (parentheses with nothing inside).
    type_suffix == UNIT_TYPE_SUFFIX_ELEMENT || type_suffix.ends_with("_LP__RP_")
}

/// SMT-encoded type suffix for the unit type `()` as an array element.
///
/// When the array type `[(); 5]` is encoded, the element suffix reconstructed
/// by `assert_array_size_axioms` is `"_____LP__RP_"` (4 underscores for the
/// `____` prefix + `_LP__RP_` for `()`).
const UNIT_TYPE_SUFFIX_ELEMENT: &str = "_____LP__RP_";

/// Check if an SMT-encoded type suffix represents a pointer-sized type.
///
/// Pointer-sized types in Rust:
/// - `&T` (shared/exclusive references): suffix starts with `_____R_`
/// - `*const T` / `*mut T` (raw pointers): suffix starts with `_____D_`
/// - `Box<T>`: suffix starts with `____Box_LT_`
/// - `Option<&T>`: suffix starts with `____Option_LT__R_` (niche optimization)
/// - `Option<Box<T>>`: suffix starts with `____Option_LT_Box_LT_` (niche optimization)
fn is_pointer_sized_type_suffix(type_suffix: &str) -> bool {
    type_suffix.starts_with(REF_TYPE_PREFIX)
        || type_suffix.starts_with(RAW_PTR_TYPE_PREFIX)
        || type_suffix.starts_with(BOX_TYPE_PREFIX)
        || type_suffix.starts_with(OPTION_REF_TYPE_PREFIX)
        || type_suffix.starts_with(OPTION_BOX_TYPE_PREFIX)
}

/// Extract field type names from a tuple type suffix.
///
/// Tuple `(A, B, C)` encodes as `_____LP_A_C__S_B_C__S_C_RP_`.
/// Fields are separated by `_C__S_` (comma-space). Returns `None`
/// if the suffix does not match the tuple pattern (no `_RP_` terminator).
///
/// Note: This only handles simple (non-nested) field types. Nested
/// generics like `(Vec<u32>, Option<i64>)` would have `_LT_` / `_GT_`
/// inside field names, which this parser preserves as-is. The caller
/// uses the raw field name as a suffix to look up existing declarations.
fn extract_tuple_field_types(type_suffix: &str) -> Option<Vec<&str>> {
    let interior = &type_suffix[TUPLE_TYPE_PREFIX.len()..];

    // Must end with `_RP_`
    if !interior.ends_with("_RP_") {
        return None;
    }
    let interior = &interior[..interior.len() - "_RP_".len()];

    // Empty interior is the unit type `()` -- caller should handle separately
    if interior.is_empty() {
        return None;
    }

    // Split on `_C__S_` (comma + space separator).
    // Note: We use the full `_C__S_` separator, not just `_C_`, because
    // `_C_` alone could appear inside nested generic type names.
    let comma_space = "_C__S_";
    let fields: Vec<&str> = interior.split(comma_space).collect();

    Some(fields)
}
