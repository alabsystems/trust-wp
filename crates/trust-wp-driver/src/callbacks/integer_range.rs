// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integer range precondition generation for SMT verification.
//!
//! Rust integer types (`u8`..`u128`, `i8`..`i128`, `usize`, `isize`) are
//! encoded as unbounded mathematical integers in the SMT `Int` sort. Without
//! explicit range constraints the solver can construct spurious counterexamples
//! with out-of-range values (e.g., `i = -1` for `i: usize`).
//!
//! This module inspects function signatures via `TyCtxt` and generates range
//! constraint expressions:
//! - unsigned: `0 <= param@ <= 2^N - 1`
//! - signed:   `-2^(N-1) <= param@ <= 2^(N-1) - 1`

use std::sync::Arc;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};
use trust_wp_core::formula::{
    int_bounds::{signed_bounds_expr, unsigned_max_expr},
    BinOp, PureExpr,
};

use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

// pub(crate): the formula kernel lane (formula_kernel_lane.rs) resolves its
// unsigned variable widths through this same function — one width authority.
pub(crate) fn uint_bit_width(uint_ty: rustc_middle::ty::UintTy, pointer_bits: u32) -> u32 {
    use rustc_middle::ty::UintTy;
    match uint_ty {
        UintTy::U8 => 8,
        UintTy::U16 => 16,
        UintTy::U32 => 32,
        UintTy::U64 => 64,
        UintTy::U128 => 128,
        UintTy::Usize => pointer_bits,
    }
}

pub(crate) fn int_bit_width(int_ty: rustc_middle::ty::IntTy, pointer_bits: u32) -> u32 {
    use rustc_middle::ty::IntTy;
    match int_ty {
        IntTy::I8 => 8,
        IntTy::I16 => 16,
        IntTy::I32 => 32,
        IntTy::I64 => 64,
        IntTy::I128 => 128,
        IntTy::Isize => pointer_bits,
    }
}

/// Build integer range constraints for a single variable of known `Ty`.
///
/// Returns `>= 0` and `<= 2^N - 1` for unsigned types, or
/// `>= -2^(N-1)` and `<= 2^(N-1) - 1` for signed types.
/// Returns an empty vec for non-integer types.
///
/// The `var_expr` should be the `PureExpr::Var` representing the variable
/// (e.g., an opaque call result `_call_5`). A `View` wrapper is applied
/// internally to match the convention used for parameter range constraints.
pub(crate) fn build_integer_range_for_var(
    var_expr: PureExpr,
    ty: Ty<'_>,
    pointer_bits: u32,
) -> Vec<PureExpr> {
    use rustc_middle::ty::TyKind;

    let view_expr = PureExpr::View(Arc::new(var_expr));

    match ty.kind() {
        TyKind::Uint(uint_ty) => {
            let bits = uint_bit_width(*uint_ty, pointer_bits);
            vec![
                PureExpr::BinOp(
                    Arc::new(view_expr.clone()),
                    BinOp::Ge,
                    Arc::new(PureExpr::Int(0)),
                ),
                PureExpr::BinOp(
                    Arc::new(view_expr),
                    BinOp::Le,
                    Arc::new(unsigned_max_expr(bits)),
                ),
            ]
        }
        TyKind::Int(int_ty) => {
            let bits = int_bit_width(*int_ty, pointer_bits);
            let (min_val, max_val) = signed_bounds_expr(bits);
            vec![
                PureExpr::BinOp(Arc::new(view_expr.clone()), BinOp::Ge, Arc::new(min_val)),
                PureExpr::BinOp(Arc::new(view_expr), BinOp::Le, Arc::new(max_val)),
            ]
        }
        _ => Vec::new(),
    }
}

/// Build range preconditions for integer parameters.
///
/// For each unsigned parameter: `param@ >= 0` and `param@ <= 2^N - 1`.
/// For each signed parameter: `param@ >= -2^(N-1)` and `param@ <= 2^(N-1) - 1`.
///
/// `&T` and `&mut T` parameters are auto-dereferenced before the constraint.
pub(super) fn build_unsigned_range_preconditions(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
) -> Vec<PureExpr> {
    use std::sync::Arc;

    use rustc_middle::ty::TyKind;

    // Closures don't support fn_sig(); return empty.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return Vec::new();
    }

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();
    let pointer_bits = u32::try_from(tcx.data_layout.pointer_size().bits()).unwrap_or(64);

    let mut constraints = Vec::new();

    for (i, ty) in inputs.iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        let arg_name = &arg_names[i];

        // Peel references to get the inner type
        let (inner_ty, is_ref) = match ty.kind() {
            TyKind::Ref(_, inner, _) => (*inner, true),
            _ => (*ty, false),
        };

        // Build the variable expression, dereferencing if needed (#1965).
        let sort = ty_to_expr_sort_enriched(tcx, *ty);
        let var_expr = if is_ref {
            PureExpr::Deref(Arc::new(PureExpr::Var(arg_name.clone(), sort)))
        } else {
            PureExpr::Var(arg_name.clone(), sort)
        };

        // Use View to get the mathematical model (identity for integers)
        let view_expr = PureExpr::View(Arc::new(var_expr));

        match inner_ty.kind() {
            TyKind::Uint(uint_ty) => {
                // Non-negativity: param@ >= 0
                constraints.push(PureExpr::BinOp(
                    Arc::new(view_expr.clone()),
                    BinOp::Ge,
                    Arc::new(PureExpr::Int(0)),
                ));

                // Upper bound: param@ <= 2^N - 1, where N is the integer width.
                let bits = uint_bit_width(*uint_ty, pointer_bits);
                constraints.push(PureExpr::BinOp(
                    Arc::new(view_expr),
                    BinOp::Le,
                    Arc::new(unsigned_max_expr(bits)),
                ));
            }
            TyKind::Int(int_ty) => {
                // Signed integer range constraints: -2^(N-1) <= param@ <= 2^(N-1)-1.
                let bits = int_bit_width(*int_ty, pointer_bits);
                let (min_val, max_val) = signed_bounds_expr(bits);
                constraints.push(PureExpr::BinOp(
                    Arc::new(view_expr.clone()),
                    BinOp::Ge,
                    Arc::new(min_val),
                ));
                constraints.push(PureExpr::BinOp(
                    Arc::new(view_expr),
                    BinOp::Le,
                    Arc::new(max_val),
                ));
            }
            _ => {}
        }
    }

    constraints
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::{
            atomic::{AtomicU64, Ordering},
            Arc,
        },
    };

    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;
    use rustc_middle::ty::TyCtxt;
    use trust_wp_core::formula::{
        int_bounds::{signed_bounds_expr, unsigned_max_expr},
        BinOp, ExprSort, PureExpr,
    };

    use super::build_unsigned_range_preconditions;

    const TEST_CRATE_NAME: &str = "trust_wp_type_invariant_map_test";
    static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

    fn eval_u128(expr: &PureExpr) -> u128 {
        match expr {
            PureExpr::Int(n) => u128::try_from(*n).expect("expected non-negative literal"),
            PureExpr::BinOp(lhs, BinOp::Add, rhs) => eval_u128(lhs) + eval_u128(rhs),
            PureExpr::BinOp(lhs, BinOp::Sub, rhs) => eval_u128(lhs) - eval_u128(rhs),
            PureExpr::BinOp(lhs, BinOp::Mul, rhs) => eval_u128(lhs) * eval_u128(rhs),
            _ => panic!("unsupported expression in eval_u128: {expr:?}"),
        }
    }

    fn eval_i128(expr: &PureExpr) -> i128 {
        match expr {
            PureExpr::Int(n) => i128::from(*n),
            PureExpr::BinOp(lhs, BinOp::Add, rhs) => eval_i128(lhs) + eval_i128(rhs),
            PureExpr::BinOp(lhs, BinOp::Sub, rhs) => eval_i128(lhs) - eval_i128(rhs),
            PureExpr::BinOp(lhs, BinOp::Mul, rhs) => eval_i128(lhs) * eval_i128(rhs),
            _ => panic!("unsupported expression in eval_i128: {expr:?}"),
        }
    }

    fn arithmetic_expr_depth(expr: &PureExpr) -> usize {
        match expr {
            PureExpr::Int(_) => 1,
            PureExpr::BinOp(lhs, BinOp::Add | BinOp::Sub | BinOp::Mul, rhs) => {
                1 + arithmetic_expr_depth(lhs).max(arithmetic_expr_depth(rhs))
            }
            _ => panic!("unsupported expression shape in arithmetic_expr_depth: {expr:?}"),
        }
    }

    #[test]
    fn unsigned_max_expr_matches_u64_max() {
        assert_eq!(eval_u128(&unsigned_max_expr(64)), u64::MAX as u128);
    }

    #[test]
    fn signed_bounds_expr_matches_i64_bounds() {
        let (min_expr, max_expr) = signed_bounds_expr(64);
        assert_eq!(eval_i128(&min_expr), i64::MIN as i128);
        assert_eq!(eval_i128(&max_expr), i64::MAX as i128);
    }

    #[test]
    fn unsigned_max_expr_matches_65_bit_bound() {
        assert_eq!(eval_u128(&unsigned_max_expr(65)), (1_u128 << 65) - 1);
    }

    #[test]
    fn signed_bounds_expr_matches_65_bit_bounds() {
        let (min_expr, max_expr) = signed_bounds_expr(65);
        assert_eq!(eval_i128(&min_expr), -(1_i128 << 64));
        assert_eq!(eval_i128(&max_expr), (1_i128 << 64) - 1);
    }

    #[test]
    fn wide_integer_bound_exprs_stay_shallow() {
        // Keep expression depth well below ay encoding recursion guard (128).
        let unsigned_depth = arithmetic_expr_depth(&unsigned_max_expr(128));
        assert!(
            unsigned_depth <= 32,
            "unsigned max bound expression too deep: {unsigned_depth}"
        );

        let (signed_min, signed_max) = signed_bounds_expr(128);
        let signed_min_depth = arithmetic_expr_depth(&signed_min);
        let signed_max_depth = arithmetic_expr_depth(&signed_max);
        assert!(
            signed_min_depth <= 32,
            "signed min bound expression too deep: {signed_min_depth}"
        );
        assert!(
            signed_max_depth <= 32,
            "signed max bound expression too deep: {signed_max_depth}"
        );
    }

    struct RangePreconditionCallbacks {
        fn_name: String,
        arg_names: Vec<String>,
        preconditions: Option<Vec<PureExpr>>,
        ran: bool,
    }

    impl Callbacks for RangePreconditionCallbacks {
        #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let suffix = format!("::{}", self.fn_name);
            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                let def_path = tcx.def_path_str(def_id);
                if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                    continue;
                }

                self.preconditions = Some(build_unsigned_range_preconditions(
                    tcx,
                    def_id,
                    &self.arg_names,
                ));
                self.ran = true;
                break;
            }
            Compilation::Stop
        }
    }

    fn collect_unsigned_range_preconditions(
        source: &str,
        fn_name: &str,
        arg_names: &[&str],
    ) -> Vec<PureExpr> {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_unsigned_range_{}_{}",
            std::process::id(),
            unique
        ));
        fs::create_dir_all(&temp_dir).expect("create test temp dir");

        let source_path = temp_dir.join("test.rs");
        fs::write(&source_path, source).expect("write test source");

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            TEST_CRATE_NAME.to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = RangePreconditionCallbacks {
            fn_name: fn_name.to_string(),
            arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
            preconditions: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);

        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to locate function `{fn_name}` in rustc callback"
        );
        callbacks
            .preconditions
            .expect("range preconditions should be collected")
    }

    #[test]
    fn unsigned_and_signed_params_get_range_preconditions() {
        let source = r#"
pub fn f(u: usize, i: i32, b: bool) {
    let _ = (u, i, b);
}
"#;
        let preconditions = collect_unsigned_range_preconditions(source, "f", &["u", "i", "b"]);
        assert_eq!(
            preconditions.len(),
            4,
            "expected 4 range constraints (usize + i32), got {preconditions:?}"
        );

        #[allow(clippy::cast_possible_truncation)] // usize width always fits u32
        let usize_bits = (std::mem::size_of::<usize>() as u32) * 8;
        let (i32_min, i32_max) = signed_bounds_expr(32);
        // After #1965, Var nodes carry ExprSort from MIR types.
        let int_sort = Some(ExprSort::Int);
        assert_eq!(
            preconditions[0],
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "u".to_string(),
                    int_sort.clone()
                )))),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0))
            )
        );
        assert_eq!(
            preconditions[1],
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "u".to_string(),
                    int_sort.clone()
                )))),
                BinOp::Le,
                Arc::new(unsigned_max_expr(usize_bits))
            )
        );
        assert_eq!(
            preconditions[2],
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "i".to_string(),
                    int_sort.clone()
                )))),
                BinOp::Ge,
                Arc::new(i32_min)
            )
        );
        assert_eq!(
            preconditions[3],
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "i".to_string(),
                    int_sort
                )))),
                BinOp::Le,
                Arc::new(i32_max)
            )
        );
    }

    #[test]
    fn referenced_integer_params_are_dereferenced_before_range_checks() {
        let source = r#"
pub fn f(u: &u16, i: &mut i8) {
    let _ = (u, i);
}
"#;
        let preconditions = collect_unsigned_range_preconditions(source, "f", &["u", "i"]);
        assert_eq!(
            preconditions.len(),
            4,
            "expected 4 range constraints (&u16 + &mut i8), got {preconditions:?}"
        );

        let (i8_min, i8_max) = signed_bounds_expr(8);
        // After #1965, referenced params carry Ref/MutRef(Int) sort.
        // &u16 → Ref(Int), &mut i8 → MutRef(Int) (#2141).
        let ref_int = Some(ExprSort::Ref(Box::new(ExprSort::Int)));
        let mutref_int = Some(ExprSort::MutRef(Box::new(ExprSort::Int)));
        assert_eq!(
            preconditions[0],
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("u".to_string(), ref_int.clone())
                ))))),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0))
            )
        );
        assert_eq!(
            preconditions[1],
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("u".to_string(), ref_int)
                ))))),
                BinOp::Le,
                Arc::new(unsigned_max_expr(16))
            )
        );
        assert_eq!(
            preconditions[2],
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("i".to_string(), mutref_int.clone())
                ))))),
                BinOp::Ge,
                Arc::new(i8_min)
            )
        );
        assert_eq!(
            preconditions[3],
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("i".to_string(), mutref_int)
                ))))),
                BinOp::Le,
                Arc::new(i8_max)
            )
        );
    }
}
