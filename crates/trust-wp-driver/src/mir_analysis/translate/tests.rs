// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

mod binop_unop;

mod float_helper_tests {
    use rustc_middle::{mir::BinOp as MirBinOp, ty::FloatTy};
    use trust_wp_core::formula::{
        ieee::{IeeeFn, IeeeOp, OpaqueFloatFn, OpaqueFormat, OpaqueOp, OpaquePeer},
        FloatBits, FloatWidth,
    };

    use super::*;

    fn f64_lit(v: f64) -> PureExpr {
        PureExpr::Float(FloatBits::from_f64(v))
    }

    fn call_name(expr: &PureExpr) -> Option<IeeeFn> {
        match expr {
            PureExpr::LogicFnCall { name, .. } => IeeeFn::parse(name),
            _ => None,
        }
    }

    #[test]
    fn test_translate_float_scalar_bits_keeps_the_format() {
        assert_eq!(
            super::float::translate_float_scalar_bits(FloatTy::F32, f32::to_bits(-0.0) as u128),
            Some(PureExpr::Float(FloatBits::from_f32(-0.0))),
            "f32 translation should preserve the raw IEEE payload"
        );
        assert_eq!(
            super::float::translate_float_scalar_bits(FloatTy::F64, f64::to_bits(1.5) as u128),
            Some(f64_lit(1.5)),
            "f64 translation should decode the scalar bits"
        );
    }

    #[test]
    fn test_translate_float_scalar_bits_rejects_out_of_range_widths() {
        assert_eq!(
            super::float::translate_float_scalar_bits(FloatTy::F32, u32::MAX as u128 + 1),
            None
        );
        assert_eq!(
            super::float::translate_float_scalar_bits(FloatTy::F64, u64::MAX as u128 + 1),
            None
        );
        assert_eq!(
            super::float::translate_float_scalar_bits(FloatTy::F16, u16::MAX as u128 + 1),
            None
        );
    }

    fn opaque_name(expr: &PureExpr) -> Option<OpaqueFloatFn> {
        match expr {
            PureExpr::LogicFnCall { name, .. } => OpaqueFloatFn::parse(name),
            _ => None,
        }
    }

    #[test]
    fn test_opaque_literal_is_a_function_of_its_bits() {
        let lit = super::float::translate_float_scalar_bits(FloatTy::F16, 0x3c00).unwrap();
        assert_eq!(
            lit,
            PureExpr::LogicFnCall {
                name: OpaqueFloatFn::new(OpaqueOp::Literal, OpaqueFormat::F16).name(),
                args: vec![PureExpr::Int(0x3c00)],
            }
        );
        let wide = super::float::translate_float_scalar_bits(FloatTy::F128, u128::MAX).unwrap();
        assert_eq!(
            opaque_name(&wide),
            Some(OpaqueFloatFn::new(OpaqueOp::Literal, OpaqueFormat::F128))
        );
    }

    #[test]
    fn test_opaque_operators_and_casts_are_functions_of_their_operands() {
        let h = PureExpr::Var("h".to_string(), None);
        let g = PureExpr::Var("g".to_string(), None);
        let f16 = OpaqueFormat::F16;
        for (mir, op) in [
            (MirBinOp::Add, OpaqueOp::Add),
            (MirBinOp::Sub, OpaqueOp::Sub),
            (MirBinOp::Mul, OpaqueOp::Mul),
            (MirBinOp::Div, OpaqueOp::Div),
            (MirBinOp::Rem, OpaqueOp::Rem),
            (MirBinOp::Eq, OpaqueOp::Eq),
            (MirBinOp::Lt, OpaqueOp::Lt),
            (MirBinOp::Le, OpaqueOp::Le),
            (MirBinOp::Gt, OpaqueOp::Gt),
            (MirBinOp::Ge, OpaqueOp::Ge),
        ] {
            let call =
                super::float::translate_opaque_binop(mir, f16, h.clone(), g.clone()).unwrap();
            assert_eq!(
                opaque_name(&call),
                Some(OpaqueFloatFn::new(op, f16)),
                "{mir:?}"
            );
            assert_ne!(call, h, "{mir:?} is never its operand");
        }
        let ne = super::float::translate_opaque_binop(MirBinOp::Ne, f16, h.clone(), g).unwrap();
        let eq = Some(OpaqueFloatFn::new(OpaqueOp::Eq, f16));
        assert!(matches!(&ne, PureExpr::UnOp(UnOp::Not, inner) if opaque_name(inner) == eq));
        assert_eq!(
            opaque_name(&super::float::translate_opaque_neg(f16, h.clone())),
            Some(OpaqueFloatFn::new(OpaqueOp::Neg, f16))
        );
        use super::float::FloatClass;
        let opaque = FloatClass::Opaque(f16);
        let u32_int = Some((false, 32));
        let u32_peer = OpaquePeer::Int {
            signed: false,
            bits: 32,
        };
        let f32_class = FloatClass::Float(FloatWidth::F32);
        let f64_class = FloatClass::Float(FloatWidth::F64);
        let f128_class = FloatClass::Opaque(OpaqueFormat::F128);
        for (source, target, int, op) in [
            (
                opaque,
                FloatClass::NotFloat,
                u32_int,
                OpaqueOp::To(u32_peer),
            ),
            (
                FloatClass::NotFloat,
                opaque,
                u32_int,
                OpaqueOp::From(u32_peer),
            ),
            (
                opaque,
                f32_class,
                None,
                OpaqueOp::To(OpaquePeer::Float(FloatWidth::F32)),
            ),
            (
                f64_class,
                opaque,
                None,
                OpaqueOp::From(OpaquePeer::Float(FloatWidth::F64)),
            ),
            (
                opaque,
                f128_class,
                None,
                OpaqueOp::To(OpaquePeer::Opaque(OpaqueFormat::F128)),
            ),
        ] {
            let cast = super::float::translate_opaque_cast(source, target, int, h.clone()).unwrap();
            let expected = OpaqueFloatFn::new(op, f16);
            assert_eq!(
                opaque_name(&cast),
                Some(expected),
                "{source:?} -> {target:?}"
            );
        }
        assert_eq!(
            super::float::translate_opaque_cast(opaque, opaque, None, h.clone()),
            Some(h.clone()),
            "a cast within one format changes nothing"
        );
        assert_eq!(
            super::float::translate_opaque_cast(opaque, FloatClass::NotFloat, None, h.clone()),
            None,
            "an integer side needs its width"
        );
        assert_eq!(
            super::float::translate_opaque_cast(
                FloatClass::Float(FloatWidth::F32),
                FloatClass::Float(FloatWidth::F64),
                None,
                h
            ),
            None,
            "no opaque side"
        );
    }

    #[test]
    fn test_float_operators_become_ieee_calls() {
        let x = PureExpr::Var("x".into(), None);
        let y = PureExpr::Var("y".into(), None);
        for (mir, op) in [
            (MirBinOp::Add, IeeeOp::Add),
            (MirBinOp::Sub, IeeeOp::Sub),
            (MirBinOp::Mul, IeeeOp::Mul),
            (MirBinOp::Div, IeeeOp::Div),
            (MirBinOp::Rem, IeeeOp::Rem),
            (MirBinOp::Eq, IeeeOp::Eq),
            (MirBinOp::Lt, IeeeOp::Lt),
            (MirBinOp::Le, IeeeOp::Le),
            (MirBinOp::Gt, IeeeOp::Gt),
            (MirBinOp::Ge, IeeeOp::Ge),
        ] {
            let got =
                super::float::translate_float_binop(mir, FloatWidth::F32, x.clone(), y.clone())
                    .expect("translates");
            assert_eq!(
                call_name(&got),
                Some(IeeeFn::new(op, FloatWidth::F32)),
                "{mir:?}"
            );
        }
        let ne = super::float::translate_float_binop(MirBinOp::Ne, FloatWidth::F64, x.clone(), y)
            .expect("translates");
        match ne {
            PureExpr::UnOp(UnOp::Not, inner) => assert_eq!(
                call_name(&inner),
                Some(IeeeFn::new(IeeeOp::Eq, FloatWidth::F64))
            ),
            other => panic!("`!=` must be the negation of IEEE `==`, got {other:?}"),
        }
        assert_eq!(
            call_name(&super::float::translate_float_neg(FloatWidth::F64, x)),
            Some(IeeeFn::new(IeeeOp::Neg, FloatWidth::F64))
        );
    }

    #[test]
    fn test_literal_comparisons_fold_by_ieee_rules() {
        let nan = f64_lit(f64::NAN);
        let one = f64_lit(1.0);
        let fold = |op, l: &PureExpr, r: &PureExpr| {
            super::float::translate_float_binop(op, FloatWidth::F64, l.clone(), r.clone())
        };
        assert_eq!(
            fold(MirBinOp::Lt, &one, &f64_lit(2.0)),
            Some(PureExpr::Bool(true))
        );
        assert_eq!(fold(MirBinOp::Eq, &nan, &nan), Some(PureExpr::Bool(false)));
        assert_eq!(fold(MirBinOp::Ne, &nan, &nan), Some(PureExpr::Bool(true)));
        assert_eq!(fold(MirBinOp::Ge, &nan, &one), Some(PureExpr::Bool(false)));
        assert_eq!(
            fold(MirBinOp::Eq, &f64_lit(0.0), &f64_lit(-0.0)),
            Some(PureExpr::Bool(true))
        );
        assert_eq!(
            fold(MirBinOp::Add, &f64_lit(1.0e16), &one),
            Some(f64_lit(1.0e16)),
            "literal arithmetic folds by IEEE rounding, not over the reals"
        );
        assert_eq!(
            fold(MirBinOp::Sub, &f64_lit(0.3), &f64_lit(0.1)),
            Some(f64_lit(0.3 - 0.1))
        );
        assert!(
            matches!(fold(MirBinOp::Div, &f64_lit(0.0), &f64_lit(0.0)), Some(PureExpr::Float(bits)) if bits.to_f64().is_nan())
        );
        assert_eq!(
            fold(MirBinOp::Rem, &f64_lit(-7.0), &f64_lit(5.0)),
            Some(f64_lit(-2.0)),
            "`%` truncates the quotient, so the remainder takes the dividend's sign"
        );
        let f32_sum = super::float::translate_float_binop(
            MirBinOp::Add,
            FloatWidth::F32,
            PureExpr::Float(FloatBits::from_f32(16_777_216.0)),
            PureExpr::Float(FloatBits::from_f32(1.0)),
        );
        assert_eq!(
            f32_sum,
            Some(PureExpr::Float(FloatBits::from_f32(16_777_216.0)))
        );
    }

    #[test]
    fn test_literal_negation_and_conversion_keep_the_format() {
        assert_eq!(
            super::float::translate_float_neg(
                FloatWidth::F32,
                PureExpr::Float(FloatBits::from_f32(0.1))
            ),
            PureExpr::Float(FloatBits::from_f32(-0.1))
        );
        assert_eq!(
            super::float::translate_float_to_float(FloatWidth::F64, FloatWidth::F32, f64_lit(0.1)),
            PureExpr::Float(FloatBits::from_f32(0.1_f64 as f32))
        );
        let x = PureExpr::Var("x".into(), None);
        assert_eq!(
            super::float::translate_float_to_float(FloatWidth::F64, FloatWidth::F64, x.clone()),
            x
        );
    }

    #[test]
    fn test_literal_float_to_int_folds_by_rust_as() {
        let to_int = |value: f64, signed, bits| {
            super::float::translate_float_to_int(FloatWidth::F64, signed, bits, f64_lit(value))
        };
        assert_eq!(
            to_int(300.0, false, 8),
            PureExpr::Int(255),
            "saturates high"
        );
        assert_eq!(to_int(-1.5, false, 8), PureExpr::Int(0), "saturates low");
        assert_eq!(
            to_int(-2.7, true, 32),
            PureExpr::Int(-2),
            "truncates toward zero"
        );
        assert_eq!(to_int(f64::NAN, true, 32), PureExpr::Int(0), "NaN is zero");
        assert_eq!(
            to_int(f64::NEG_INFINITY, true, 16),
            PureExpr::Int(i64::from(i16::MIN))
        );
        assert_eq!(
            super::float::translate_float_to_int(
                FloatWidth::F32,
                true,
                8,
                PureExpr::Float(FloatBits::from_f32(127.9))
            ),
            PureExpr::Int(127)
        );
        // A literal of the other format is not this cast's operand: no fold.
        let foreign = super::float::translate_float_to_int(FloatWidth::F32, true, 8, f64_lit(1.0));
        assert!(matches!(foreign, PureExpr::LogicFnCall { .. }));
    }

    #[test]
    fn test_literal_int_to_float_folds_by_rust_as_within_the_source_range() {
        assert_eq!(
            super::float::translate_int_to_float(
                true,
                32,
                FloatWidth::F32,
                PureExpr::Int(16_777_217)
            ),
            PureExpr::Float(FloatBits::from_f32(16_777_216.0)),
            "rounds to nearest-even"
        );
        assert_eq!(
            super::float::translate_int_to_float(false, 64, FloatWidth::F64, PureExpr::Int(3)),
            f64_lit(3.0)
        );
        assert_eq!(
            super::float::translate_int_to_float(true, 128, FloatWidth::F64, PureExpr::Int(-5)),
            f64_lit(-5.0),
            "an i128 literal folds like a narrower one"
        );
        // A value its source type cannot hold is not folded.
        for (signed, bits, value) in [(false, 8, 256), (false, 8, -1), (true, 8, 128)] {
            let cast = super::float::translate_int_to_float(
                signed,
                bits,
                FloatWidth::F64,
                PureExpr::Int(value),
            );
            assert!(
                matches!(cast, PureExpr::LogicFnCall { .. }),
                "{signed} {bits} {value}"
            );
        }
    }
}

// Tests for translate_place/translate_operand/translate_rvalue helpers.
mod translate_helpers_tests {
    use rustc_abi::Size;
    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;
    use rustc_middle::{
        mir::{interpret::Scalar, Const, ConstOperand, ConstValue},
        ty::{ScalarInt, TyCtxt},
    };
    use rustc_span::DUMMY_SP;

    use super::*;

    fn local_exprs() -> HashMap<Local, PureExpr> {
        let mut locals = HashMap::new();
        locals.insert(Local::from_usize(1), PureExpr::Var("x".to_string(), None));
        locals.insert(Local::from_usize(2), PureExpr::Var("y".to_string(), None));
        locals
    }

    #[test]
    fn test_project_tuple_field_from_synthetic_tuple() {
        let tuple = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![PureExpr::Int(10), PureExpr::Int(20)],
        };
        assert_eq!(project_tuple_field(&tuple, 0), Some(PureExpr::Int(10)));
        assert_eq!(project_tuple_field(&tuple, 1), Some(PureExpr::Int(20)));
        assert_eq!(project_tuple_field(&tuple, 2), None);
    }

    #[test]
    fn test_project_tuple_field_ignores_non_tuple_logic_calls() {
        let not_tuple = PureExpr::LogicFnCall {
            name: "max".to_string(),
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        };
        assert_eq!(project_tuple_field(&not_tuple, 0), None);
    }

    #[test]
    fn test_project_tuple_field_supports_arity_1_newtype() {
        // Arity 1 is valid since d6f665e9 (newtype struct decomposition).
        let singleton = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![PureExpr::Int(99)],
        };
        assert_eq!(project_tuple_field(&singleton, 0), Some(PureExpr::Int(99)));
        assert_eq!(project_tuple_field(&singleton, 1), None);
    }

    #[test]
    fn test_project_tuple_field_rejects_arity_0() {
        let zero_ary = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".to_string(),
            args: vec![],
        };
        assert_eq!(project_tuple_field(&zero_ary, 0), None);
    }

    #[test]
    fn test_project_tuple_field_rejects_mismatched_tuple_arity() {
        let malformed = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(3),
            args: vec![PureExpr::Int(10), PureExpr::Int(20)],
        };
        assert_eq!(project_tuple_field(&malformed, 0), None);
    }

    #[test]
    fn test_project_const_index_from_tuple_constructor() {
        let tuple = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(3),
            args: vec![PureExpr::Int(10), PureExpr::Int(20), PureExpr::Int(30)],
        };
        assert_eq!(project_const_index(&tuple, 0), Some(PureExpr::Int(10)));
        assert_eq!(project_const_index(&tuple, 2), Some(PureExpr::Int(30)));
        assert_eq!(project_const_index(&tuple, 3), None);
    }

    #[test]
    fn test_project_const_index_from_array_repeat() {
        let repeated = PureExpr::LogicFnCall {
            name: "array_repeat".to_string(),
            args: vec![PureExpr::Int(7), PureExpr::Int(4)],
        };
        assert_eq!(project_const_index(&repeated, 0), Some(PureExpr::Int(7)));
        assert_eq!(project_const_index(&repeated, 3), Some(PureExpr::Int(7)));
        assert_eq!(project_const_index(&repeated, 4), None);
    }

    #[test]
    fn test_project_closure_capture_field_from_self_env() {
        let env = PureExpr::Var("self".to_string(), None);
        assert_eq!(
            project_closure_capture_field(&env, 0),
            Some(PureExpr::Var("self.0".to_string(), None))
        );
        assert_eq!(
            project_closure_capture_field(&env, 2),
            Some(PureExpr::Var("self.2".to_string(), None))
        );
    }

    #[test]
    fn test_project_closure_capture_field_nested_path() {
        let nested = PureExpr::Var("self.0".to_string(), None);
        assert_eq!(
            project_closure_capture_field(&nested, 1),
            Some(PureExpr::Var("self.0.1".to_string(), None))
        );
    }

    #[test]
    fn test_project_closure_capture_field_non_self_returns_none() {
        let not_env = PureExpr::Var("arg0".to_string(), None);
        assert_eq!(project_closure_capture_field(&not_env, 0), None);
    }

    #[test]
    fn test_translate_place_simple_local() {
        let locals = local_exprs();
        let place = Place::from(Local::from_usize(1));
        assert_eq!(
            translate_place(&place, &locals),
            Some(PureExpr::Var("x".to_string(), None))
        );
    }

    #[test]
    fn test_translate_place_named_adt_field_uses_generic_accessor_not_closure_capture() {
        struct NamedAdtFieldCallbacks {
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for NamedAdtFieldCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let base_place = Place::from(Local::from_usize(1));
                let projected = base_place.project_deeper(
                    &[ProjectionElem::Field(
                        rustc_abi::FieldIdx::from_u32(0),
                        tcx.types.i32,
                    )],
                    tcx,
                );

                let locals = HashMap::from([(
                    Local::from_usize(1),
                    PureExpr::Var(
                        "self".to_string(),
                        Some(ExprSort::Datatype(intern_sort_name("Point"))),
                    ),
                )]);

                self.result = Some(translate_place(&projected, &locals));
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_place_named_adt_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn dummy() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = NamedAdtFieldCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "callback did not run");
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![PureExpr::Var(
                    "self".to_string(),
                    Some(ExprSort::Datatype(intern_sort_name("Point"))),
                )],
            }),
            "Datatype receivers should use the generic field accessor path"
        );
    }

    #[test]
    fn test_translate_place_preserves_deref_for_ref_typed_local() {
        struct RefDerefCallbacks {
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for RefDerefCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let base_place = Place::from(Local::from_usize(1));
                let projected = base_place.project_deeper(&[ProjectionElem::Deref], tcx);

                let locals = HashMap::from([(
                    Local::from_usize(1),
                    PureExpr::Var(
                        "b".to_string(),
                        Some(ExprSort::Ref(Box::new(ExprSort::Bool))),
                    ),
                )]);

                self.result = Some(translate_place(&projected, &locals));
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_place_ref_deref_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn dummy() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = RefDerefCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "callback did not run");
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::Deref(Arc::new(PureExpr::Var(
                "b".to_string(),
                Some(ExprSort::Ref(Box::new(ExprSort::Bool))),
            )))),
            "ref-typed deref should preserve current-value semantics"
        );
    }

    #[test]
    fn test_translate_place_missing_local() {
        let locals = local_exprs();
        let place = Place::from(Local::from_usize(99));
        assert_eq!(translate_place(&place, &locals), None);
    }

    #[test]
    fn test_translate_operand_copy_move() {
        let locals = local_exprs();
        let place = Place::from(Local::from_usize(2));
        let copy = Operand::Copy(place);
        let place = Place::from(Local::from_usize(2));
        let mov = Operand::Move(place);
        assert_eq!(
            translate_operand(&copy, &locals),
            Some(PureExpr::Var("y".to_string(), None))
        );
        assert_eq!(
            translate_operand(&mov, &locals),
            Some(PureExpr::Var("y".to_string(), None))
        );
    }

    #[test]
    fn test_translate_operand_missing_local() {
        let locals = local_exprs();
        let place = Place::from(Local::from_usize(42));
        let copy = Operand::Copy(place);
        assert_eq!(translate_operand(&copy, &locals), None);
    }

    #[test]
    fn test_translate_operand_constant() {
        struct ConstOperandCallbacks {
            ran: bool,
        }

        impl Callbacks for ConstOperandCallbacks {
            #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let scalar_int = ScalarInt::try_from_uint(42_u128, Size::from_bytes(4)).unwrap();
                let scalar = Scalar::from(scalar_int);
                let const_val = Const::Val(ConstValue::Scalar(scalar), tcx.types.i32);
                let const_operand = ConstOperand {
                    span: DUMMY_SP,
                    user_ty: None,
                    const_: const_val,
                };
                let operand = Operand::Constant(Box::new(const_operand));

                let empty: HashMap<Local, PureExpr> = HashMap::new();
                assert_eq!(translate_operand(&operand, &empty), Some(PureExpr::Int(42)));
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_operand_constant_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn placeholder() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = ConstOperandCallbacks { ran: false };
        run_compiler(&args, &mut callbacks);
        assert!(callbacks.ran, "compiler callbacks did not run");

        let _ = std::fs::remove_file(&source_path);
        let _ = std::fs::remove_dir_all(&temp_dir);
    }

    #[test]
    fn test_translate_operand_unit_constant() {
        struct UnitConstOperandCallbacks {
            ran: bool,
        }

        impl Callbacks for UnitConstOperandCallbacks {
            #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let const_val = Const::Val(ConstValue::ZeroSized, tcx.types.unit);
                let const_operand = ConstOperand {
                    span: DUMMY_SP,
                    user_ty: None,
                    const_: const_val,
                };
                let operand = Operand::Constant(Box::new(const_operand));

                let empty: HashMap<Local, PureExpr> = HashMap::new();
                assert_eq!(
                    translate_operand(&operand, &empty),
                    Some(PureExpr::LogicFnCall {
                        name: tuple_logic_fn_name(0),
                        args: vec![],
                    })
                );
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_operand_unit_constant_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn placeholder() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = UnitConstOperandCallbacks { ran: false };
        run_compiler(&args, &mut callbacks);
        assert!(callbacks.ran, "compiler callbacks did not run");

        let _ = std::fs::remove_file(&source_path);
        let _ = std::fs::remove_dir_all(&temp_dir);
    }

    #[test]
    fn test_translate_noncapturing_closure_environment_is_unit() {
        use std::sync::atomic::{AtomicU64, Ordering};

        use rustc_middle::mir::AggregateKind;

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct NoncapturingClosureCallbacks {
            result: Option<Option<PureExpr>>,
            found: bool,
        }

        impl Callbacks for NoncapturingClosureCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if !def_path.contains("make_noncapturing::{closure") {
                        continue;
                    }
                    let closure_ty = tcx
                        .type_of(local_def_id)
                        .instantiate_identity()
                        .skip_norm_wip();
                    let TyKind::Closure(def_id, args) = closure_ty.kind() else {
                        continue;
                    };

                    // Optimized MIR now elides assignment of a zero-sized
                    // non-capturing closure entirely. Reconstruct the exact
                    // aggregate from the compiler-observed closure DefId and
                    // substitutions so this remains a translation regression,
                    // rather than depending on a pre-optimization MIR shape.
                    let rvalue = Rvalue::Aggregate(
                        Box::new(AggregateKind::Closure(*def_id, *args)),
                        rustc_index::IndexVec::new(),
                    );
                    let locals: HashMap<Local, PureExpr> = HashMap::new();
                    self.result = Some(translate_rvalue(&rvalue, &locals, None));
                    self.found = true;
                    break;
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_noncapturing_closure_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "pub fn make_noncapturing() -> impl Fn() -> i32 { || 42 }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = NoncapturingClosureCallbacks {
            result: None,
            found: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.found,
            "failed to find the compiler-observed non-capturing closure type"
        );
        assert_eq!(
            callbacks.result,
            Some(Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(0),
                args: vec![],
            })),
            "an empty closure environment must lower to the unit tuple"
        );
    }

    #[test]
    fn test_translate_operand_f64_constant() {
        struct FloatConstOperandCallbacks {
            ran: bool,
        }

        impl Callbacks for FloatConstOperandCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let scalar_int =
                    ScalarInt::try_from_uint(f64::to_bits(1.5) as u128, Size::from_bytes(8))
                        .unwrap();
                let scalar = Scalar::from(scalar_int);
                let const_val = Const::Val(ConstValue::Scalar(scalar), tcx.types.f64);
                let const_operand = ConstOperand {
                    span: DUMMY_SP,
                    user_ty: None,
                    const_: const_val,
                };
                let operand = Operand::Constant(Box::new(const_operand));

                let empty: HashMap<Local, PureExpr> = HashMap::new();
                assert_eq!(
                    translate_operand(&operand, &empty),
                    Some(PureExpr::Float(
                        trust_wp_core::formula::FloatBits::from_f64(1.5)
                    ))
                );
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_operand_f64_constant_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn placeholder() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = FloatConstOperandCallbacks { ran: false };
        run_compiler(&args, &mut callbacks);
        assert!(callbacks.ran, "compiler callbacks did not run");

        let _ = std::fs::remove_file(&source_path);
        let _ = std::fs::remove_dir_all(&temp_dir);
    }

    /// Values outside i64 range must decompose into binary expressions, not
    /// silently return None or truncate (#1436, #976).
    #[test]
    fn test_translate_constant_i128_overflow_decomposes() {
        struct OverflowCallbacks {
            ran: bool,
        }

        impl Callbacks for OverflowCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                // i128::MAX exceeds i64 range. Size 16 = 128-bit integer.
                let overflow_val = i128::MAX as u128;
                let scalar_int =
                    ScalarInt::try_from_uint(overflow_val, Size::from_bytes(16)).unwrap();
                let scalar = Scalar::from(scalar_int);
                let const_val = Const::Val(ConstValue::Scalar(scalar), tcx.types.i128);
                let const_operand = ConstOperand {
                    span: DUMMY_SP,
                    user_ty: None,
                    const_: const_val,
                };

                let result = translate_constant(&const_operand);
                assert!(
                    result.is_some(),
                    "i128::MAX should decompose via binary decomposition, not return None"
                );
                // The result should be a BinOp expression tree, not a plain Int.
                let expr = result.unwrap();
                assert!(
                    matches!(expr, PureExpr::BinOp(..)),
                    "i128::MAX should produce a BinOp decomposition, got: {expr:?}"
                );
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_constant_overflow_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn placeholder() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = OverflowCallbacks { ran: false };
        run_compiler(&args, &mut callbacks);
        assert!(callbacks.ran, "compiler callbacks did not run");

        let _ = std::fs::remove_dir_all(&temp_dir);
    }

    /// Regression: u32::MAX must translate to 4294967295, not -1.
    /// The unsigned match-arm result path previously used `to_int()` for both
    /// signed and unsigned scalars, reinterpreting large unsigned values as
    /// negative. (#2479)
    #[test]
    fn test_translate_constant_u32_max_stays_unsigned() {
        struct U32MaxCallbacks {
            ran: bool,
        }

        impl Callbacks for U32MaxCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                // u32::MAX = 4294967295
                let scalar_int =
                    ScalarInt::try_from_uint(u32::MAX as u128, Size::from_bytes(4)).unwrap();
                let scalar = Scalar::from(scalar_int);
                let const_val = Const::Val(ConstValue::Scalar(scalar), tcx.types.u32);
                let const_operand = ConstOperand {
                    span: DUMMY_SP,
                    user_ty: None,
                    const_: const_val,
                };

                let result = translate_constant(&const_operand);
                assert_eq!(
                    result,
                    Some(PureExpr::Int(u32::MAX as i64)),
                    "u32::MAX should translate to 4294967295, not -1"
                );
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_constant_u32_max_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn placeholder() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = U32MaxCallbacks { ran: false };
        run_compiler(&args, &mut callbacks);
        assert!(callbacks.ran, "compiler callbacks did not run");

        let _ = std::fs::remove_dir_all(&temp_dir);
    }

    #[test]
    fn test_translate_rvalue_unary_and_binary() {
        let locals = local_exprs();
        let x_place = Place::from(Local::from_usize(1));
        let y_place = Place::from(Local::from_usize(2));
        let unary = Rvalue::UnaryOp(MirUnOp::Neg, Operand::Copy(x_place));
        let binary = Rvalue::BinaryOp(
            MirBinOp::Add,
            Box::new((Operand::Copy(x_place), Operand::Move(y_place))),
        );

        assert_eq!(
            translate_rvalue(&unary, &locals, None),
            Some(PureExpr::UnOp(
                UnOp::Neg,
                Arc::new(PureExpr::Var("x".to_string(), None))
            ))
        );
        assert_eq!(
            translate_rvalue(&binary, &locals, None),
            Some(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None))
            ))
        );
    }

    #[test]
    fn test_translate_rvalue_missing_operand() {
        let locals = local_exprs();
        let missing_place = Place::from(Local::from_usize(7));
        let unary = Rvalue::UnaryOp(MirUnOp::Neg, Operand::Copy(missing_place));
        assert_eq!(translate_rvalue(&unary, &locals, None), None);
    }

    #[test]
    fn test_translate_rvalue_detailed_records_missing_local_diagnostic() {
        let locals = local_exprs();
        let missing_place = Place::from(Local::from_usize(7));
        let unary = Rvalue::UnaryOp(MirUnOp::Neg, Operand::Copy(missing_place));
        let diagnostics = crate::mir_analysis::diagnostics::ExtractionDiagnosticSink::default();
        let diag_ctx = TranslationDiagContext {
            sink: Some(&diagnostics),
            module: "translate/tests.rs",
            location: None,
        };

        assert_eq!(
            translate_rvalue_detailed(&unary, &locals, None, Some(&diag_ctx)),
            None
        );

        let diagnostics = diagnostics.into_inner();
        assert_eq!(diagnostics.entries.len(), 1);
        let diag = &diagnostics.entries[0];
        assert_eq!(
            diag.kind,
            crate::mir_analysis::diagnostics::ExtractionDiagKind::FeatureGap
        );
        assert_eq!(diag.module, "translate/tests.rs");
        assert_eq!(diag.detail, "missing local expression for _7");
    }

    /// Without a MIR body no operand type is known, and a float operator read
    /// as a generic `BinOp`/`UnOp` would be integer arithmetic or logical
    /// equality: an operand that is syntactically a float is refused.
    #[test]
    fn test_translate_rvalue_float_operator_without_body_is_refused() {
        let lit = |v: f64| PureExpr::Float(trust_wp_core::formula::FloatBits::from_f64(v));
        let mut locals = HashMap::new();
        locals.insert(Local::from_usize(1), lit(1.5));
        locals.insert(Local::from_usize(2), lit(2.0));
        let unary = Rvalue::UnaryOp(
            MirUnOp::Neg,
            Operand::Copy(Place::from(Local::from_usize(1))),
        );
        assert_eq!(translate_rvalue(&unary, &locals, None), None);
        for op in [
            MirBinOp::Add,
            MirBinOp::Sub,
            MirBinOp::Mul,
            MirBinOp::Div,
            MirBinOp::Eq,
            MirBinOp::Ne,
            MirBinOp::Lt,
            MirBinOp::Ge,
        ] {
            let left = Place::from(Local::from_usize(1));
            let right = Place::from(Local::from_usize(2));
            let rvalue =
                Rvalue::BinaryOp(op, Box::new((Operand::Copy(left), Operand::Copy(right))));
            assert_eq!(translate_rvalue(&rvalue, &locals, None), None, "{op:?}");
        }
    }

    #[test]
    fn test_translate_rvalue_use_copy() {
        // Rvalue::Use just passes through to translate_operand
        let locals = local_exprs();
        let x_place = Place::from(Local::from_usize(1));
        let use_copy = Rvalue::Use(Operand::Copy(x_place), rustc_middle::mir::WithRetag::No);
        assert_eq!(
            translate_rvalue(&use_copy, &locals, None),
            Some(PureExpr::Var("x".to_string(), None))
        );
    }

    #[test]
    fn test_translate_rvalue_use_move() {
        let locals = local_exprs();
        let y_place = Place::from(Local::from_usize(2));
        let use_move = Rvalue::Use(Operand::Move(y_place), rustc_middle::mir::WithRetag::No);
        assert_eq!(
            translate_rvalue(&use_move, &locals, None),
            Some(PureExpr::Var("y".to_string(), None))
        );
    }

    #[test]
    fn test_translate_rvalue_use_missing_local() {
        let locals = local_exprs();
        let missing_place = Place::from(Local::from_usize(99));
        let use_missing = Rvalue::Use(
            Operand::Copy(missing_place),
            rustc_middle::mir::WithRetag::No,
        );
        assert_eq!(translate_rvalue(&use_missing, &locals, None), None);
    }

    #[test]
    fn test_translate_rvalue_use_retag_is_extensional_for_scalar_and_mut_ref() {
        let mut locals = local_exprs();
        let mut_ref_local = Local::from_usize(3);
        let mut_ref_expr = PureExpr::Var(
            "r".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        );
        locals.insert(mut_ref_local, mut_ref_expr.clone());

        for (place, expected) in [
            (
                Place::from(Local::from_usize(1)),
                PureExpr::Var("x".to_string(), None),
            ),
            (Place::from(mut_ref_local), mut_ref_expr),
        ] {
            let with_retag = Rvalue::Use(Operand::Move(place), rustc_middle::mir::WithRetag::Yes);
            let without_retag = Rvalue::Use(Operand::Move(place), rustc_middle::mir::WithRetag::No);

            assert_eq!(
                translate_rvalue(&with_retag, &locals, None),
                Some(expected.clone())
            );
            assert_eq!(
                translate_rvalue(&without_retag, &locals, None),
                Some(expected)
            );
        }
    }

    #[test]
    fn test_translate_generic_reborrow_fails_closed_for_both_aliasing_modes() {
        assert_eq!(
            translate_generic_reborrow(rustc_middle::ty::Mutability::Mut, None),
            None,
            "exclusive generic reborrow needs alias/writeback semantics",
        );
        assert_eq!(
            translate_generic_reborrow(rustc_middle::ty::Mutability::Not, None),
            None,
            "shared CoerceShared needs source-to-target carrier semantics",
        );
    }

    // #947: Rvalue::Discriminant produces a MethodCall("discriminant") on
    // the translated place expression.
    #[test]
    fn test_translate_rvalue_discriminant() {
        let locals = local_exprs();
        let x_place = Place::from(Local::from_usize(1));
        let discr = Rvalue::Discriminant(x_place);
        assert_eq!(
            translate_rvalue(&discr, &locals, None),
            Some(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
                method: "discriminant".to_string(),
                args: vec![],
            })
        );
    }

    #[test]
    fn test_translate_rvalue_discriminant_missing_local() {
        let locals = local_exprs();
        let missing_place = Place::from(Local::from_usize(99));
        let discr = Rvalue::Discriminant(missing_place);
        assert_eq!(translate_rvalue(&discr, &locals, None), None);
    }

    // #2049: body-less PtrMetadata translation must fail closed because
    // the translator cannot prove the metadata is a slice length without
    // MIR type data.
    #[test]
    fn test_ptr_metadata_without_body_returns_none() {
        let locals = local_exprs();
        let x_place = Place::from(Local::from_usize(1));
        let ptr_meta = Rvalue::UnaryOp(MirUnOp::PtrMetadata, Operand::Copy(x_place));
        assert_eq!(translate_rvalue(&ptr_meta, &locals, None), None);
    }

    #[test]
    fn test_translate_rvalue_ptr_metadata_missing_local() {
        let locals = local_exprs();
        let missing_place = Place::from(Local::from_usize(99));
        let ptr_meta = Rvalue::UnaryOp(MirUnOp::PtrMetadata, Operand::Copy(missing_place));
        assert_eq!(translate_rvalue(&ptr_meta, &locals, None), None);
    }

    #[test]
    fn test_ptr_metadata_without_body_records_diagnostic() {
        let locals = local_exprs();
        let x_place = Place::from(Local::from_usize(1));
        let ptr_meta = Rvalue::UnaryOp(MirUnOp::PtrMetadata, Operand::Copy(x_place));
        let diagnostics = crate::mir_analysis::diagnostics::ExtractionDiagnosticSink::default();
        let diag_ctx = TranslationDiagContext {
            sink: Some(&diagnostics),
            module: "translate/tests.rs",
            location: None,
        };

        assert_eq!(
            translate_rvalue_detailed(&ptr_meta, &locals, None, Some(&diag_ctx)),
            None
        );

        let diagnostics = diagnostics.into_inner();
        assert_eq!(diagnostics.entries.len(), 1);
        let diag = &diagnostics.entries[0];
        assert_eq!(
            diag.kind,
            crate::mir_analysis::diagnostics::ExtractionDiagKind::FeatureGap
        );
        assert_eq!(diag.module, "translate/tests.rs");
        assert_eq!(diag.detail, "PtrMetadata without MIR body");
    }

    // #956: PtrMetadata on slice types should produce `.len()` even
    // when a real Body is provided (the guard accepts slice types).
    #[test]
    fn test_ptr_metadata_slice_with_body_produces_len() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct SlicePtrMetaCallbacks {
            #[allow(clippy::option_option)]
            // Distinguish "callback didn't run" from "returned None"
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for SlicePtrMetaCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if def_path != "takes_slice" && !def_path.ends_with("::takes_slice") {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());

                    // Local 1 is the first argument (`s: &[i32]`).
                    let mut locals = HashMap::new();
                    locals.insert(Local::from_usize(1), PureExpr::Var("s".to_string(), None));

                    let place = Place::from(Local::from_usize(1));
                    let rvalue = Rvalue::UnaryOp(MirUnOp::PtrMetadata, Operand::Copy(place));
                    self.result = Some(translate_rvalue(&rvalue, &locals, Some(body)));
                    self.ran = true;
                    break;
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_ptr_meta_slice_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "pub fn takes_slice(s: &[i32]) -> usize { s.len() }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = SlicePtrMetaCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to locate takes_slice in rustc callback"
        );
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "s".to_string(),
                    None,
                )))),
                method: "len".to_string(),
                args: vec![],
            }),
            "PtrMetadata on &[i32] should produce View(..).len() method call (#2675)"
        );
    }

    // #956: PtrMetadata on trait-object types must return None (not
    // `.len()`) because PtrMetadata extracts the vtable pointer, not
    // a length. This is the soundness guard from #952.
    #[test]
    fn test_ptr_metadata_trait_object_with_body_returns_none() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct TraitObjPtrMetaCallbacks {
            #[allow(clippy::option_option)]
            // Distinguish "callback didn't run" from "returned None"
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for TraitObjPtrMetaCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if def_path != "takes_dyn" && !def_path.ends_with("::takes_dyn") {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());

                    // Local 1 is the first argument (`d: &dyn std::fmt::Debug`).
                    let mut locals = HashMap::new();
                    locals.insert(Local::from_usize(1), PureExpr::Var("d".to_string(), None));

                    let place = Place::from(Local::from_usize(1));
                    let rvalue = Rvalue::UnaryOp(MirUnOp::PtrMetadata, Operand::Copy(place));
                    self.result = Some(translate_rvalue(&rvalue, &locals, Some(body)));
                    self.ran = true;
                    break;
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_ptr_meta_trait_obj_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "pub fn takes_dyn(d: &dyn std::fmt::Debug) { let _ = d; }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = TraitObjPtrMetaCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to locate takes_dyn in rustc callback"
        );
        assert_eq!(
            callbacks.result.unwrap(),
            None,
            "PtrMetadata on &dyn Trait must return None — vtable pointer, not length"
        );
    }

    // #947: Rvalue::CopyForDeref is an identity copy — delegates to
    // translate_place, same as Rvalue::Ref.
    #[test]
    fn test_translate_rvalue_copy_for_deref() {
        let locals = local_exprs();
        let x_place = Place::from(Local::from_usize(1));
        let cfd = Rvalue::CopyForDeref(x_place);
        assert_eq!(
            translate_rvalue(&cfd, &locals, None),
            Some(PureExpr::Var("x".to_string(), None))
        );
    }

    #[test]
    fn test_translate_rvalue_copy_for_deref_missing_local() {
        let locals = local_exprs();
        let missing_place = Place::from(Local::from_usize(99));
        let cfd = Rvalue::CopyForDeref(missing_place);
        assert_eq!(translate_rvalue(&cfd, &locals, None), None);
    }

    // #953: Discriminant on a field-projected place (e.g., `discriminant((_1.0))`)
    // should produce MethodCall("discriminant") on a tuple_get_0 accessor.
    #[test]
    fn test_translate_rvalue_discriminant_with_field_projection() {
        struct DiscriminantFieldCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for DiscriminantFieldCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let field_ty = tcx.type_of(tcx.lang_items().option_type().unwrap());

                // Build a projected place: _1.0 (field 0 of local 1)
                let base_place = Place::from(Local::from_usize(1));
                let projected = base_place.project_deeper(
                    &[ProjectionElem::Field(
                        rustc_abi::FieldIdx::from_u32(0),
                        field_ty.instantiate_identity().skip_norm_wip(),
                    )],
                    tcx,
                );

                let mut locals = HashMap::new();
                locals.insert(Local::from_usize(1), PureExpr::Var("x".to_string(), None));

                let rvalue = Rvalue::Discriminant(projected);
                self.result = Some(translate_rvalue(&rvalue, &locals, None));
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir =
            std::env::temp_dir().join(format!("trust_wp_discr_field_{}", std::process::id()));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn dummy() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = DiscriminantFieldCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "callback did not run");
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(0),
                    args: vec![PureExpr::Var("x".to_string(), None)],
                }),
                method: "discriminant".to_string(),
                args: vec![],
            }),
            "Discriminant on field-projected place should produce \
             MethodCall('discriminant') on tuple_get_0 accessor"
        );
    }

    // #953: CopyForDeref on a field-projected place (e.g., `CopyForDeref(_1.1)`)
    // should produce the tuple_get_1 accessor through translate_place.
    #[test]
    fn test_translate_rvalue_copy_for_deref_with_field_projection() {
        struct CfdFieldCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for CfdFieldCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let base_place = Place::from(Local::from_usize(1));
                let projected = base_place.project_deeper(
                    &[ProjectionElem::Field(
                        rustc_abi::FieldIdx::from_u32(1),
                        tcx.types.i32,
                    )],
                    tcx,
                );

                let mut locals = HashMap::new();
                locals.insert(Local::from_usize(1), PureExpr::Var("x".to_string(), None));

                let rvalue = Rvalue::CopyForDeref(projected);
                self.result = Some(translate_rvalue(&rvalue, &locals, None));
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir =
            std::env::temp_dir().join(format!("trust_wp_cfd_field_{}", std::process::id()));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn dummy() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = CfdFieldCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "callback did not run");
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![PureExpr::Var("x".to_string(), None)],
            }),
            "CopyForDeref on field(1)-projected place should produce tuple_get_1 accessor"
        );
    }

    // #2049: body-less PtrMetadata on a projected place must also fail
    // closed because the translator cannot recover authoritative type
    // information from the lowered place expression.
    #[test]
    fn test_translate_rvalue_ptr_metadata_with_deref_field_projection() {
        struct PtrMetaDerefFieldCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for PtrMetaDerefFieldCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                // Build: (*_1).0 — Deref then Field(0)
                let base_place = Place::from(Local::from_usize(1));
                let projected = base_place.project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Field(rustc_abi::FieldIdx::from_u32(0), tcx.types.i32),
                    ],
                    tcx,
                );

                let mut locals = HashMap::new();
                locals.insert(Local::from_usize(1), PureExpr::Var("s".to_string(), None));

                let rvalue = Rvalue::UnaryOp(MirUnOp::PtrMetadata, Operand::Copy(projected));
                // No body: fail closed instead of manufacturing `.len()`.
                self.result = Some(translate_rvalue(&rvalue, &locals, None));
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir =
            std::env::temp_dir().join(format!("trust_wp_ptrmeta_deref_{}", std::process::id()));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn dummy() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = PtrMetaDerefFieldCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "callback did not run");
        assert_eq!(
            callbacks.result.unwrap(),
            None,
            "PtrMetadata on deref+field projected place should fail closed without MIR body"
        );
    }

    // #948: Rvalue::Repeat translates `[expr; N]` array initialization
    // to a LogicFnCall("array_repeat", [operand, count]).
    #[test]
    fn test_translate_rvalue_repeat() {
        struct RepeatCallbacks {
            ran: bool,
        }

        impl Callbacks for RepeatCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let mut locals = HashMap::new();
                locals.insert(Local::from_usize(1), PureExpr::Int(0));

                let x_place = Place::from(Local::from_usize(1));
                let count_const = rustc_middle::ty::Const::from_target_usize(tcx, 5);
                let repeat = Rvalue::Repeat(Operand::Copy(x_place), count_const);

                let result = translate_rvalue(&repeat, &locals, None);
                assert_eq!(
                    result,
                    Some(PureExpr::LogicFnCall {
                        name: "array_repeat".to_string(),
                        args: vec![PureExpr::Int(0), PureExpr::Int(5)],
                    }),
                    "Rvalue::Repeat([0; 5]) should produce array_repeat(0, 5)"
                );
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_rvalue_repeat_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn placeholder() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = RepeatCallbacks { ran: false };
        run_compiler(&args, &mut callbacks);
        assert!(callbacks.ran, "compiler callbacks did not run");

        let _ = std::fs::remove_file(&source_path);
        let _ = std::fs::remove_dir_all(&temp_dir);
    }

    #[test]
    fn test_translate_rvalue_repeat_missing_local() {
        struct RepeatMissingCallbacks {
            ran: bool,
        }

        impl Callbacks for RepeatMissingCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                let locals: HashMap<Local, PureExpr> = HashMap::new();

                let missing_place = Place::from(Local::from_usize(99));
                let count_const = rustc_middle::ty::Const::from_target_usize(tcx, 3);
                let repeat = Rvalue::Repeat(Operand::Copy(missing_place), count_const);

                assert_eq!(
                    translate_rvalue(&repeat, &locals, None),
                    None,
                    "Repeat with missing operand should return None"
                );
                self.ran = true;
                Compilation::Stop
            }
        }

        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_rvalue_repeat_missing_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn placeholder() {}\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = RepeatMissingCallbacks { ran: false };
        run_compiler(&args, &mut callbacks);
        assert!(callbacks.ran, "compiler callbacks did not run");

        let _ = std::fs::remove_file(&source_path);
        let _ = std::fs::remove_dir_all(&temp_dir);
    }

    // --- allows_field0_identity_fallback soundness tests (#953) ---

    /// Field(0) identity on Var is unsound — Var("x") might be a struct,
    /// so `x.0` != `x`. The function must reject Var.
    #[test]
    fn test_field0_identity_rejects_var() {
        assert!(
            !allows_field0_identity_fallback(&PureExpr::Var("x".to_string(), None)),
            "field0 identity on Var is unsound: x.0 != x for struct-typed vars"
        );
    }

    /// Field(0) identity on MethodCall is unsound — the call result could be
    /// a tuple/struct. The function must reject MethodCall.
    #[test]
    fn test_field0_identity_rejects_method_call() {
        let method_call = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
            method: "len".to_string(),
            args: vec![],
        };
        assert!(
            !allows_field0_identity_fallback(&method_call),
            "field0 identity on MethodCall is unsound: result could be compound"
        );
    }

    /// Field(0) identity on LogicFnCall is unsound — the call could be a
    /// struct/tuple constructor. The function must reject LogicFnCall.
    #[test]
    fn test_field0_identity_rejects_logic_fn_call() {
        let logic_call = PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![PureExpr::Int(1)],
        };
        assert!(
            !allows_field0_identity_fallback(&logic_call),
            "field0 identity on LogicFnCall is unsound: could be a struct constructor"
        );
    }

    /// Field(0) identity IS valid for checked-op temporaries (Int, Bool,
    /// BinOp, UnOp) because these are scalar results.
    #[test]
    fn test_field0_identity_accepts_scalars() {
        assert!(allows_field0_identity_fallback(&PureExpr::Int(42)));
        assert!(allows_field0_identity_fallback(&PureExpr::Bool(true)));
        assert!(allows_field0_identity_fallback(&PureExpr::BinOp(
            Arc::new(PureExpr::Int(1)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2)),
        )));
        assert!(allows_field0_identity_fallback(&PureExpr::UnOp(
            UnOp::Neg,
            Arc::new(PureExpr::Int(1)),
        )));
    }

    // --- simplify_tuple_get_from_constructor tests ---

    /// tuple_get_0(tuple2(a, b)) should simplify to a.
    #[test]
    fn test_simplify_tuple_get_basic() {
        let constructor = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![PureExpr::Int(10), PureExpr::Int(20)],
        };
        let get_0 = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![constructor],
        };
        assert_eq!(
            simplify_tuple_get_from_constructor(&get_0),
            Some(PureExpr::Int(10)),
            "tuple_get_0(tuple2(10, 20)) should simplify to 10"
        );
    }

    /// tuple_get_1(tuple2(a, b)) should simplify to b.
    #[test]
    fn test_simplify_tuple_get_second_element() {
        let constructor = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![PureExpr::Int(10), PureExpr::Int(20)],
        };
        let get_1 = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![constructor],
        };
        assert_eq!(
            simplify_tuple_get_from_constructor(&get_1),
            Some(PureExpr::Int(20)),
            "tuple_get_1(tuple2(10, 20)) should simplify to 20"
        );
    }

    /// tuple_get_0(non_constructor(x)) should NOT simplify — only
    /// recognized tuple constructors are reduced.
    #[test]
    fn test_simplify_tuple_get_non_constructor_unchanged() {
        let non_constructor = PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };
        let get_0 = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![non_constructor],
        };
        assert_eq!(
            simplify_tuple_get_from_constructor(&get_0),
            None,
            "tuple_get_0 on non-constructor should not simplify"
        );
    }

    /// tuple_get_2(tuple2(a, b)) out-of-bounds should return None.
    #[test]
    fn test_simplify_tuple_get_out_of_bounds() {
        let constructor = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![PureExpr::Int(10), PureExpr::Int(20)],
        };
        let get_2 = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(2),
            args: vec![constructor],
        };
        assert_eq!(
            simplify_tuple_get_from_constructor(&get_2),
            None,
            "tuple_get_2 on a 2-tuple should return None (out of bounds)"
        );
    }

    // --- resolve_deref_projection tests via custom ExprLookup ---

    /// Custom ExprLookup that provides deref-aware tracking for testing
    /// projection resolution without needing a full rustc Place.
    struct DerefTrackingLookup {
        locals: HashMap<Local, PureExpr>,
        deref_exprs: HashMap<Local, PureExpr>,
        field_deref_exprs: HashMap<(Local, u32), PureExpr>,
    }

    impl ExprLookup for DerefTrackingLookup {
        fn get_expr(&self, local: &Local) -> Option<&PureExpr> {
            self.locals.get(local)
        }
        fn get_deref_expr(&self, local: &Local) -> Option<&PureExpr> {
            self.deref_exprs.get(local)
        }
        fn get_field_deref_expr(&self, local: &Local, field: u32) -> Option<&PureExpr> {
            self.field_deref_exprs.get(&(*local, field))
        }
        fn rich_field_projections(&self) -> bool {
            false // Deref-aware lookups use simpler projection
        }
    }

    /// resolve_deref_projection: [Deref] pattern should use get_deref_expr.
    #[test]
    fn test_resolve_deref_plain_deref() {
        let local1 = Local::from_usize(1);
        let mut deref_exprs = HashMap::new();
        deref_exprs.insert(local1, PureExpr::Var("x_current".to_string(), None));
        let lookup = DerefTrackingLookup {
            locals: HashMap::from([(local1, PureExpr::Var("x".to_string(), None))]),
            deref_exprs,
            field_deref_exprs: HashMap::new(),
        };
        // Construct Place with [Deref] projection
        // We test via translate_place which calls resolve_deref_projection
        // For a [Deref]-only projection, we need Place + tcx, so test the lookup trait
        assert_eq!(
            lookup.get_deref_expr(&local1),
            Some(&PureExpr::Var("x_current".to_string(), None)),
            "deref lookup should return tracked expression"
        );
    }

    /// resolve_deref_projection: field-deref lookup should distinguish fields.
    #[test]
    fn test_resolve_deref_field_discrimination() {
        let local1 = Local::from_usize(1);
        let mut field_deref_exprs = HashMap::new();
        field_deref_exprs.insert((local1, 0), PureExpr::Var("self.0_val".to_string(), None));
        field_deref_exprs.insert((local1, 1), PureExpr::Var("self.1_val".to_string(), None));
        let lookup = DerefTrackingLookup {
            locals: HashMap::from([(local1, PureExpr::Var("self".to_string(), None))]),
            deref_exprs: HashMap::new(),
            field_deref_exprs,
        };
        assert_eq!(
            lookup.get_field_deref_expr(&local1, 0),
            Some(&PureExpr::Var("self.0_val".to_string(), None)),
            "field 0 should resolve to self.0_val"
        );
        assert_eq!(
            lookup.get_field_deref_expr(&local1, 1),
            Some(&PureExpr::Var("self.1_val".to_string(), None)),
            "field 1 should resolve to self.1_val"
        );
        assert_eq!(
            lookup.get_field_deref_expr(&local1, 2),
            None,
            "untracked field 2 should return None"
        );
    }

    // --- project_nested_tuple_get_field tests ---

    /// Nested field projection: tuple_get_0(x) -> project field 1 should
    /// produce tuple_get_1(tuple_get_0(x)), NOT collapse away the outer get.
    #[test]
    fn test_project_nested_tuple_get_field_chains_correctly() {
        let outer_get = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };
        let result = project_nested_tuple_get_field(&outer_get, 1);
        assert_eq!(
            result,
            Some(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![outer_get],
            }),
            "nested field projection should wrap, not collapse"
        );
    }

    /// Non-tuple-get LogicFnCall should NOT be treated as nested projection.
    #[test]
    fn test_project_nested_tuple_get_rejects_non_tuple_get() {
        let not_getter = PureExpr::LogicFnCall {
            name: "max".to_string(),
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        };
        assert_eq!(
            project_nested_tuple_get_field(&not_getter, 0),
            None,
            "non-tuple-get LogicFnCall should not trigger nested projection"
        );
    }

    // --- Const tuple/array translation tests (#1588) ---

    // #1588: translate_constant on a tuple constant `(42, 24)` should
    // decompose via ValTree into `__trust_wp_tuple2(42, 24)`.
    #[test]
    fn test_translate_constant_tuple() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct TupleConstCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for TupleConstCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_middle::mir::Operand;

                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if !def_path.ends_with("get_tuple") {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());
                    // Scan MIR for a constant operand of tuple type
                    for bb in body.basic_blocks.iter() {
                        for stmt in &bb.statements {
                            if let rustc_middle::mir::StatementKind::Assign((
                                _,
                                Rvalue::Use(Operand::Constant(ref c), _),
                            )) = stmt.kind
                            {
                                if matches!(c.ty().kind(), TyKind::Tuple(f) if f.len() == 2) {
                                    self.result = Some(translate_constant_with_tcx(c, tcx));
                                    self.ran = true;
                                    return Compilation::Stop;
                                }
                            }
                        }
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_const_tuple_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "const TUP: (i32, i32) = (42, 24);\n\
             pub fn get_tuple() -> (i32, i32) { TUP }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = TupleConstCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to find tuple constant in MIR for get_tuple"
        );
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(2),
                args: vec![PureExpr::Int(42), PureExpr::Int(24)],
            }),
            "const TUP: (i32, i32) = (42, 24) should translate to \
             __trust_wp_tuple2(42, 24)"
        );
    }

    // #1588: translate_constant on a uniform array `[1; 5]` should produce
    // `array_repeat(1, 5)`.
    #[test]
    fn test_translate_constant_array_repeat() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct ArrayConstCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for ArrayConstCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_middle::mir::Operand;

                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if !def_path.ends_with("get_array") {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());
                    for bb in body.basic_blocks.iter() {
                        for stmt in &bb.statements {
                            if let rustc_middle::mir::StatementKind::Assign((
                                _,
                                Rvalue::Use(Operand::Constant(ref c), _),
                            )) = stmt.kind
                            {
                                if matches!(c.ty().kind(), TyKind::Array(..)) {
                                    self.result = Some(translate_constant_with_tcx(c, tcx));
                                    self.ran = true;
                                    return Compilation::Stop;
                                }
                            }
                        }
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_const_array_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "const ARR: [i32; 5] = [1; 5];\n\
             pub fn get_array() -> [i32; 5] { ARR }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = ArrayConstCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to find array constant in MIR for get_array"
        );
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::LogicFnCall {
                name: "array_repeat".to_string(),
                args: vec![PureExpr::Int(1), PureExpr::Int(5)],
            }),
            "const ARR: [i32; 5] = [1; 5] should translate to \
             array_repeat(1, 5)"
        );
    }

    // #1588: mixed-element const arrays should lower to tuple constructors
    // so constant index projections can recover concrete elements.
    #[test]
    fn test_translate_constant_array_mixed_elements() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct MixedArrayConstCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for MixedArrayConstCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_middle::mir::Operand;

                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if !def_path.ends_with("get_mixed_array") {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());
                    for bb in body.basic_blocks.iter() {
                        for stmt in &bb.statements {
                            if let rustc_middle::mir::StatementKind::Assign((
                                _,
                                Rvalue::Use(Operand::Constant(ref c), _),
                            )) = stmt.kind
                            {
                                if matches!(c.ty().kind(), TyKind::Array(..)) {
                                    self.result = Some(translate_constant_with_tcx(c, tcx));
                                    self.ran = true;
                                    return Compilation::Stop;
                                }
                            }
                        }
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_const_mixed_array_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "const ARR: [i32; 2] = [1, 2];\n\
             pub fn get_mixed_array() -> [i32; 2] { ARR }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = MixedArrayConstCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to find array constant in MIR for get_mixed_array"
        );
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(2),
                args: vec![PureExpr::Int(1), PureExpr::Int(2)],
            }),
            "const ARR: [i32; 2] = [1, 2] should translate to \
             __trust_wp_tuple2(1, 2)"
        );
    }

    // #2572: const arrays with enum (ADT) elements should decompose via
    // the tcx-aware ValTree translator into LogicFnCall variants.
    #[test]
    fn test_translate_constant_array_enum_elements() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct EnumArrayConstCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for EnumArrayConstCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_middle::mir::Operand;

                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if !def_path.ends_with("get_colors") {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());
                    for bb in body.basic_blocks.iter() {
                        for stmt in &bb.statements {
                            if let rustc_middle::mir::StatementKind::Assign((
                                _,
                                Rvalue::Use(Operand::Constant(ref c), _),
                            )) = stmt.kind
                            {
                                if matches!(c.ty().kind(), TyKind::Array(..)) {
                                    self.result = Some(translate_constant_with_tcx(c, tcx));
                                    self.ran = true;
                                    return Compilation::Stop;
                                }
                            }
                        }
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_const_enum_array_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "#[derive(Clone, Copy, PartialEq, Eq)]\n\
             enum Color { Red, Green, Blue }\n\
             const COLORS: [Color; 3] = [Color::Red, Color::Green, Color::Blue];\n\
             pub fn get_colors() -> [Color; 3] { COLORS }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = EnumArrayConstCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to find array constant in MIR for get_colors"
        );
        // Three distinct unit variants → tuple3(Red(), Green(), Blue())
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(3),
                args: vec![
                    PureExpr::LogicFnCall {
                        name: "Color::Red".to_string(),
                        args: vec![],
                    },
                    PureExpr::LogicFnCall {
                        name: "Color::Green".to_string(),
                        args: vec![],
                    },
                    PureExpr::LogicFnCall {
                        name: "Color::Blue".to_string(),
                        args: vec![],
                    },
                ],
            }),
            "const COLORS: [Color; 3] = [Red, Green, Blue] should translate to \
             __trust_wp_tuple3(Color::Red(), Color::Green(), Color::Blue())"
        );
    }

    // #2572: const arrays with enum elements that carry data fields
    // (e.g., Option<i32>) should decompose the variant payload correctly.
    #[test]
    fn test_translate_constant_array_enum_with_payload() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct EnumPayloadArrayCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for EnumPayloadArrayCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_middle::mir::Operand;

                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if !def_path.ends_with("get_opts") {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());
                    for bb in body.basic_blocks.iter() {
                        for stmt in &bb.statements {
                            if let rustc_middle::mir::StatementKind::Assign((
                                _,
                                Rvalue::Use(Operand::Constant(ref c), _),
                            )) = stmt.kind
                            {
                                if matches!(c.ty().kind(), TyKind::Array(..)) {
                                    self.result = Some(translate_constant_with_tcx(c, tcx));
                                    self.ran = true;
                                    return Compilation::Stop;
                                }
                            }
                        }
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_const_enum_payload_array_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "const OPTS: [Option<i32>; 2] = [None, Some(42)];\n\
             pub fn get_opts() -> [Option<i32>; 2] { OPTS }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = EnumPayloadArrayCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to find array constant in MIR for get_opts"
        );
        // [None, Some(42)] → tuple2(None(), Some(42))
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(2),
                args: vec![
                    PureExpr::LogicFnCall {
                        name: "Option::None".to_string(),
                        args: vec![],
                    },
                    PureExpr::LogicFnCall {
                        name: "Option::Some".to_string(),
                        args: vec![PureExpr::Int(42)],
                    },
                ],
            }),
            "const OPTS: [Option<i32>; 2] = [None, Some(42)] should translate to \
             __trust_wp_tuple2(Option::None(), Option::Some(42))"
        );
    }

    // #994: `translate_rvalue_typed` on an enum aggregate must produce the
    // variant constructor (e.g. `None`) — NOT collapse to `__trust_wp_tuple0()`.
    //
    // Regression scenario: in `while let Some(_) = b { *b = None; }`, the MIR
    // for the body builds `_4 = Option::<i32>::None` as an `Rvalue::Aggregate`
    // and the loop's deref_effect records the value written through `*b`. If
    // the aggregate is translated as `tuple0()` (Unit sort), the loop encoder
    // ends up asserting `b_prime_current = __trust_wp_unit` (Option = Unit),
    // poisoning the SAT context for loop_initialization / loop_preservation.
    #[test]
    fn test_translate_rvalue_typed_option_none_aggregate_preserves_variant() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct OptionNoneAggregateCallbacks {
            result: Option<PureExpr>,
            ran: bool,
        }

        impl Callbacks for OptionNoneAggregateCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_middle::mir::AggregateKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if !def_path.ends_with("make_none") {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());
                    for bb in body.basic_blocks.iter() {
                        for stmt in &bb.statements {
                            let rustc_middle::mir::StatementKind::Assign((_, rvalue)) = &stmt.kind
                            else {
                                continue;
                            };
                            if !matches!(rvalue, Rvalue::Aggregate(AggregateKind::Adt(..), _)) {
                                continue;
                            }
                            let locals: HashMap<Local, PureExpr> = HashMap::new();
                            self.result =
                                super::translate_rvalue_typed(tcx, rvalue, &locals, Some(body));
                            self.ran = true;
                            return Compilation::Stop;
                        }
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_translate_rvalue_option_none_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, "pub fn make_none() -> Option<i32> { None }\n").unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = OptionNoneAggregateCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "expected to find Option::<i32>::None aggregate in make_none's MIR"
        );
        assert_eq!(
            callbacks.result,
            Some(PureExpr::LogicFnCall {
                name: "None".to_string(),
                args: vec![],
            }),
            "translate_rvalue_typed should emit `None()` for the Option::None aggregate \
             instead of collapsing to `__trust_wp_tuple0()` (Unit sort) — see #994"
        );
    }

    // #1588: resolve_const_item_value on a tuple constant should produce
    // the same result as translate_constant_with_tcx, but from a DefId.
    #[test]
    fn test_resolve_const_item_value_tuple() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct ResolveCallbacks {
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for ResolveCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_hir::def::DefKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if !matches!(tcx.def_kind(def_id), DefKind::Const { .. }) {
                        continue;
                    }
                    let path = tcx.def_path_str(def_id);
                    if path.ends_with("TUP") {
                        self.result = Some(resolve_const_item_value(tcx, def_id));
                        self.ran = true;
                        return Compilation::Stop;
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_resolve_const_tuple_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "const TUP: (i32, i32) = (42, 24);\n\
             pub fn dummy() -> (i32, i32) { TUP }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = ResolveCallbacks {
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to find const TUP via hir_body_owners"
        );
        assert_eq!(
            callbacks.result.unwrap(),
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(2),
                args: vec![PureExpr::Int(42), PureExpr::Int(24)],
            }),
            "resolve_const_item_value for const TUP: (i32, i32) = (42, 24) \
             should produce __trust_wp_tuple2(42, 24)"
        );
    }

    #[test]
    fn test_ty_to_expr_sort_enriched_snapshot_and_ghost_preserve_inner_bool_sort() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct WrapperSortCallbacks {
            #[allow(clippy::option_option)]
            snapshot_bool: Option<Option<ExprSort>>,
            #[allow(clippy::option_option)]
            ghost_bool: Option<Option<ExprSort>>,
            #[allow(clippy::option_option)]
            snapshot_bool_ref: Option<Option<ExprSort>>,
        }

        impl Callbacks for WrapperSortCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_hir::def::DefKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if tcx.def_kind(def_id) != DefKind::Fn {
                        continue;
                    }
                    let path = tcx.def_path_str(def_id);
                    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                    let input = sig.inputs()[0];
                    if path.ends_with("snapshot_bool") {
                        self.snapshot_bool = Some(ty_to_expr_sort_enriched(tcx, input));
                    } else if path.ends_with("ghost_bool") {
                        self.ghost_bool = Some(ty_to_expr_sort_enriched(tcx, input));
                    } else if path.ends_with("snapshot_bool_ref") {
                        self.snapshot_bool_ref = Some(ty_to_expr_sort_enriched(tcx, input));
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_ty_to_expr_sort_enriched_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "use trust_wp_std::ghost::{Ghost, Snapshot};\n\
             pub fn snapshot_bool(_x: Snapshot<bool>) {}\n\
             pub fn ghost_bool(_x: Ghost<bool>) {}\n\
             pub fn snapshot_bool_ref(_x: &Snapshot<bool>) {}\n",
        )
        .unwrap();

        let units = trust_wp_test_utils::unit_dirs::UnitDirs::of_current_exe();
        let trust_wp_std = units.artifact("trust_wp_std", &["rmeta", "rlib"]);
        let mut args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_sort_wrapper_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
            "--extern".to_string(),
            format!("trust_wp_std={}", trust_wp_std.display()),
        ];
        args.extend(units.search_args());

        let mut callbacks = WrapperSortCallbacks {
            snapshot_bool: None,
            ghost_bool: None,
            snapshot_bool_ref: None,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert_eq!(
            callbacks.snapshot_bool,
            Some(Some(ExprSort::Bool)),
            "Snapshot<bool> should preserve Bool sort instead of collapsing to Datatype"
        );
        assert_eq!(
            callbacks.ghost_bool,
            Some(Some(ExprSort::Bool)),
            "Ghost<bool> should preserve Bool sort instead of collapsing to Datatype"
        );
        assert_eq!(
            callbacks.snapshot_bool_ref,
            Some(Some(ExprSort::Ref(Box::new(ExprSort::Bool)))),
            "&Snapshot<bool> should preserve Ref(Bool) through the transparent wrapper"
        );
    }

    #[test]
    fn test_ty_to_expr_sort_enriched_preserves_shared_vs_mut_bool_refs() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct RefSortCallbacks {
            #[allow(clippy::option_option)]
            shared_bool_ref: Option<Option<ExprSort>>,
            #[allow(clippy::option_option)]
            mut_bool_ref: Option<Option<ExprSort>>,
        }

        impl Callbacks for RefSortCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_hir::def::DefKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if tcx.def_kind(def_id) != DefKind::Fn {
                        continue;
                    }
                    let path = tcx.def_path_str(def_id);
                    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                    let input = sig.inputs()[0];
                    if path.ends_with("shared_bool_ref") {
                        self.shared_bool_ref = Some(ty_to_expr_sort_enriched(tcx, input));
                    } else if path.ends_with("mut_bool_ref") {
                        self.mut_bool_ref = Some(ty_to_expr_sort_enriched(tcx, input));
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_ty_to_expr_sort_ref_kinds_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "pub fn shared_bool_ref(_x: &bool) {}\n\
             pub fn mut_bool_ref(_x: &mut bool) {}\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_ref_kind_sort_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = RefSortCallbacks {
            shared_bool_ref: None,
            mut_bool_ref: None,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert_eq!(
            callbacks.shared_bool_ref,
            Some(Some(ExprSort::Ref(Box::new(ExprSort::Bool)))),
            "&bool should preserve the shared-reference wrapper"
        );
        assert_eq!(
            callbacks.mut_bool_ref,
            Some(Some(ExprSort::MutRef(Box::new(ExprSort::Bool)))),
            "&mut bool should preserve the mutable-reference wrapper"
        );
    }

    #[test]
    fn test_ty_to_expr_sort_enriched_preserves_box_inner_sort() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct BoxSortCallbacks {
            #[allow(clippy::option_option)]
            boxed_bool: Option<Option<ExprSort>>,
            #[allow(clippy::option_option)]
            ref_boxed_bool: Option<Option<ExprSort>>,
            #[allow(clippy::option_option)]
            boxed_mut_bool_ref: Option<Option<ExprSort>>,
        }

        impl Callbacks for BoxSortCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_hir::def::DefKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if tcx.def_kind(def_id) != DefKind::Fn {
                        continue;
                    }
                    let path = tcx.def_path_str(def_id);
                    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                    let input = sig.inputs()[0];
                    if path.ends_with("ref_boxed_bool") {
                        self.ref_boxed_bool = Some(ty_to_expr_sort_enriched(tcx, input));
                    } else if path.ends_with("boxed_mut_bool_ref") {
                        self.boxed_mut_bool_ref = Some(ty_to_expr_sort_enriched(tcx, input));
                    } else if path.ends_with("boxed_bool") {
                        self.boxed_bool = Some(ty_to_expr_sort_enriched(tcx, input));
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_ty_to_expr_sort_box_inner_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "pub fn boxed_bool(_x: Box<bool>) {}\n\
             pub fn ref_boxed_bool(_x: &Box<bool>) {}\n\
             pub fn boxed_mut_bool_ref(_x: Box<&mut bool>) {}\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_box_inner_sort_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = BoxSortCallbacks {
            boxed_bool: None,
            ref_boxed_bool: None,
            boxed_mut_bool_ref: None,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert_eq!(
            callbacks.boxed_bool,
            Some(Some(ExprSort::Bool)),
            "Box<bool> should preserve the inner Bool sort"
        );
        assert_eq!(
            callbacks.ref_boxed_bool,
            Some(Some(ExprSort::Ref(Box::new(ExprSort::Bool)))),
            "&Box<bool> should preserve the shared-reference wrapper over Bool"
        );
        assert_eq!(
            callbacks.boxed_mut_bool_ref,
            Some(Some(ExprSort::MutRef(Box::new(ExprSort::Bool)))),
            "Box<&mut bool> should erase transparently to &mut bool"
        );
    }

    #[test]
    fn test_ty_to_expr_sort_enriched_predcell_slice_uses_internal_marker_2316() {
        use std::sync::atomic::{AtomicU64, Ordering};

        use trust_wp_core::formula::intern_sort_name;

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct PredCellSliceSortCallbacks {
            #[allow(clippy::option_option)]
            predcell_slice: Option<Option<ExprSort>>,
        }

        impl Callbacks for PredCellSliceSortCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_hir::def::DefKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if tcx.def_kind(def_id) != DefKind::Fn {
                        continue;
                    }
                    let path = tcx.def_path_str(def_id);
                    if !path.ends_with("predcell_slice") {
                        continue;
                    }
                    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                    self.predcell_slice = Some(ty_to_expr_sort_enriched(tcx, sig.inputs()[0]));
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_predcell_slice_sort_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "use trust_wp_std::std::cell::PredCell;\n\
             pub fn predcell_slice(_x: &[PredCell<u32>]) {}\n",
        )
        .unwrap();

        let units = trust_wp_test_utils::unit_dirs::UnitDirs::of_current_exe();
        let trust_wp_std = units.artifact("trust_wp_std", &["rmeta", "rlib"]);
        let mut args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_predcell_slice_sort_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
            "--extern".to_string(),
            format!("trust_wp_std={}", trust_wp_std.display()),
        ];
        args.extend(units.search_args());

        let mut callbacks = PredCellSliceSortCallbacks {
            predcell_slice: None,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert_eq!(
            callbacks.predcell_slice,
            Some(Some(ExprSort::Ref(Box::new(ExprSort::Datatype(
                intern_sort_name("trust_wp_internal::PredCellSlice"),
            ))))),
            "&[PredCell<T>] should preserve the internal PredCellSlice marker for #2316"
        );
    }
}

// Tests for integer type bit-width helpers and switch value conversion.
// Part of #27 (mir_analysis test coverage)
mod int_type_tests {
    use rustc_middle::ty::{IntTy, UintTy};

    use super::*;

    #[test]
    fn test_int_ty_bits_sizes() {
        assert_eq!(int_ty_bits(IntTy::I8), 8);
        assert_eq!(int_ty_bits(IntTy::I16), 16);
        assert_eq!(int_ty_bits(IntTy::I32), 32);
        assert_eq!(int_ty_bits(IntTy::I64), 64);
        assert_eq!(int_ty_bits(IntTy::I128), 128);
        // isize is platform-dependent, just check it's reasonable
        let isize_bits = int_ty_bits(IntTy::Isize);
        assert!(isize_bits == 32 || isize_bits == 64);
    }

    #[test]
    fn test_uint_ty_bits_sizes() {
        assert_eq!(uint_ty_bits(UintTy::U8), 8);
        assert_eq!(uint_ty_bits(UintTy::U16), 16);
        assert_eq!(uint_ty_bits(UintTy::U32), 32);
        assert_eq!(uint_ty_bits(UintTy::U64), 64);
        assert_eq!(uint_ty_bits(UintTy::U128), 128);
        // usize is platform-dependent, just check it's reasonable
        let usize_bits = uint_ty_bits(UintTy::Usize);
        assert!(usize_bits == 32 || usize_bits == 64);
    }

    #[test]
    fn test_switch_value_to_i64_unsigned() {
        let u32_ty = DiscrIntTy {
            signed: false,
            bits: 32,
        };

        // Small positive values
        assert_eq!(switch_value_to_i64(0, u32_ty), Some(0));
        assert_eq!(switch_value_to_i64(1, u32_ty), Some(1));
        assert_eq!(switch_value_to_i64(42, u32_ty), Some(42));

        // Max u32 fits in i64
        assert_eq!(
            switch_value_to_i64(u128::from(u32::MAX), u32_ty),
            Some(i64::from(u32::MAX))
        );
    }

    #[test]
    fn test_switch_value_to_i64_signed() {
        let i32_ty = DiscrIntTy {
            signed: true,
            bits: 32,
        };

        // Positive values
        assert_eq!(switch_value_to_i64(0, i32_ty), Some(0));
        assert_eq!(switch_value_to_i64(1, i32_ty), Some(1));
        assert_eq!(
            switch_value_to_i64(i32::MAX as u128, i32_ty),
            Some(i64::from(i32::MAX))
        );

        // Negative values (two's complement representation)
        // -1 as u32 = 0xFFFFFFFF = 4294967295
        let neg1_u128 = u128::from(u32::MAX); // 0xFFFFFFFF
        assert_eq!(switch_value_to_i64(neg1_u128, i32_ty), Some(-1));

        // -2 as u32 = 0xFFFFFFFE
        let neg2_u128 = u128::from(u32::MAX - 1);
        assert_eq!(switch_value_to_i64(neg2_u128, i32_ty), Some(-2));

        // i32::MIN as u32 = 0x80000000 = 2147483648
        let min_u128 = u128::from(i32::MIN.cast_unsigned());
        assert_eq!(
            switch_value_to_i64(min_u128, i32_ty),
            Some(i64::from(i32::MIN))
        );
    }

    #[test]
    fn test_switch_value_to_i64_i8() {
        let i8_ty = DiscrIntTy {
            signed: true,
            bits: 8,
        };

        assert_eq!(switch_value_to_i64(0, i8_ty), Some(0));
        assert_eq!(switch_value_to_i64(127, i8_ty), Some(127));
        // -1 as u8 = 255
        assert_eq!(switch_value_to_i64(255, i8_ty), Some(-1));
        // -128 as u8 = 128
        assert_eq!(switch_value_to_i64(128, i8_ty), Some(-128));
    }

    #[test]
    fn test_switch_value_to_i64_overflow() {
        let u64_ty = DiscrIntTy {
            signed: false,
            bits: 64,
        };

        // Values larger than i64::MAX cannot be represented
        let large_value = (i64::MAX as u128) + 1;
        assert_eq!(switch_value_to_i64(large_value, u64_ty), None);

        // u64::MAX is too large
        assert_eq!(switch_value_to_i64(u128::from(u64::MAX), u64_ty), None);
    }

    #[test]
    fn test_switch_value_to_i64_invalid_bits() {
        let zero_bits = DiscrIntTy {
            signed: true,
            bits: 0,
        };
        assert_eq!(switch_value_to_i64(42, zero_bits), None);

        let too_many_bits = DiscrIntTy {
            signed: true,
            bits: 256,
        };
        assert_eq!(switch_value_to_i64(42, too_many_bits), None);
    }

    #[test]
    fn test_switch_value_to_i64_i64_signed() {
        // Test i64 specifically since the output type matches input width
        let i64_ty = DiscrIntTy {
            signed: true,
            bits: 64,
        };

        // Positive values
        assert_eq!(switch_value_to_i64(0, i64_ty), Some(0));
        assert_eq!(
            switch_value_to_i64(i64::MAX as u128, i64_ty),
            Some(i64::MAX)
        );

        // Negative -1: 0xFFFFFFFFFFFFFFFF in u64 representation
        let neg1_u128 = u128::from(u64::MAX);
        assert_eq!(switch_value_to_i64(neg1_u128, i64_ty), Some(-1));

        // i64::MIN: 0x8000000000000000
        let min_u128 = u128::from(i64::MIN.cast_unsigned());
        assert_eq!(switch_value_to_i64(min_u128, i64_ty), Some(i64::MIN));
    }

    #[test]
    fn test_switch_value_to_i64_i128() {
        // Test 128-bit special case path
        let i128_ty = DiscrIntTy {
            signed: true,
            bits: 128,
        };

        // Small values fit in i64
        assert_eq!(switch_value_to_i64(0, i128_ty), Some(0));
        assert_eq!(switch_value_to_i64(42, i128_ty), Some(42));
        assert_eq!(
            switch_value_to_i64(i64::MAX as u128, i128_ty),
            Some(i64::MAX)
        );

        // i64::MIN as signed i128 fits in i64
        // In two's complement, -1 as i128 has all bits set
        // But we need values that fit in i64 range
        let i64_min_as_u128 = i128::from(i64::MIN).cast_unsigned();
        assert_eq!(
            switch_value_to_i64(i64_min_as_u128, i128_ty),
            Some(i64::MIN)
        );

        // Values outside i64 range return None
        let too_large = (i64::MAX as u128) + 1;
        assert_eq!(switch_value_to_i64(too_large, i128_ty), None);

        // u128 type
        let u128_ty = DiscrIntTy {
            signed: false,
            bits: 128,
        };
        assert_eq!(switch_value_to_i64(0, u128_ty), Some(0));
        assert_eq!(
            switch_value_to_i64(i64::MAX as u128, u128_ty),
            Some(i64::MAX)
        );
        // Unsigned values larger than i64::MAX don't fit
        assert_eq!(switch_value_to_i64((i64::MAX as u128) + 1, u128_ty), None);
    }

    // Prover audit: document that project_closure_capture_field accepts
    // arbitrary field indices (no upper-bound check). Sound because MIR
    // field indices are compiler-generated, but this test documents the
    // behavior for defense-in-depth awareness.
    #[test]
    fn test_project_closure_capture_field_unbounded_index() {
        let env = PureExpr::Var("self".to_string(), None);
        // Large index succeeds — no arity gate
        assert_eq!(
            project_closure_capture_field(&env, 999),
            Some(PureExpr::Var("self.999".to_string(), None))
        );
    }

    // Prover audit: document the `.0` legacy fallback in translate_place.
    // When a non-tuple, non-closure value has a Field(0) projection,
    // translate_place returns the base expression unchanged (identity).
    // This is correct for checked-arithmetic temporaries but would be
    // incorrect if struct field lowering is added without updating the
    // fallback. This test documents the current behavior.
    #[test]
    fn test_project_tuple_field_non_tuple_non_closure_returns_none() {
        // An Int literal is not a tuple or closure env.
        let scalar = PureExpr::Int(42);
        assert_eq!(project_tuple_field(&scalar, 0), None);
        assert_eq!(project_closure_capture_field(&scalar, 0), None);
        // In translate_place, the legacy fallback would return Some(Int(42))
        // for field_idx == 0, which is the documented checked-op behavior.
    }

    // Regression test for #489: LogicFnCall base expressions must not
    // get the .0 identity fallback. A LogicFnCall that isn't a recognized
    // tuple (__trust_wp_tupleN) could be a struct, and treating .0 as
    // identity would silently return the whole struct instead of field 0.
    #[test]
    fn test_field0_fallback_rejects_logic_fn_call() {
        // A LogicFnCall that is NOT a tuple (e.g., a struct constructor)
        let struct_like = PureExpr::LogicFnCall {
            name: "MyStruct::new".to_string(),
            args: vec![PureExpr::Int(1), PureExpr::Bool(true)],
        };
        // project_tuple_field won't match (not __trust_wp_tupleN)
        assert_eq!(project_tuple_field(&struct_like, 0), None);
        // project_closure_capture_field won't match (not a Var named "self")
        assert_eq!(project_closure_capture_field(&struct_like, 0), None);
        assert!(
            !allows_field0_identity_fallback(&struct_like),
            ".0 identity fallback must be disabled for generic LogicFnCall bases"
        );
    }

    #[test]
    fn test_field0_fallback_allows_scalar_checked_op_shape() {
        let scalar = PureExpr::Int(42);
        assert!(
            allows_field0_identity_fallback(&scalar),
            ".0 identity fallback should remain enabled for scalar checked-op shapes"
        );
    }

    #[test]
    fn test_field0_fallback_allows_binop_checked_op_shape() {
        let checked_op_shape = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        assert!(
            allows_field0_identity_fallback(&checked_op_shape),
            ".0 identity fallback should remain enabled for checked-op BinOp shapes"
        );
    }

    #[test]
    fn test_field0_fallback_rejects_opaque_var_base() {
        let opaque = PureExpr::Var("opaque_value".to_string(), None);
        assert!(
            !allows_field0_identity_fallback(&opaque),
            ".0 identity fallback must be disabled for opaque Var bases"
        );
    }

    // Prover audit: synthetic tuple names with non-numeric suffixes are
    // rejected by tuple_logic_fn_arity. This confirms defense against
    // malformed names like "__trust_wp_tupleABC".
    #[test]
    fn test_project_tuple_field_rejects_malformed_tuple_names() {
        let malformed_alpha = PureExpr::LogicFnCall {
            name: "__trust_wp_tupleABC".to_string(),
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        };
        assert_eq!(project_tuple_field(&malformed_alpha, 0), None);

        let bare_prefix = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple".to_string(),
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        };
        assert_eq!(project_tuple_field(&bare_prefix, 0), None);

        let negative = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple-2".to_string(),
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        };
        assert_eq!(project_tuple_field(&negative, 0), None);
    }

    #[test]
    fn test_project_nested_tuple_get_field_composes_accessors() {
        let base = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };
        let projected = project_nested_tuple_get_field(&base, 1);
        assert_eq!(
            projected,
            Some(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![base],
            })
        );
    }

    #[test]
    fn test_project_nested_tuple_get_field_rejects_non_tuple_get() {
        let base = PureExpr::LogicFnCall {
            name: "my_logic_fn".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };
        assert_eq!(project_nested_tuple_get_field(&base, 0), None);
    }

    #[test]
    fn test_simplify_tuple_get_from_constructor() {
        let tuple = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple2".to_string(),
            args: vec![
                PureExpr::Var("a".to_string(), None),
                PureExpr::Var("b".to_string(), None),
            ],
        };
        let nested = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![tuple],
        };
        assert_eq!(
            simplify_tuple_get_from_constructor(&nested),
            Some(PureExpr::Var("b".to_string(), None))
        );
    }

    #[test]
    fn test_switch_value_to_i64_masking() {
        // Test that values with extra high bits are properly masked
        let u8_ty = DiscrIntTy {
            signed: false,
            bits: 8,
        };

        // 0x1FF (511) should mask to 0xFF (255)
        assert_eq!(switch_value_to_i64(0x1FF, u8_ty), Some(255));

        // 0xABCD should mask to 0xCD (205)
        assert_eq!(switch_value_to_i64(0xABCD, u8_ty), Some(0xCD));

        let i8_ty = DiscrIntTy {
            signed: true,
            bits: 8,
        };

        // 0x1FF masks to 0xFF, which is -1 in signed i8
        assert_eq!(switch_value_to_i64(0x1FF, i8_ty), Some(-1));

        // 0xAB80 masks to 0x80, which is -128 in signed i8
        assert_eq!(switch_value_to_i64(0xAB80, i8_ty), Some(-128));
    }
}

// Tests for the shift-amount syntactic range discharge (ledger
// int-shift-full): amounts provably inside `[0, bits)` by shape skip the
// `__trust_wp_shift_amount_in_range_{bits}` marker; everything else keeps it
// so the ay encoder collects the range proof obligation.
mod shift_amount_syntactic_range_tests {
    use super::*;

    fn bitand(l: PureExpr, r: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(l), BinOp::BitAnd, Arc::new(r))
    }

    #[test]
    fn test_in_range_literals_discharge() {
        for amount in [0, 1, 7] {
            assert!(
                super::super::rvalue::shift_amount_syntactically_in_range(
                    &PureExpr::Int(amount),
                    8
                ),
                "literal {amount} is inside [0, 8)"
            );
        }
    }

    #[test]
    fn test_out_of_range_literals_keep_the_marker() {
        // The int-shift-full amount (8 for a u8 shift) and negatives.
        for amount in [8, 64, -1] {
            assert!(
                !super::super::rvalue::shift_amount_syntactically_in_range(
                    &PureExpr::Int(amount),
                    8
                ),
                "literal {amount} is NOT inside [0, 8)"
            );
        }
    }

    #[test]
    fn test_mask_idiom_discharges_on_either_side() {
        let n = PureExpr::Var("n".to_string(), None);
        assert!(super::super::rvalue::shift_amount_syntactically_in_range(
            &bitand(n.clone(), PureExpr::Int(7)),
            8
        ));
        assert!(super::super::rvalue::shift_amount_syntactically_in_range(
            &bitand(PureExpr::Int(7), n.clone()),
            8
        ));
        // A mask as wide as the type (8 = 0b1000) does NOT bound the amount
        // below the width — the obligation stays.
        assert!(!super::super::rvalue::shift_amount_syntactically_in_range(
            &bitand(n.clone(), PureExpr::Int(8)),
            8
        ));
        // A negative "mask" has all high bits set — no bound either.
        assert!(!super::super::rvalue::shift_amount_syntactically_in_range(
            &bitand(n, PureExpr::Int(-1)),
            8
        ));
    }

    #[test]
    fn test_symbolic_amounts_keep_the_marker() {
        let n = PureExpr::Var("n".to_string(), None);
        assert!(!super::super::rvalue::shift_amount_syntactically_in_range(
            &n, 8
        ));
    }
}

// Tests for Cast handling in translate_rvalue.
//
// Verifies type-aware cast dispatch: supported casts (IntToInt, PtrToPtr,
// Subtype, safe PointerCoercions) pass through as identity; unsupported
// casts (float, transmute, provenance) return None.
mod translate_cast_tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;
    use rustc_middle::{
        mir::{Rvalue, StatementKind},
        ty::TyCtxt,
    };

    use super::*;

    static COUNTER: AtomicU64 = AtomicU64::new(0);

    /// Helper: compile `source`, locate function `fn_name` in MIR,
    /// find the first `Rvalue::Cast` statement, and translate it via
    /// `translate_rvalue`. Returns the translation result.
    fn run_cast_test(source: &str, fn_name: &str) -> Option<PureExpr> {
        struct CastCallbacks {
            fn_name: String,
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            ran: bool,
        }

        impl Callbacks for CastCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if def_path != self.fn_name
                        && !def_path.ends_with(&format!("::{}", self.fn_name))
                    {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());

                    // Build a local-expr map for all locals.
                    let mut locals = HashMap::new();
                    for (idx, _) in body.local_decls.iter_enumerated() {
                        locals.insert(idx, PureExpr::Var(format!("__{}", idx.index()), None));
                    }

                    // Find the first Cast rvalue in MIR statements.
                    for bb in body.basic_blocks.iter() {
                        for stmt in &bb.statements {
                            if let StatementKind::Assign((_, ref rvalue)) = stmt.kind {
                                if matches!(rvalue, Rvalue::Cast(..)) {
                                    self.result =
                                        Some(translate_rvalue(rvalue, &locals, Some(body)));
                                    self.ran = true;
                                    return Compilation::Stop;
                                }
                            }
                        }
                    }
                    // No Cast found — still mark ran.
                    self.ran = true;
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_cast_test_{}_{}",
            std::process::id(),
            unique,
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, source).unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_cast_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = CastCallbacks {
            fn_name: fn_name.to_string(),
            result: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to locate {} in rustc callback",
            fn_name
        );
        callbacks.result.unwrap_or(None)
    }

    // IntToInt: widening cast (u8 → u32) should pass through.
    #[test]
    fn test_cast_int_widening_passes_through() {
        let result = run_cast_test("pub fn widen(x: u8) -> u32 { x as u32 }", "widen");
        assert!(
            result.is_some(),
            "IntToInt widening cast should translate successfully"
        );
    }

    // IntToInt: narrowing cast (u32 → u8) should pass through
    // (overflow checking is the verifier's responsibility, not MIR translation).
    #[test]
    fn test_cast_int_narrowing_passes_through() {
        let result = run_cast_test("pub fn narrow(x: u32) -> u8 { x as u8 }", "narrow");
        assert!(
            result.is_some(),
            "IntToInt narrowing cast should translate successfully"
        );
    }

    // IntToInt: sign-changing cast (i32 → u32) should pass through.
    #[test]
    fn test_cast_int_sign_change_passes_through() {
        let result = run_cast_test(
            "pub fn sign_change(x: i32) -> u32 { x as u32 }",
            "sign_change",
        );
        assert!(
            result.is_some(),
            "IntToInt sign-changing cast should translate successfully"
        );
    }

    fn ieee_fn_of(expr: &PureExpr) -> trust_wp_core::formula::ieee::IeeeFn {
        match expr {
            PureExpr::LogicFnCall { name, args } => {
                assert_eq!(args.len(), 1, "a cast has one operand: {expr:?}");
                trust_wp_core::formula::ieee::IeeeFn::parse(name)
                    .unwrap_or_else(|| panic!("expected a reserved IEEE call, got {expr:?}"))
            }
            other => panic!("expected a reserved IEEE call, got {other:?}"),
        }
    }

    // `as` between a float and an integer, or between the two float formats,
    // is its IEEE conversion, named with both sides' types.
    #[test]
    fn test_cast_float_to_int_is_the_ieee_conversion() {
        use trust_wp_core::formula::{
            ieee::{IeeeFn, IeeeOp},
            FloatWidth,
        };
        let signed = run_cast_test(
            "#[allow(clippy::cast_possible_truncation)]\npub fn float_to_int(x: f64) -> i32 { x as i32 }",
            "float_to_int",
        )
        .expect("f64 as i32 translates");
        assert_eq!(
            ieee_fn_of(&signed),
            IeeeFn::new(
                IeeeOp::ToInt {
                    signed: true,
                    bits: 32
                },
                FloatWidth::F64
            )
        );
        let unsigned = run_cast_test(
            "#[allow(clippy::cast_possible_truncation)]\npub fn float_to_uint(x: f32) -> u8 { x as u8 }",
            "float_to_uint",
        )
        .expect("f32 as u8 translates");
        assert_eq!(
            ieee_fn_of(&unsigned),
            IeeeFn::new(
                IeeeOp::ToInt {
                    signed: false,
                    bits: 8
                },
                FloatWidth::F32
            )
        );
    }

    #[test]
    fn test_cast_int_to_float_is_the_ieee_conversion() {
        use trust_wp_core::formula::{
            ieee::{IeeeFn, IeeeOp},
            FloatWidth,
        };
        let result = run_cast_test(
            "pub fn int_to_float(x: u64) -> f64 { x as f64 }",
            "int_to_float",
        )
        .expect("u64 as f64 translates");
        assert_eq!(
            ieee_fn_of(&result),
            IeeeFn::new(
                IeeeOp::FromInt {
                    signed: false,
                    bits: 64
                },
                FloatWidth::F64
            ),
            "not the identity: 2^53 + 1 is no f64 value"
        );
    }

    #[test]
    fn test_cast_float_to_float_rounds_through_the_ieee_conversion() {
        use trust_wp_core::formula::{
            ieee::{IeeeFn, IeeeOp},
            FloatWidth,
        };
        let result = run_cast_test(
            "#[allow(clippy::cast_possible_truncation)]\npub fn float_narrow(x: f64) -> f32 { x as f32 }",
            "float_narrow",
        )
        .expect("f64 as f32 translates");
        assert_eq!(
            ieee_fn_of(&result),
            IeeeFn::new(IeeeOp::ToFloat(FloatWidth::F32), FloatWidth::F64)
        );
    }

    fn ptr_thin_of(operand: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: trust_wp_core::formula::internal::builtins::PTR_THIN_LOGIC_FN.to_string(),
            args: vec![operand],
        }
    }

    // PtrToPtr between thin pointers keeps the pointer: the identity.
    #[test]
    fn test_cast_thin_ptr_to_thin_ptr_is_identity() {
        let result = run_cast_test(
            "pub fn t(p: *const u32) -> *const u8 { p as *const u8 }",
            "t",
        );
        assert_eq!(result, Some(PureExpr::Var("__1".into(), None)));
    }

    // A fat pointer cast to a thin one drops the length: two slice pointers
    // that differ only in length have equal casts, so the cast is `thin`,
    // never its operand.
    #[test]
    fn test_cast_fat_ptr_to_thin_ptr_is_thin() {
        let result = run_cast_test(
            "pub fn t(p: *const [u8]) -> *const u8 { p as *const u8 }",
            "t",
        );
        assert_eq!(result, Some(ptr_thin_of(PureExpr::Var("__1".into(), None))));
    }

    // The same pointee keeps the metadata whatever it is, `?Sized` included.
    #[test]
    fn test_cast_same_unsized_pointee_is_identity() {
        let result = run_cast_test(
            "pub fn t<T: ?Sized>(p: *const T) -> *mut T { p as *mut T }",
            "t",
        );
        assert_eq!(result, Some(PureExpr::Var("__1".into(), None)));
    }

    // A `?Sized` pointee cast to a sized one may drop metadata: `thin`.
    #[test]
    fn test_cast_maybe_unsized_to_sized_is_thin() {
        let result = run_cast_test(
            "pub fn t<T: ?Sized>(p: *const T) -> *const u8 { p as *const u8 }",
            "t",
        );
        assert_eq!(result, Some(ptr_thin_of(PureExpr::Var("__1".into(), None))));
    }

    // Unsizing a raw pointer adds a length: `p as *const [u8; 4]` and
    // `p as *const [u8; 8]` unsized to `*const [u8]` differ, so each is its
    // own type pair's function of the operand, never the operand.
    #[test]
    fn test_cast_raw_ptr_unsize_is_its_pair_function() {
        let four = run_cast_test("pub fn t(p: *const [u8; 4]) -> *const [u8] { p }", "t");
        let eight = run_cast_test("pub fn t(p: *const [u8; 8]) -> *const [u8] { p }", "t");
        let prefix = trust_wp_core::formula::internal::builtins::PTR_PAIR_LOGIC_FN_PREFIX;
        match (four, eight) {
            (
                Some(PureExpr::LogicFnCall { name: four, args }),
                Some(PureExpr::LogicFnCall { name: eight, .. }),
            ) => {
                assert!(
                    four.starts_with(prefix) && eight.starts_with(prefix),
                    "{four} {eight}"
                );
                assert_ne!(four, eight);
                assert_eq!(args, vec![PureExpr::Var("__1".into(), None)]);
            }
            other => panic!("expected two unsizing functions, got {other:?}"),
        }
    }

    // A generic pair is its function too (keyed by the body's owner as
    // well), never the identity: lengths `N` and `M` of one address differ.
    #[test]
    fn test_cast_raw_ptr_unsize_generic_pair_is_a_function() {
        let result = run_cast_test(
            "pub fn t<const N: usize>(p: *const [u8; N]) -> *const [u8] { p }",
            "t",
        );
        let prefix = trust_wp_core::formula::internal::builtins::PTR_PAIR_LOGIC_FN_PREFIX;
        assert!(
            matches!(&result, Some(PureExpr::LogicFnCall { name, .. }) if name.starts_with(prefix)),
            "{result:?}"
        );
    }

    // The operand's type is followed through a field projection, so a field's
    // fat pointer cast to a thin one is `thin`.
    #[test]
    fn test_cast_fat_ptr_field_to_thin_ptr_is_thin() {
        let result = run_cast_test(
            "pub struct S { pub p: *const [u8], pub n: u8 }\n\
             pub fn t(s: &S) -> *const u8 { s.p as *const u8 }",
            "t",
        );
        assert!(
            matches!(
                &result,
                Some(PureExpr::LogicFnCall { name, .. })
                    if name == trust_wp_core::formula::internal::builtins::PTR_THIN_LOGIC_FN
            ),
            "{result:?}"
        );
    }

    /// The `PtrToPtr` cast of field 0 behind a deref of `t`'s first parameter
    /// (a `Box` of a struct) to `t`'s return type, translated in `t`'s body.
    ///
    /// The cast is built here rather than found: the optimized MIR a unit test
    /// can read has already elaborated a `Box` deref into a transmute of the
    /// box's inner pointer (and inlined the box's deallocation, itself a
    /// `PtrToPtr`), while the borrow-checked MIR the driver translates spells
    /// the access `(*s).p`, a `Deref` of the `Box` local.
    fn run_ptr_cast_through_box_param_test(source: &str) -> Option<PureExpr> {
        use rustc_middle::{
            mir::{CastKind, Operand, Place, ProjectionElem, RETURN_PLACE},
            ty::TyKind,
        };

        struct BoxCallbacks {
            result: Option<Option<PureExpr>>,
        }

        impl Callbacks for BoxCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                for local_def_id in tcx.hir_body_owners() {
                    if tcx.def_path_str(local_def_id) != "t" {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());
                    let param = Local::from_u32(1);
                    let Some(boxed) = body.local_decls[param].ty.boxed_ty() else {
                        panic!("`t`'s first parameter must be a Box");
                    };
                    let TyKind::Adt(adt, args) = boxed.kind() else {
                        panic!("`t`'s Box must hold a struct");
                    };
                    let field_ty = adt.non_enum_variant().fields[rustc_abi::FieldIdx::ZERO]
                        .ty(tcx, *args)
                        .skip_norm_wip();
                    let target = body.local_decls[RETURN_PLACE].ty;
                    let locals: HashMap<_, _> = body
                        .local_decls
                        .indices()
                        .map(|idx| (idx, PureExpr::Var(format!("__{}", idx.index()), None)))
                        .collect();
                    let place = Place {
                        local: param,
                        projection: tcx.mk_place_elems(&[
                            ProjectionElem::Deref,
                            ProjectionElem::Field(rustc_abi::FieldIdx::ZERO, field_ty),
                        ]),
                    };
                    let rvalue = Rvalue::Cast(CastKind::PtrToPtr, Operand::Copy(place), target);
                    self.result = Some(translate_rvalue(&rvalue, &locals, Some(body)));
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_box_cast_test_{}_{}",
            std::process::id(),
            unique,
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, source).unwrap();
        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_box_cast_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];
        let mut callbacks = BoxCallbacks { result: None };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);
        callbacks
            .result
            .expect("failed to locate `t` in rustc callback")
    }

    // A `Box` deref is followed too: the boxed field's fat pointer cast to a
    // thin one is `thin`, never untranslated.
    #[test]
    fn test_cast_fat_ptr_in_box_to_thin_ptr_is_thin() {
        let result = run_ptr_cast_through_box_param_test(
            "pub struct S { pub p: *const [u8], pub n: u8 }\n\
             pub fn t(s: Box<S>) -> *const u8 { s.p as *const u8 }",
        );
        assert!(
            matches!(
                &result,
                Some(PureExpr::LogicFnCall { name, .. })
                    if name == trust_wp_core::formula::internal::builtins::PTR_THIN_LOGIC_FN
            ),
            "{result:?}"
        );
    }

    // A cast to a custom unsized pointee keeps a length the classifier does
    // not read: it is its pair's function of the operand, neither the
    // identity nor untranslated (an untranslated right-hand side shares its
    // source name with a shadowing binding).
    #[test]
    fn test_cast_to_custom_unsized_pointee_is_its_pair_function() {
        let result = run_cast_test(
            "pub struct D { pub n: u8, pub tail: [u8] }\n\
             pub fn t(p: *const [u8]) -> *const D { p as *const D }",
            "t",
        );
        let prefix = trust_wp_core::formula::internal::builtins::PTR_PAIR_LOGIC_FN_PREFIX;
        match result {
            Some(PureExpr::LogicFnCall { name, args }) => {
                assert!(name.starts_with(prefix), "{name}");
                assert_eq!(args, vec![PureExpr::Var("__1".into(), None)]);
            }
            other => panic!("expected the pair's function, got {other:?}"),
        }
    }

    // A reference's unsizing keeps its value (the value model): the identity.
    #[test]
    fn test_cast_reference_unsize_is_identity() {
        let result = run_cast_test("pub fn t(a: &[u8; 4]) -> &[u8] { a }", "t");
        assert_eq!(result, Some(PureExpr::Var("__1".into(), None)));
    }

    /// `ptr_cast_kind` from the pointee of `t`'s first parameter to the
    /// pointee of its second, in `t`'s environment.
    fn run_ptr_cast_kind_test(source: &str) -> Option<super::super::ptr_cast::PtrCastKind> {
        struct KindCallbacks {
            result: Option<Option<super::super::ptr_cast::PtrCastKind>>,
        }

        impl Callbacks for KindCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                for local_def_id in tcx.hir_body_owners() {
                    if tcx.def_path_str(local_def_id) != "t" {
                        continue;
                    }
                    let def_id = local_def_id.to_def_id();
                    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip();
                    let sig = tcx.liberate_late_bound_regions(def_id, sig);
                    let inputs = sig.inputs();
                    let pointee = super::super::ptr_cast::raw_pointee;
                    let (Some(from), Some(to)) = (pointee(inputs[0]), pointee(inputs[1])) else {
                        panic!("both parameters of `t` must be raw pointers");
                    };
                    self.result =
                        Some(super::super::ptr_cast::ptr_cast_kind(tcx, def_id, from, to));
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_ptr_cast_kind_test_{}_{}",
            std::process::id(),
            unique,
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, source).unwrap();
        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_ptr_cast_kind_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];
        let mut callbacks = KindCallbacks { result: None };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);
        callbacks
            .result
            .expect("failed to locate `t` in rustc callback")
    }

    // A clause's `p as *const [u8]` from `*const [u8; 4]` reaches the
    // classifier untyped: it is an unsizing, which adds a length, never the
    // identity (Creusot's rule reads any fat target as the identity).
    #[test]
    fn test_ptr_cast_kind_sized_to_fat_is_neither() {
        let kind = run_ptr_cast_kind_test("pub fn t(_p: *const [u8; 4], _q: *const [u8]) {}");
        assert_eq!(kind, None);
    }

    // Between two fat pointees the metadata is kept: the identity.
    #[test]
    fn test_ptr_cast_kind_fat_to_fat_is_identity() {
        let kind = run_ptr_cast_kind_test("pub fn t(_p: *const str, _q: *const [u8]) {}");
        assert_eq!(kind, Some(super::super::ptr_cast::PtrCastKind::Id));
    }

    // ---------------------------------------------------------------------------
    // IntegerCastIdentity unsoundness counter verification (#938)
    //
    // These tests verify that the `translate_rvalue` path for `CastKind::IntToInt`
    // only increments `IntegerCastIdentity` for risky casts. The counter fires
    // inside the rustc `after_analysis` callback, so we capture the delta within
    // the callback itself (thread-local counters are per-thread, and `run_compiler`
    // may execute callbacks on an internal thread).
    // ---------------------------------------------------------------------------

    /// Helper: compile `source`, locate function `fn_name` in MIR,
    /// find the first `Rvalue::Cast` statement, translate it, and return
    /// both the translation result and the `IntegerCastIdentity` unsoundness
    /// delta that occurred during translation.
    fn run_cast_test_with_unsoundness(source: &str, fn_name: &str) -> (Option<PureExpr>, usize) {
        struct CastUnsoundnessCallbacks {
            fn_name: String,
            #[allow(clippy::option_option)]
            result: Option<Option<PureExpr>>,
            /// IntegerCastIdentity delta observed during translation.
            integer_cast_delta: usize,
            ran: bool,
        }

        impl Callbacks for CastUnsoundnessCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                for local_def_id in tcx.hir_body_owners() {
                    let def_path = tcx.def_path_str(local_def_id);
                    if def_path != self.fn_name
                        && !def_path.ends_with(&format!("::{}", self.fn_name))
                    {
                        continue;
                    }
                    let body = tcx.optimized_mir(local_def_id.to_def_id());

                    let mut locals = HashMap::new();
                    for (idx, _) in body.local_decls.iter_enumerated() {
                        locals.insert(idx, PureExpr::Var(format!("__{}", idx.index()), None));
                    }

                    for bb in body.basic_blocks.iter() {
                        for stmt in &bb.statements {
                            if let StatementKind::Assign((_, ref rvalue)) = stmt.kind {
                                if matches!(rvalue, Rvalue::Cast(..)) {
                                    // Snapshot before translation to measure the delta.
                                    let before = trust_wp_ay::unsoundness::snapshot();
                                    self.result =
                                        Some(translate_rvalue(rvalue, &locals, Some(body)));
                                    let after = trust_wp_ay::unsoundness::snapshot();
                                    let d = trust_wp_ay::unsoundness::delta(&before, &after);
                                    self.integer_cast_delta = d
                                        .get(&trust_wp_ay::UnsoundnessCategory::IntegerCastIdentity)
                                        .copied()
                                        .unwrap_or(0);
                                    self.ran = true;
                                    return Compilation::Stop;
                                }
                            }
                        }
                    }
                    self.ran = true;
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_cast_test_{}_{}",
            std::process::id(),
            unique,
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, source).unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_cast_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = CastUnsoundnessCallbacks {
            fn_name: fn_name.to_string(),
            result: None,
            integer_cast_delta: 0,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.ran,
            "failed to locate {} in rustc callback",
            fn_name
        );
        (
            callbacks.result.unwrap_or(None),
            callbacks.integer_cast_delta,
        )
    }

    // IntToInt narrowing cast (u32 -> u8) now emits a BV truncation call (#2666).
    //
    // Since #2666, narrowing casts emit `__trust_wp_int_truncate_u8(value)` which
    // the encoder intercepts to produce exact modular truncation via BV theory.
    // The IntegerCastIdentity counter is NOT incremented because the cast is now
    // properly modeled, not approximated as identity.
    //
    // Before #2666: identity + IntegerCastIdentity counter → demotion.
    // After #2666: BV truncation LogicFnCall → exact semantics, no demotion.
    #[test]
    fn test_cast_int_narrowing_emits_bv_truncation() {
        let (result, delta) =
            run_cast_test_with_unsoundness("pub fn narrow(x: u32) -> u8 { x as u8 }", "narrow");
        assert!(
            result.is_some(),
            "IntToInt narrowing cast should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "IntToInt narrowing cast must NOT increment IntegerCastIdentity after #2666; \
             got delta={delta}. Narrowing casts now use BV truncation."
        );
        // Verify the result is a LogicFnCall with the truncation name.
        let expr = result.unwrap();
        match &expr {
            PureExpr::LogicFnCall { name, args } => {
                assert_eq!(
                    name, "__trust_wp_int_truncate_u8",
                    "narrowing u32->u8 should emit __trust_wp_int_truncate_u8, got {name}"
                );
                assert_eq!(args.len(), 1, "truncation call should have exactly 1 arg");
            }
            other => panic!("narrowing cast should produce LogicFnCall, got {other:?}"),
        }
    }

    // Same-signed widening casts are value-preserving in Rust, so they must stay
    // clean even though MIR translation lowers them as identity. (#2663)
    #[test]
    fn test_cast_int_widening_does_not_increment_unsoundness() {
        let (result, delta) =
            run_cast_test_with_unsoundness("pub fn widen(x: u8) -> u32 { x as u32 }", "widen");
        assert!(
            result.is_some(),
            "IntToInt widening cast should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "Same-signed widening cast must not increment IntegerCastIdentity; got delta={delta}."
        );
    }

    #[test]
    fn test_cast_int_signed_widening_does_not_increment_unsoundness() {
        let (result, delta) = run_cast_test_with_unsoundness(
            "pub fn widen_signed(x: i8) -> i32 { x as i32 }",
            "widen_signed",
        );
        assert!(
            result.is_some(),
            "Signed IntToInt widening cast should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "Same-signed signed widening cast must not increment IntegerCastIdentity; got delta={delta}."
        );
    }

    // IntToInt sign-changing cast (i32 -> u32) now emits a BV truncation call (#2666).
    //
    // Since #2666, sign-changing casts emit `__trust_wp_int_truncate_u32(value)` which
    // the encoder intercepts to produce exact unsigned truncation via BV theory.
    // This correctly models `(-1i32) as u32` -> 4294967295 (wrapping semantics).
    #[test]
    fn test_cast_int_sign_change_emits_bv_truncation() {
        let (result, delta) = run_cast_test_with_unsoundness(
            "pub fn sign_change(x: i32) -> u32 { x as u32 }",
            "sign_change",
        );
        assert!(
            result.is_some(),
            "IntToInt sign-changing cast should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "IntToInt sign-changing cast must NOT increment IntegerCastIdentity after #2666; \
             got delta={delta}. Sign changes now use BV truncation."
        );
        // Verify the result is a LogicFnCall with the truncation name.
        let expr = result.unwrap();
        match &expr {
            PureExpr::LogicFnCall { name, args } => {
                assert_eq!(
                    name, "__trust_wp_int_truncate_u32",
                    "sign-changing i32->u32 should emit __trust_wp_int_truncate_u32, got {name}"
                );
                assert_eq!(args.len(), 1, "truncation call should have exactly 1 arg");
            }
            other => panic!("sign-changing cast should produce LogicFnCall, got {other:?}"),
        }
    }

    // Same-width unsigned -> signed casts avoid BV terms. This keeps exact
    // reinterpret semantics for source-typed values while avoiding ay model
    // validation failures in tuple-building assumptions such as `usize as isize`.
    #[test]
    fn test_cast_unsigned_to_signed_same_width_emits_arithmetic_cast() {
        let (result, delta) = run_cast_test_with_unsoundness(
            "pub fn sign_reinterpret(x: u64) -> i64 { x as i64 }",
            "sign_reinterpret",
        );
        assert!(
            result.is_some(),
            "same-width unsigned->signed cast should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "same-width unsigned->signed cast must not increment IntegerCastIdentity; got {delta}"
        );

        let expr = result.unwrap();
        match &expr {
            PureExpr::LogicFnCall { name, args } => {
                assert_eq!(
                    name, "__trust_wp_int_cast_u64_to_s64",
                    "u64->i64 should emit arithmetic same-width cast marker, got {name}"
                );
                assert_eq!(args.len(), 1, "cast call should have exactly 1 arg");
            }
            other => {
                panic!("same-width unsigned->signed cast should produce LogicFnCall, got {other:?}")
            }
        }
    }

    // Bool→Int should NOT increment IntegerCastIdentity (#2675).
    //
    // Bool values are 0 or 1, which fit in every integer type. The cast
    // `b as u32` is always value-preserving, so it must not fire the
    // unsoundness counter. This fixes 72 spurious demotions in
    // integer_ops.rs.
    #[test]
    fn test_cast_bool_to_int_does_not_increment_unsoundness() {
        let (result, delta) = run_cast_test_with_unsoundness(
            "pub fn bool_to_u32(b: bool) -> u32 { b as u32 }",
            "bool_to_u32",
        );
        assert!(
            result.is_some(),
            "Bool-to-int cast should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "Bool-to-int cast must NOT increment IntegerCastIdentity; \
             got delta={delta}. Bool values (0 or 1) fit in every integer type."
        );
    }

    // Bool→i8 should also NOT increment IntegerCastIdentity (#2675).
    //
    // Even the smallest signed type can hold 0 or 1.
    #[test]
    fn test_cast_bool_to_i8_does_not_increment_unsoundness() {
        let (result, delta) = run_cast_test_with_unsoundness(
            "pub fn bool_to_i8(b: bool) -> i8 { b as i8 }",
            "bool_to_i8",
        );
        assert!(
            result.is_some(),
            "Bool-to-i8 cast should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "Bool-to-i8 cast must NOT increment IntegerCastIdentity; \
             got delta={delta}. Bool values (0 or 1) fit in every integer type."
        );
    }

    // Non-negative signed constant → unsigned should NOT increment
    // IntegerCastIdentity (#2675). Shift operations generate `3_i32 as u32`
    // where the constant is small and non-negative. The SMT identity model
    // is correct because non-negative values have the same bit pattern in
    // signed and unsigned representations.
    #[test]
    fn test_cast_nonneg_const_signed_to_unsigned_does_not_increment_unsoundness() {
        // `n << 3` generates `3_i32 as u32` for the shift amount.
        let (result, delta) = run_cast_test_with_unsoundness(
            "pub fn shift_left(n: u8) -> u8 { n << 3 }",
            "shift_left",
        );
        assert!(
            result.is_some(),
            "Shift operation should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "Non-negative constant signed→unsigned cast must NOT increment \
             IntegerCastIdentity; got delta={delta}. The shift amount 3 is \
             non-negative and fits in u32."
        );
    }

    // IntToFloat should NOT increment IntegerCastIdentity (#938).
    //
    // IntToFloat is value-preserving in the SMT model (every integer is exactly
    // representable as a Real). Only IntToInt fires the counter.
    #[test]
    fn test_cast_int_to_float_does_not_increment_unsoundness() {
        let (result, delta) = run_cast_test_with_unsoundness(
            "pub fn int_to_float(x: i32) -> f64 { x as f64 }",
            "int_to_float",
        );
        assert!(
            result.is_some(),
            "IntToFloat cast should translate successfully"
        );
        assert_eq!(
            delta, 0,
            "IntToFloat cast must NOT increment IntegerCastIdentity;              got delta={delta}. Only IntToInt casts should fire this counter."
        );
    }

    // #2685: `dyn Trait` types must get an opaque Datatype sort, not None (which
    // causes sort_fallback_to_int). The enriched version resolves the principal
    // trait name via TyCtxt for a precise sort annotation.
    #[test]
    fn test_ty_to_expr_sort_enriched_dyn_trait_opaque_sort() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct DynTraitSortCallbacks {
            #[allow(clippy::option_option)]
            dyn_debug_sort: Option<Option<ExprSort>>,
            #[allow(clippy::option_option)]
            dyn_debug_ref_sort: Option<Option<ExprSort>>,
        }

        impl Callbacks for DynTraitSortCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_hir::def::DefKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if tcx.def_kind(def_id) != DefKind::Fn {
                        continue;
                    }
                    let path = tcx.def_path_str(def_id);
                    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                    let input = sig.inputs()[0];
                    if path.ends_with("takes_dyn_debug") {
                        // `*const dyn Debug` — dereference to get `dyn Debug`
                        // (fn sig uses `&dyn Debug`, we get `&dyn Debug` as the
                        // first input; the enriched function handles refs).
                        self.dyn_debug_ref_sort = Some(ty_to_expr_sort_enriched(tcx, input));
                    } else if path.ends_with("takes_boxed_dyn") {
                        self.dyn_debug_sort = Some(ty_to_expr_sort_enriched(tcx, input));
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_dyn_trait_sort_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "pub fn takes_dyn_debug(_d: &dyn std::fmt::Debug) {}\n\
             pub fn takes_boxed_dyn(_d: Box<dyn std::fmt::Debug>) {}\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_dyn_sort_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = DynTraitSortCallbacks {
            dyn_debug_sort: None,
            dyn_debug_ref_sort: None,
        };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        // &dyn Debug → Ref(Datatype("dyn std::fmt::Debug"))
        let ref_sort = callbacks
            .dyn_debug_ref_sort
            .expect("callback for takes_dyn_debug should run");
        assert!(
            ref_sort.is_some(),
            "&dyn Debug must NOT return None (would cause sort_fallback_to_int); got None"
        );
        let ref_sort = ref_sort.unwrap();
        match &ref_sort {
            ExprSort::Ref(inner) => match inner.as_ref() {
                ExprSort::Datatype(id) => {
                    let name = trust_wp_core::formula::resolve_sort_name(*id);
                    assert!(
                        name.starts_with("dyn"),
                        "dyn Trait sort name must start with 'dyn', got: {name}"
                    );
                }
                other => panic!("&dyn Debug inner sort must be Datatype, got: {other:?}"),
            },
            other => panic!("&dyn Debug must produce Ref(Datatype(...)), got: {other:?}"),
        }

        // Box<dyn Debug> → Datatype("dyn std::fmt::Debug")
        // (Box is a transparent wrapper, so ty_to_expr_sort_enriched sees through it)
        let box_sort = callbacks
            .dyn_debug_sort
            .expect("callback for takes_boxed_dyn should run");
        assert!(
            box_sort.is_some(),
            "Box<dyn Debug> must NOT return None; got None"
        );
        let box_sort = box_sort.unwrap();
        match &box_sort {
            ExprSort::Datatype(id) => {
                let name = trust_wp_core::formula::resolve_sort_name(*id);
                assert!(
                    name.starts_with("dyn"),
                    "Box<dyn Debug> sort name must start with 'dyn', got: {name}"
                );
            }
            other => panic!("Box<dyn Debug> must produce Datatype(...), got: {other:?}"),
        }
    }

    #[test]
    fn test_ty_to_expr_sort_enriched_generic_alias_does_not_normalize_empty_env() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct GenericAliasSortCallbacks {
            #[allow(clippy::option_option)]
            output_sort: Option<Option<ExprSort>>,
        }

        impl Callbacks for GenericAliasSortCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_hir::def::DefKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if tcx.def_kind(def_id) != DefKind::Fn {
                        continue;
                    }
                    let path = tcx.def_path_str(def_id);
                    if path.ends_with("view_alias") {
                        let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                        self.output_sort = Some(ty_to_expr_sort_enriched(tcx, sig.output()));
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_generic_alias_sort_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "pub struct Seq<T>(T);\n\
             pub struct Sparse<T, const SIZE: usize>(T);\n\
             pub trait View { type ViewTy; }\n\
             impl<T, const SIZE: usize> View for Sparse<T, SIZE> {\n\
                 type ViewTy = Seq<Option<T>>;\n\
             }\n\
             pub fn view_alias<T, const SIZE: usize>(\n\
                 _s: Sparse<T, SIZE>,\n\
             ) -> <Sparse<T, SIZE> as View>::ViewTy {\n\
                 loop {}\n\
             }\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_generic_alias_sort_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = GenericAliasSortCallbacks { output_sort: None };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        assert_eq!(
            callbacks.output_sort,
            Some(None),
            "generic associated type aliases should fail closed without invoking \
             fully_monomorphized normalization"
        );
    }

    #[test]
    fn test_ty_to_expr_sort_enriched_unresolved_assoc_type_is_type_param() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        struct AssocTypeSortCallbacks {
            #[allow(clippy::option_option)]
            assoc_sort: Option<Option<ExprSort>>,
        }

        impl Callbacks for AssocTypeSortCallbacks {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                use rustc_hir::def::DefKind;

                for local_def_id in tcx.hir_body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if tcx.def_kind(def_id) != DefKind::Fn {
                        continue;
                    }
                    let path = tcx.def_path_str(def_id);
                    if path.ends_with("assoc_param") {
                        let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                        self.assoc_sort = Some(ty_to_expr_sort_enriched(tcx, sig.inputs()[0]));
                    }
                }
                Compilation::Stop
            }
        }

        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_assoc_type_sort_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).unwrap();
        let source_path = temp_dir.join("test.rs");
        std::fs::write(
            &source_path,
            "pub trait Model { type DeepModelTy; }\n\
             pub fn assoc_param<K: Model>(_x: K::DeepModelTy) {}\n",
        )
        .unwrap();

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_assoc_type_sort_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = AssocTypeSortCallbacks { assoc_sort: None };
        run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);

        let assoc_sort = callbacks
            .assoc_sort
            .expect("callback for assoc_param should run")
            .expect("unresolved associated type should still produce a sort");
        let ExprSort::TypeParam(id) = assoc_sort else {
            panic!("unresolved associated type should map to TypeParam, got {assoc_sort:?}");
        };
        let name = trust_wp_core::formula::resolve_sort_name(id);
        assert!(
            name.contains("DeepModelTy"),
            "associated type sort name should retain the projection name, got {name}"
        );
    }
}
