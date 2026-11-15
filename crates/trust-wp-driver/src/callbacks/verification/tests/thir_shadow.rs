// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The shadow component reads real macro vehicles after real parent MIR cleanup.
//! These tests grant no proof credit and do not change production compiler flags.

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::{
    mir::{AggregateKind, Rvalue, StatementKind},
    ty::{TyCtxt, TyKind},
};

use super::rustc_callback_harness::{run_test_compiler_with_args, trust_wp_probe_args};
use crate::callbacks::{
    frontend::{
        check_callee_surface_for_test, lower_clause, lower_owner_clauses, Binding,
        CanonicalHelpers, ExprKind, LiteralSide, Op, Origin, Refusal, TypedExpr, UnaryOp,
    },
    spec_typecheck::{clause_tag, install_spec_tc_mir_built_erasure},
};

const COMPARISONS: &[(&str, Op)] = &[
    ("==", Op::Eq),
    ("!=", Op::Ne),
    ("<", Op::Lt),
    ("<=", Op::Le),
    (">", Op::Gt),
    (">=", Op::Ge),
];
const ARITHMETIC: &[(&str, Op)] = &[
    ("+", Op::Add),
    ("-", Op::Sub),
    ("*", Op::Mul),
    ("/", Op::Div),
    ("%", Op::Rem),
];

fn fixture() -> String {
    let mut source =
        "#![feature(stmt_expr_attributes, proc_macro_hygiene)]\nuse trust_wp::*;\n".to_string();
    for (symbol, _) in COMPARISONS {
        source.push_str(&format!(
            "#[requires(x {symbol} 7)]\n#[requires(7 {symbol} x)]\n"
        ));
    }
    for (symbol, _) in ARITHMETIC {
        source.push_str(&format!(
            "#[requires((n {symbol} 7) == n)]\n#[requires((7 {symbol} n) == n)]\n"
        ));
    }
    for clause in [
        "x >= -1",
        "-1 >= x",
        "x >= y",
        "x + y == x",
        "-x == y",
        "a && !b",
        "a || b",
        "x == y",
        "x == x",
        "x == 7i32",
        "1 == 2",
        "true",
        "c == 'z'",
    ] {
        source.push_str(&format!("#[requires({clause})]\n"));
    }
    source.push_str(
        "pub fn shadow_clause(x:i32,y:i32,n:trust_wp_std::logic::Int,a:bool,b:bool,c:char){}\n",
    );
    source
}

enum Mode {
    Accept,
    Refuse,
    Stolen,
}

struct ShadowCallbacks {
    mode: Mode,
    observed: usize,
}

impl Callbacks for ShadowCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, providers| install_spec_tc_mir_built_erasure(providers));
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let helpers = CanonicalHelpers::discover(tcx).expect("actual library helper identities");
        let clauses: Vec<_> = tcx
            .hir_body_owners()
            .filter(|&id| clause_tag(tcx, id).is_some())
            .collect();
        assert!(!clauses.is_empty());
        let owner = tcx.local_parent(clauses[0]);
        match self.mode {
            Mode::Accept => assert_eq!(
                lower_owner_clauses(tcx, &helpers, owner)
                    .expect("complete supported owner inventory")
                    .len(),
                clauses.len()
            ),
            Mode::Refuse => {
                let Refusal::MissingClauseVehicles(missing) =
                    lower_owner_clauses(tcx, &helpers, owner).unwrap_err()
                else {
                    panic!("owner must explicitly report both missing macro vehicles");
                };
                assert_eq!(missing.len(), 2);
                let missing: Vec<_> = missing
                    .into_iter()
                    .map(|(kind, text)| {
                        assert_eq!(kind, "requires");
                        text.split_whitespace().collect::<String>()
                    })
                    .collect();
                assert!(missing.contains(&"[1,2]==xs".to_owned()));
                assert!(missing
                    .iter()
                    .any(|text| text.contains("effect();trust_wp_std::__spec_tc::ge_lit")));
            }
            Mode::Stolen => {}
        }
        for closure in clauses {
            let owner = tcx.local_parent(closure);
            erase_parent_then_check_unsafety(tcx, owner, closure);
            let result = lower_clause(tcx, &helpers, owner, closure);
            match self.mode {
                Mode::Accept => {
                    let clause = result.expect("supported authenticated scalar clause");
                    assert_eq!(clause.owner(), owner);
                    assert_eq!(clause.closure(), closure);
                    assert_eq!(clause.body().ty(), tcx.types.bool);
                    check_clause(
                        tcx,
                        &clause.tag().1.split_whitespace().collect::<String>(),
                        clause.body(),
                    );
                    assert!(
                        lower_clause(tcx, &helpers, closure, closure).is_err(),
                        "wrong owner must refuse"
                    );
                }
                Mode::Refuse => {
                    let tag = clause_tag(tcx, closure).unwrap().1;
                    match result.expect_err("unsupported semantics must refuse") {
                        Refusal::ErasedCall(id) => {
                            assert_eq!(tcx.crate_name(id.krate).as_str(), "trust_wp_std")
                        }
                        Refusal::UnsupportedCall(id) => assert!(
                            id.is_local(),
                            "impostor call must preserve its actual local DefId: {tag}"
                        ),
                        other => panic!("unexpected refusal for {tag}: {other:?}"),
                    }
                }
                Mode::Stolen => assert_eq!(result.unwrap_err(), Refusal::ThirStolen),
            }
            self.observed += 1;
        }
        if matches!(self.mode, Mode::Refuse) {
            let unmarked = tcx
                .hir_body_owners()
                .find(|&id| {
                    tcx.def_kind(id) == rustc_hir::def::DefKind::Closure
                        && clause_tag(tcx, id).is_none()
                })
                .expect("ordinary user closure");
            assert_eq!(
                lower_clause(tcx, &helpers, tcx.local_parent(unmarked), unmarked).unwrap_err(),
                Refusal::UnauthenticatedClause
            );
            // The macro intentionally emits no clause for block-valued callees
            // refused by the existing text parser. Exercise this production
            // guard on real unmarked THIR instead; it creates no typed clause.
            let (cached, _) = tcx.thir_body(unmarked).expect("ordinary closure THIR");
            let thir = cached.borrow();
            let (fun, function_ty) = thir
                .exprs
                .iter()
                .find_map(|expr| {
                    let rustc_middle::thir::ExprKind::Call { ty, fun, .. } = &expr.kind else {
                        return None;
                    };
                    let TyKind::FnDef(id, _) = ty.kind() else {
                        return None;
                    };
                    (!id.is_local()).then_some((*fun, *ty))
                })
                .expect("actual canonical function item returned by an effectful block");
            assert_eq!(
                check_callee_surface_for_test(&helpers, &thir, fun, function_ty),
                Err(Refusal::NontrivialCallee)
            );
        }
        Compilation::Stop
    }
}

fn erase_parent_then_check_unsafety(tcx: TyCtxt<'_>, owner: LocalDefId, closure: LocalDefId) {
    let parent = tcx.mir_built(owner).borrow();
    assert!(parent.local_decls.iter().any(
        |decl| matches!(decl.ty.kind(), TyKind::Closure(id, _) if *id == closure.to_def_id())
    ));
    assert!(!parent.basic_blocks.iter().flat_map(|block| &block.statements).any(|statement| {
        matches!(&statement.kind, StatementKind::Assign((_, Rvalue::Aggregate(AggregateKind::Closure(id, _), _))) if *id == closure.to_def_id())
    }), "actual production cleanup erased the clause construction");
    drop(parent);
    let _ = tcx.check_unsafety(owner);
}

fn stripped<'a, 'tcx>(expr: &'a TypedExpr<'tcx>) -> &'a TypedExpr<'tcx> {
    match expr.kind() {
        ExprKind::Borrow(inner) | ExprKind::Deref(inner) => stripped(inner),
        _ => expr,
    }
}

fn binding(expr: &TypedExpr<'_>) -> Binding {
    let ExprKind::Binding(binding) = stripped(expr).kind() else {
        panic!("expected compiler binding: {expr:?}");
    };
    *binding
}

fn literal(expr: &TypedExpr<'_>, magnitude: u128, negative: bool) {
    match expr.kind() {
        ExprKind::Integer {
            magnitude: actual,
            negative: sign,
        } => {
            assert_eq!(*actual, magnitude);
            assert_eq!(*sign, negative);
        }
        ExprKind::Unary {
            op: UnaryOp::Neg,
            origin: Origin::Native,
            arg,
        } if negative => literal(arg, magnitude, false),
        _ => panic!("expected exact typed integer literal: {expr:?}"),
    }
}

fn check_literal_binary<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &TypedExpr<'tcx>,
    op: Op,
    side: LiteralSide,
    signed: bool,
) {
    let ExprKind::Binary {
        op: actual,
        origin:
            Origin::LiteralHelper {
                helper,
                side: actual_side,
                value_ty,
            },
        lhs,
        rhs,
    } = expr.kind()
    else {
        panic!("expected literal helper: {expr:?}");
    };
    assert_eq!(*actual, op);
    assert_eq!(*actual_side, side);
    assert_eq!(tcx.crate_name(helper.krate).as_str(), "trust_wp_std");
    let (carrier, value) = if side == LiteralSide::Left {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    };
    assert_eq!(
        carrier.ty(),
        if signed {
            tcx.types.i128
        } else {
            tcx.types.u128
        }
    );
    literal(carrier, if signed { 1 } else { 7 }, signed);
    assert_eq!(value.ty(), *value_ty);
    assert!(
        matches!(binding(value), Binding::Upvar { .. }),
        "captures retain actual rustc binding identity"
    );
}

fn check_clause<'tcx>(tcx: TyCtxt<'tcx>, text: &str, expr: &TypedExpr<'tcx>) {
    for (symbol, op) in COMPARISONS {
        for (text_case, side) in [
            (format!("x{symbol}7"), LiteralSide::Right),
            (format!("7{symbol}x"), LiteralSide::Left),
        ] {
            if text == text_case {
                check_literal_binary(tcx, expr, *op, side, false);
                return;
            }
        }
    }
    for (symbol, op) in ARITHMETIC {
        for (text_case, side) in [
            (format!("(n{symbol}7)==n"), LiteralSide::Right),
            (format!("(7{symbol}n)==n"), LiteralSide::Left),
        ] {
            if text == text_case {
                let ExprKind::Binary {
                    op: Op::Eq,
                    lhs,
                    rhs,
                    ..
                } = expr.kind()
                else {
                    panic!("outer equality");
                };
                check_literal_binary(tcx, lhs, *op, side, false);
                let ExprKind::Binary {
                    lhs: inner_left,
                    rhs: inner_right,
                    ..
                } = lhs.kind()
                else {
                    unreachable!()
                };
                let value = if side == LiteralSide::Left {
                    inner_right
                } else {
                    inner_left
                };
                assert_eq!(binding(value), binding(rhs));
                return;
            }
        }
    }
    match text {
        "x>=-1" => check_literal_binary(tcx, expr, Op::Ge, LiteralSide::Right, true),
        "-1>=x" => check_literal_binary(tcx, expr, Op::Ge, LiteralSide::Left, true),
        "x>=y" => assert!(matches!(
            expr.kind(),
            ExprKind::Binary {
                op: Op::Ge,
                origin: Origin::Helper(_),
                ..
            }
        )),
        "x+y==x" => {
            let ExprKind::Binary { lhs, .. } = expr.kind() else {
                panic!("outer equality");
            };
            assert!(matches!(
                lhs.kind(),
                ExprKind::Binary {
                    op: Op::Add,
                    origin: Origin::Helper(_),
                    ..
                }
            ));
        }
        "-x==y" => {
            let ExprKind::Binary { lhs, .. } = expr.kind() else {
                panic!("outer equality");
            };
            assert!(matches!(
                lhs.kind(),
                ExprKind::Unary {
                    op: UnaryOp::Neg,
                    origin: Origin::Helper(_),
                    ..
                }
            ));
        }
        "a&&!b" => {
            let ExprKind::Binary {
                op: Op::And, rhs, ..
            } = expr.kind()
            else {
                panic!("native short-circuit and");
            };
            assert!(matches!(
                rhs.kind(),
                ExprKind::Unary {
                    op: UnaryOp::Not,
                    origin: Origin::Native,
                    ..
                }
            ));
        }
        "a||b" => assert!(matches!(
            expr.kind(),
            ExprKind::Binary {
                op: Op::Or,
                origin: Origin::Native,
                ..
            }
        )),
        "x==y" | "x==x" => {
            let ExprKind::Binary { lhs, rhs, .. } = expr.kind() else {
                panic!("equality");
            };
            assert_eq!(binding(lhs) == binding(rhs), text == "x==x");
            assert_eq!(lhs.ty(), tcx.types.i32);
            assert_eq!(rhs.ty(), tcx.types.i32);
        }
        "x==7i32" => {
            let ExprKind::Binary {
                rhs,
                origin: Origin::Helper(_),
                ..
            } = expr.kind()
            else {
                panic!("suffixed literal equality");
            };
            literal(rhs, 7, false);
            assert_eq!(rhs.ty(), tcx.types.i32);
        }
        "1==2" => {
            let ExprKind::Binary { lhs, rhs, .. } = expr.kind() else {
                panic!("logical literal equality");
            };
            assert!(matches!(lhs.kind(), ExprKind::IntLiteral { .. }));
            assert!(matches!(rhs.kind(), ExprKind::IntLiteral { .. }));
        }
        "true" => assert!(matches!(expr.kind(), ExprKind::Bool(true))),
        "c=='z'" => {
            let ExprKind::Binary { rhs, .. } = expr.kind() else {
                panic!("character equality");
            };
            assert!(matches!(rhs.kind(), ExprKind::Char('z')));
        }
        _ => panic!("unaccounted compiler fixture: {text}"),
    }
}

fn run(source: &str, mode: Mode, retain: bool) -> usize {
    let mut args = trust_wp_probe_args();
    args.push("-Ztrust-verify=off".into());
    if retain {
        args.push("-Zno-steal-thir".into());
    }
    let mut callbacks = ShadowCallbacks { mode, observed: 0 };
    run_test_compiler_with_args(source, "trust_wp_thir_shadow", &args, &mut callbacks);
    callbacks.observed
}

#[test]
fn thir_shadow_preserves_typed_operators_operands_and_bindings() {
    assert_eq!(run(&fixture(), Mode::Accept, true), 35);
}

#[test]
fn thir_shadow_refuses_erased_vehicles_and_helper_name_impostors() {
    let source = r#"
#![feature(stmt_expr_attributes, proc_macro_hygiene)]
use trust_wp::*;
mod impostor {
    pub fn ge_lit(_: i32, _: u128) -> bool { true }
    pub fn equal_pa(_: i32, _: i32) -> bool { true }
}
fn effect() {}
#[requires(impostor::ge_lit(x, 7u128))]
#[requires(impostor::equal_pa(x, x))]
#[requires(*trust_wp_std::__spec_tc::dead::<bool>())]
#[requires([1, 2] == xs)]
#[requires(({ effect(); trust_wp_std::__spec_tc::ge_lit::<i32, u128> })(x, 7u128))]
pub fn refused(x: i32, xs: [i32; 2]) {
    let ordinary = || ({ effect(); trust_wp_std::__spec_tc::ge_lit::<i32, u128> })(x, 7u128);
}
"#;
    assert_eq!(run(source, Mode::Refuse, true), 3);
}

#[test]
fn thir_shadow_refuses_stolen_bodies_without_retention() {
    assert_eq!(run("#![feature(stmt_expr_attributes, proc_macro_hygiene)]\nuse trust_wp::*;\n#[requires(x >= 0)]\npub fn stolen(x:i32) {}", Mode::Stolen, false), 1);
}
