// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compiler evidence for reading typed specification vehicles after MIR erasure.
//! This does not enable retention in production or establish its corpus cost.
//! Literal vehicles retain operator-specific DefIds and physical operand order.
//! These checks establish availability and identity. Production semantic
//! lowering and the retention policy require their own qualification.

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::{
    mir::{AggregateKind, Rvalue, StatementKind, TerminatorKind},
    thir::ExprKind,
    ty::{TyCtxt, TyKind},
};

use super::rustc_callback_harness::{run_test_compiler_with_args, trust_wp_probe_args};
use crate::callbacks::spec_typecheck::{
    clause_markers, clause_tag, install_spec_tc_mir_built_erasure,
};

#[derive(Clone, Copy)]
enum VehicleShape {
    Comparison { literal_left: bool, signed: bool },
    Arithmetic { literal_left: bool },
    NonliteralComparison,
}

struct VehicleCase {
    clause: &'static str,
    helper: &'static str,
    shape: VehicleShape,
}

impl VehicleCase {
    const fn comparison(clause: &'static str, helper: &'static str, literal_left: bool) -> Self {
        Self {
            clause,
            helper,
            shape: VehicleShape::Comparison {
                literal_left,
                signed: false,
            },
        }
    }

    const fn arithmetic(clause: &'static str, helper: &'static str, literal_left: bool) -> Self {
        Self {
            clause,
            helper,
            shape: VehicleShape::Arithmetic { literal_left },
        }
    }
}

const CASES: &[VehicleCase] = &[
    VehicleCase::comparison("x == 0", "eq_lit", false),
    VehicleCase::comparison("0 == x", "eq_lit_left", true),
    VehicleCase::comparison("x != 0", "ne_lit", false),
    VehicleCase::comparison("0 != x", "ne_lit_left", true),
    VehicleCase::comparison("x < 0", "lt_lit", false),
    VehicleCase::comparison("0 < x", "lt_lit_left", true),
    VehicleCase::comparison("x <= 0", "le_lit", false),
    VehicleCase::comparison("0 <= x", "le_lit_left", true),
    VehicleCase::comparison("x > 0", "gt_lit", false),
    VehicleCase::comparison("0 > x", "gt_lit_left", true),
    VehicleCase::comparison("x >= 0", "ge_lit", false),
    VehicleCase::comparison("0 >= x", "ge_lit_left", true),
    VehicleCase {
        clause: "x >= -1",
        helper: "ge_lit",
        shape: VehicleShape::Comparison {
            literal_left: false,
            signed: true,
        },
    },
    VehicleCase {
        clause: "-1 >= x",
        helper: "ge_lit_left",
        shape: VehicleShape::Comparison {
            literal_left: true,
            signed: true,
        },
    },
    VehicleCase {
        clause: "x >= y",
        helper: "ge_log",
        shape: VehicleShape::NonliteralComparison,
    },
    VehicleCase::arithmetic("(n + 7) == n", "add_lit", false),
    VehicleCase::arithmetic("(7 + n) == n", "add_lit_left", true),
    VehicleCase::arithmetic("(n - 7) == n", "sub_lit", false),
    VehicleCase::arithmetic("(7 - n) == n", "sub_lit_left", true),
    VehicleCase::arithmetic("(n * 7) == n", "mul_lit", false),
    VehicleCase::arithmetic("(7 * n) == n", "mul_lit_left", true),
    VehicleCase::arithmetic("(n / 7) == n", "div_lit", false),
    VehicleCase::arithmetic("(7 / n) == n", "div_lit_left", true),
    VehicleCase::arithmetic("(n % 7) == n", "rem_lit", false),
    VehicleCase::arithmetic("(7 % n) == n", "rem_lit_left", true),
];

fn fixture_source() -> String {
    let mut source =
        "#![feature(stmt_expr_attributes, proc_macro_hygiene)]\nuse trust_wp::*;\n".to_string();
    for case in CASES {
        source.push_str(&format!("#[requires({})]\n", case.clause));
    }
    source.push_str(
        "pub fn retained_clause(x: i32, y: i32, n: trust_wp_std::logic::Int) -> i32 { x }\n",
    );
    source
}

struct RetentionCallbacks {
    retain: bool,
    observed: usize,
}

impl Callbacks for RetentionCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_session, providers| {
            install_spec_tc_mir_built_erasure(providers);
        });
    }

    #[allow(clippy::elidable_lifetime_names)] // rustc callback signature
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert_eq!(tcx.sess.opts.unstable_opts.no_steal_thir, self.retain);
        let owner = tcx
            .hir_body_owners()
            .find(|&id| {
                tcx.opt_item_name(id.to_def_id())
                    .is_some_and(|name| name.as_str() == "retained_clause")
            })
            .expect("fixture function");
        let clauses: Vec<_> = tcx
            .hir_body_owners()
            .filter_map(|id| clause_tag(tcx, id).map(|tag| (id, tag)))
            .collect();
        assert_eq!(
            clauses.len(),
            CASES.len(),
            "every macro-authenticated clause must exist"
        );
        let markers = clause_markers(tcx, owner.to_def_id());
        for (_, tag) in &clauses {
            assert!(
                markers.contains(tag),
                "closure tag must identify a real owner clause: {tag:?}"
            );
        }

        // This is the actual production erasure provider, before an optimizer
        // could independently remove an unused closure construction.
        let parent = tcx.mir_built(owner);
        {
            let mir = parent.borrow();
            for (closure, _) in &clauses {
                assert!(mir.local_decls.iter().any(|decl| {
                    matches!(decl.ty.kind(), TyKind::Closure(id, _) if *id == closure.to_def_id())
                }), "the built parent must contain the macro closure's typed local");
            }
            assert!(!mir.basic_blocks.iter().flat_map(|block| &block.statements).any(|statement| {
                matches!(&statement.kind, StatementKind::Assign((_, Rvalue::Aggregate(AggregateKind::Closure(id, _), _))) if clauses.iter().any(|(closure, _)| closure.to_def_id() == *id))
            }), "the production cleanup must erase spec closure constructions");
        }
        // Unsafety checking is the consumer that normally steals parent and
        // nested-closure THIR. Exercise it explicitly at the analysis seam.
        tcx.check_unsafety(owner);
        for (closure, (kind, text)) in clauses {
            assert_eq!(kind, "requires");
            let (cached, root) = tcx
                .thir_body(closure)
                .expect("specification THIR was built");
            assert_eq!(cached.is_stolen(), !self.retain);
            if self.retain {
                let thir = cached.borrow();
                assert_eq!(thir[root].ty, tcx.types.bool);
                let clause = text.split_whitespace().collect::<String>();
                let case = CASES
                    .iter()
                    .find(|case| case.clause.split_whitespace().collect::<String>() == clause)
                    .expect("authenticated clause must match its fixture case");
                let comparison = thir
                    .exprs
                    .iter()
                    .find_map(|expr| {
                        let ExprKind::Call { ty, args, .. } = &expr.kind else {
                            return None;
                        };
                        let TyKind::FnDef(id, _) = ty.kind() else {
                            return None;
                        };
                        (tcx.crate_name(id.krate).as_str() == "trust_wp_std"
                            && tcx.item_name(*id).as_str() == case.helper)
                            .then_some((expr, args))
                    })
                    .expect("resolved typed comparison vehicle must survive");
                assert_eq!(comparison.1.len(), 2);
                match case.shape {
                    VehicleShape::NonliteralComparison => {
                        assert_eq!(comparison.0.ty, tcx.types.bool);
                        for &arg in comparison.1.iter() {
                            assert_eq!(thir[arg].ty, tcx.types.i32);
                        }
                    }
                    VehicleShape::Comparison {
                        literal_left,
                        signed,
                    } => {
                        let literal = usize::from(!literal_left);
                        let value = usize::from(literal_left);
                        assert_eq!(comparison.0.ty, tcx.types.bool);
                        assert_eq!(thir[comparison.1[value]].ty, tcx.types.i32);
                        assert_eq!(
                            thir[comparison.1[literal]].ty,
                            if signed {
                                tcx.types.i128
                            } else {
                                tcx.types.u128
                            }
                        );
                    }
                    VehicleShape::Arithmetic { literal_left } => {
                        let literal = usize::from(!literal_left);
                        let value = usize::from(literal_left);
                        let value_ty = thir[comparison.1[value]].ty;
                        assert_eq!(comparison.0.ty, value_ty);
                        assert!(
                            matches!(value_ty.kind(), TyKind::Adt(def, _) if tcx.crate_name(def.did().krate).as_str() == "trust_wp_std" && tcx.item_name(def.did()).as_str() == "Int")
                        );
                        assert_eq!(thir[comparison.1[literal]].ty, tcx.types.u128);
                    }
                }
            }
            let closure_mir = tcx.mir_built(closure).borrow();
            assert_eq!(closure_mir.basic_blocks.len(), 1);
            assert!(
                closure_mir.basic_blocks.iter().all(|block| {
                    block.statements.is_empty()
                        && matches!(block.terminator().kind, TerminatorKind::Return)
                }),
                "the erased closure MIR must not be mistaken for its retained THIR"
            );
            self.observed += 1;
        }
        Compilation::Stop
    }
}

fn probe(retain: bool) {
    let mut args = trust_wp_probe_args();
    args.push("-Ztrust-verify=off".to_string());
    if retain {
        args.push("-Zno-steal-thir".to_string());
    }
    let mut callbacks = RetentionCallbacks {
        retain,
        observed: 0,
    };
    run_test_compiler_with_args(
        &fixture_source(),
        "trust_wp_thir_retention",
        &args,
        &mut callbacks,
    );
    assert_eq!(
        callbacks.observed,
        CASES.len(),
        "compiler callback must inspect every clause"
    );
}

#[test]
fn spec_clause_thir_survives_parent_mir_cleanup_with_retention() {
    probe(true);
}

#[test]
fn spec_clause_thir_is_stolen_by_default_after_parent_mir_cleanup() {
    probe(false);
}
