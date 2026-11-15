// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What rustc typed every arithmetic operator of a specification as, handed
//! to the contract parser before any specification is parsed (D-232).
//!
//! In the pinned oracle `u32 + u32` in logic is creusot-std's
//! `UInt32$BW$.add`, which wraps, and `x@ + y@` is mathematical
//! (D-135 item 3). The contract parser reads text with no types, so each
//! operator's meaning comes from the type check `trust-wp-macros` gives the
//! clause (`spec_typecheck`): the vehicle writes `a + b` as
//! `__spec_tc::AddTc::add_tc(a, b)`, and the operand type is the `Self`
//! rustc infers for that call. Every reader of the clause text parses it
//! with the same reading (the clause's own lane, a caller reading it as a
//! callee's contract, a logic function's unfolding), because the reading is
//! keyed by the text and installed once, here. Being keyed by the text, it
//! is the reading of every occurrence of that text: a text also written where
//! no type check reads it keeps only what holds at any type
//! (`TextReading::with_untyped_occurrence`).
//!
//! The operators are identified by `DefId`, never by spelling: the calls of
//! `trust_wp_std::__spec_tc`'s operator stubs, and the native operators the
//! vehicle leaves as Rust.

use std::collections::{BTreeMap, HashMap};

use rustc_ast::attr::AttributeExt;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    intravisit::Visitor,
    Expr, ExprKind,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, Ty, TyCtxt, TypeckResults},
};
use trust_wp_core::contract_parser::machine_arith::{
    install, ArithOp, KindReading, MachineInt, OpReading, TextReading,
};

use super::spec_typecheck;

/// The type an operator is applied to.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Operand {
    /// `trust_wp_std::logic::Int`, or a type the text stack reads as written
    /// (a float).
    Int,
    /// A machine integer of this width and signedness.
    Machine { bits: u32, signed: bool },
    /// Anything else, named for a refusal.
    Other(String),
}

impl Operand {
    fn describe(&self) -> String {
        match self {
            Self::Int => "Int".to_string(),
            Self::Machine { bits, signed } => {
                format!("{}{bits}", if *signed { 'i' } else { 'u' })
            }
            Self::Other(name) => name.clone(),
        }
    }
}

/// Install, for the contract parser, the reading of every specification
/// text the crate type-checks: each clause, `proof_assert!`, loop clause and
/// trait-signature helper by its tag, and each logic body by its text.
pub(crate) fn install_spec_arith_readings(tcx: TyCtxt<'_>) {
    let mut texts: HashMap<String, TextReading> = HashMap::new();
    let mut typed: HashMap<String, usize> = HashMap::new();
    let mut add = |text: String, reading: TextReading| {
        let merged = match texts.get(&text) {
            Some(existing) => existing.merge(&reading),
            None => reading,
        };
        *typed.entry(text.clone()).or_default() += 1;
        texts.insert(text, merged);
    };
    for body in spec_typecheck::clause_tc_bodies(tcx) {
        if let Some((_, text)) = spec_typecheck::clause_tag(tcx, body) {
            add(text, reading_of_body(tcx, body));
        }
    }
    for local in tcx.iter_local_def_id() {
        if !matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let Some(closure) = spec_typecheck::logic_body_tc_closure(tcx, local) else {
            continue;
        };
        if let Some(text) = crate::logic::discovery::logic_body_text(tcx, local) {
            add(text, reading_of_body(tcx, closure.def_id));
        }
    }
    // The reading is keyed by the text, and one text can be written both
    // where a type check reads it and where none does (a clause the vehicle
    // skips, a pass-through attribute, a built-in table): a text keeps its
    // typed reading only where every occurrence of it is typed.
    let written = written_occurrences(tcx);
    for (text, reading) in &mut texts {
        if written.get(text).copied().unwrap_or(0) != typed.get(text).copied().unwrap_or(0) {
            *reading = reading.with_untyped_occurrence();
        }
    }
    install(texts);
}

/// How many times each text a clause reader may parse is written: every
/// `trust-wp:` doc marker on any node of the crate (an `extern_spec!` marker's
/// clauses one by one), every contract attribute left unexpanded, and every
/// clause of the built-in specification tables. A text counted that is no
/// clause only makes its reading stricter.
fn written_occurrences(tcx: TyCtxt<'_>) -> HashMap<String, usize> {
    let mut written: HashMap<String, usize> = HashMap::new();
    let mut count = |text: &str| {
        *written.entry(text.to_string()).or_default() += 1;
    };
    for owner in tcx.hir_crate_items(()).owners() {
        for attrs in tcx.hir_attr_map(owner).map.values() {
            for attr in *attrs {
                count_attribute(attr, &mut count);
            }
        }
    }
    for text in trust_wp_driver::builtin_clause_texts() {
        count(&text);
    }
    written
}

fn count_attribute(attr: &rustc_attr_ir::Attribute, count: &mut impl FnMut(&str)) {
    if let Some(value) = crate::attr_utils::doc_marker_str(attr) {
        match value
            .as_str()
            .strip_prefix("trust-wp:")
            .and_then(|marker| marker.split_once(':'))
        {
            Some((kind, rest)) => {
                count(rest);
                if kind == "extern_spec" {
                    let clauses = rest
                        .strip_prefix("requires=")
                        .or_else(|| rest.strip_prefix("ensures="));
                    for clause in clauses.into_iter().flat_map(|c| c.split(';')) {
                        let clause = clause.trim();
                        if !clause.is_empty() {
                            count(clause);
                        }
                    }
                }
            }
            // A key-value attribute's value may itself be a clause
            // (`#[trust_wp::spec::requires = ".."]`).
            None if attr.doc_str().is_none() => count(value.as_str()),
            None => {}
        }
    }
    if let rustc_attr_ir::Attribute::Tool(item) | rustc_attr_ir::Attribute::DeriveHelper(item) =
        attr
    {
        if let rustc_attr_ir::AttrArgs::Delimited(args) = &item.args {
            count(&rustc_ast_pretty::pprust::tts_to_string(&args.tokens));
        }
    }
}

/// The reading of the clause one type-check body checks.
fn reading_of_body(tcx: TyCtxt<'_>, body: LocalDefId) -> TextReading {
    let mut collector = OperatorCollector {
        tcx,
        typeck: tcx.typeck(body),
        pointer_bits: u32::try_from(tcx.data_layout.pointer_size().bits()).unwrap_or(64),
        sites: Vec::new(),
        dropped: false,
    };
    collector.visit_expr(tcx.hir_body_owned_by(body).value);
    reading_of_sites(&collector.sites, collector.dropped)
}

/// The reading of each operator kind, from what rustc typed each operator
/// of the clause as. `dropped`: the vehicle replaced a subterm by an
/// unconstrained value, whose operators have no type here.
fn reading_of_sites(sites: &[(ArithOp, Operand)], dropped: bool) -> TextReading {
    let mut by_kind: BTreeMap<ArithOp, Vec<&Operand>> = BTreeMap::new();
    for (op, operand) in sites {
        by_kind.entry(*op).or_default().push(operand);
    }
    let mut kinds = BTreeMap::new();
    for (op, operands) in &by_kind {
        kinds.insert(*op, reading_of_kind(*op, operands, dropped));
    }
    if dropped {
        // Every kind the clause holds no typed operator of may still hold an
        // untyped one in the dropped subterm: it reads by syntax alone.
        for op in [
            ArithOp::Add,
            ArithOp::Sub,
            ArithOp::Mul,
            ArithOp::Div,
            ArithOp::Rem,
            ArithOp::Neg,
            ArithOp::Shl,
            ArithOp::Shr,
        ] {
            kinds.entry(op).or_insert(KindReading {
                reading: OpReading::Syntactic,
                typed: None,
            });
        }
    }
    TextReading { kinds }
}

fn refused(why: String) -> KindReading {
    KindReading {
        reading: OpReading::Refused(why),
        typed: None,
    }
}

fn reading_of_kind(op: ArithOp, operands: &[&Operand], dropped: bool) -> KindReading {
    let first = operands[0];
    let uniform = operands.iter().all(|operand| *operand == first);
    let has_machine = operands
        .iter()
        .any(|operand| !matches!(operand, Operand::Int));
    if !has_machine {
        return if dropped {
            KindReading {
                reading: OpReading::Syntactic,
                typed: None,
            }
        } else {
            KindReading {
                reading: OpReading::Mathematical,
                typed: Some(operands.len()),
            }
        };
    }
    if dropped {
        return refused(format!(
            "the clause's type check dropped a subterm, so not every `{}` of it has a type, \
             and one is applied to `{}`",
            op.spelling(),
            operands
                .iter()
                .find(|operand| !matches!(operand, Operand::Int))
                .map_or_else(String::new, |operand| operand.describe())
        ));
    }
    if !uniform {
        let mut types: Vec<String> = operands.iter().map(|operand| operand.describe()).collect();
        types.sort();
        types.dedup();
        return refused(format!(
            "the clause applies `{}` to more than one type ({}), and every `{}` of a clause \
             is read at one",
            op.spelling(),
            types.join(", "),
            op.spelling()
        ));
    }
    let Operand::Machine { bits, signed } = *first else {
        return refused(format!(
            "it is applied to `{}`, which is neither `Int` nor a machine integer",
            first.describe()
        ));
    };
    let name = first.describe();
    match op {
        // A shift is read at its shifted operand's type, whose bit-vector
        // shift the parser states for a literal amount and refuses otherwise.
        ArithOp::Add | ArithOp::Sub | ArithOp::Mul | ArithOp::Neg | ArithOp::Shl | ArithOp::Shr => {
            match MachineInt::new(bits, signed) {
                Some(ty) => KindReading {
                    reading: OpReading::Wrapping(ty),
                    typed: Some(operands.len()),
                },
                None => refused(format!(
                    "the oracle's `{}` on `{name}` wraps at 128 bits, which exceeds what \
                     native replay evaluates",
                    op.spelling()
                )),
            }
        }
        ArithOp::Div | ArithOp::Rem => refused(format!(
            "the oracle's logic has no `{}` on `{name}` (creusot-std implements `DivLogic` and \
             `RemLogic` for `Int` alone)",
            op.spelling()
        )),
        ArithOp::Not => refused(format!(
            "the oracle's `{}` on `{name}` is its bit-vector operation, which trust-wp's \
             reading of the clause does not model",
            op.spelling()
        )),
    }
}

/// The operators of one type-check body, as rustc typed them.
struct OperatorCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    pointer_bits: u32,
    sites: Vec<(ArithOp, Operand)>,
    dropped: bool,
}

/// The path of `def_id` inside `trust_wp_std`, or `None` for an item of any
/// other crate.
fn trust_wp_std_path(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Vec<String>> {
    if def_id.is_local() || tcx.crate_name(def_id.krate).as_str() != "trust_wp_std" {
        return None;
    }
    Some(
        tcx.def_path(def_id)
            .data
            .iter()
            .map(|component| component.data.to_string())
            .collect(),
    )
}

/// The operator a `__spec_tc` stub stands for, and whether its type is its
/// `Self` (a trait method) or its first type parameter (a `*_lit` helper):
/// both are generic argument 0.
fn stub_operator(path: &[String]) -> Option<ArithOp> {
    let [module, rest @ ..] = path else {
        return None;
    };
    if module != "__spec_tc" {
        return None;
    }
    let names: Vec<&str> = rest.iter().map(String::as_str).collect();
    match names.as_slice() {
        ["AddTc", "add_tc"] | ["add_lit"] => Some(ArithOp::Add),
        ["SubTc", "sub_tc"] | ["sub_lit"] => Some(ArithOp::Sub),
        ["MulTc", "mul_tc"] | ["mul_lit"] => Some(ArithOp::Mul),
        ["DivTc", "div_tc"] | ["div_lit"] => Some(ArithOp::Div),
        ["RemTc", "rem_tc"] | ["rem_lit"] => Some(ArithOp::Rem),
        ["NegTc", "neg_tc"] => Some(ArithOp::Neg),
        _ => None,
    }
}

impl<'tcx> OperatorCollector<'_, 'tcx> {
    fn operand(&self, ty: Ty<'tcx>) -> Operand {
        let ty = ty.peel_refs();
        match ty.kind() {
            ty::Uint(uint) => Operand::Machine {
                bits: uint
                    .bit_width()
                    .map_or(self.pointer_bits, |bits| u32::try_from(bits).unwrap_or(0)),
                signed: false,
            },
            ty::Int(int) => Operand::Machine {
                bits: int
                    .bit_width()
                    .map_or(self.pointer_bits, |bits| u32::try_from(bits).unwrap_or(0)),
                signed: true,
            },
            ty::Float(_) => Operand::Int,
            ty::Adt(adt, _)
                if trust_wp_std_path(self.tcx, adt.did())
                    .is_some_and(|path| path == ["logic", "int", "Int"]) =>
            {
                Operand::Int
            }
            _ => Operand::Other(ty.to_string()),
        }
    }

    /// An integer literal, or the vehicle's `Int` literal: a minus on it is
    /// a negative literal, which the parser reads as no operator either.
    fn is_literal(&self, expr: &Expr<'_>) -> bool {
        match expr.kind {
            ExprKind::Lit(_) => true,
            ExprKind::Call(callee, _) => self
                .callee(callee)
                .and_then(|def_id| trust_wp_std_path(self.tcx, def_id))
                .is_some_and(|path| path == ["__spec_tc", "int_lit"]),
            _ => false,
        }
    }

    fn callee(&self, callee: &Expr<'_>) -> Option<DefId> {
        match self.typeck.node_type_opt(callee.hir_id)?.kind() {
            ty::FnDef(def_id, _) => Some(*def_id),
            _ => None,
        }
    }

    /// Record `expr` if it is an operator; `false` when its operands must not
    /// be walked (the program expression a `for` loop's clause is checked
    /// beside, which is no part of the clause).
    fn record(&mut self, expr: &'tcx Expr<'tcx>) -> bool {
        match expr.kind {
            ExprKind::Call(callee, args) => {
                let Some(ty::FnDef(def_id, generic_args)) = self
                    .typeck
                    .node_type_opt(callee.hir_id)
                    .map(|ty| *ty.kind())
                else {
                    return true;
                };
                let Some(path) = trust_wp_std_path(self.tcx, def_id) else {
                    return true;
                };
                if path == ["__spec_tc", "dead"] || path.last().is_some_and(|last| last == "dead") {
                    self.dropped = true;
                    return true;
                }
                if path == ["__spec_tc", "for_loop_tc"] {
                    if let Some(clause) = args.get(1) {
                        self.visit_expr(clause);
                    }
                    return false;
                }
                let Some(op) = stub_operator(&path) else {
                    return true;
                };
                if op == ArithOp::Neg && args.first().is_some_and(|arg| self.is_literal(arg)) {
                    return true;
                }
                let operand = match generic_args.skip_binder().types().next() {
                    Some(ty) => self.operand(ty),
                    None => Operand::Other("an unknown type".to_string()),
                };
                self.sites.push((op, operand));
                true
            }
            ExprKind::Binary(op, left, _) => {
                use rustc_hir::BinOpKind as B;
                let kind = match op.node {
                    B::Add => ArithOp::Add,
                    B::Sub => ArithOp::Sub,
                    B::Mul => ArithOp::Mul,
                    B::Div => ArithOp::Div,
                    B::Rem => ArithOp::Rem,
                    B::Shl => ArithOp::Shl,
                    B::Shr => ArithOp::Shr,
                    _ => return true,
                };
                if let Some(ty) = self.typeck.expr_ty_adjusted_opt(left) {
                    let operand = self.operand(ty);
                    self.sites.push((kind, operand));
                }
                true
            }
            ExprKind::Unary(rustc_hir::UnOp::Neg, operand) => {
                if !self.is_literal(operand) {
                    if let Some(ty) = self.typeck.expr_ty_adjusted_opt(operand) {
                        let operand = self.operand(ty);
                        self.sites.push((ArithOp::Neg, operand));
                    }
                }
                true
            }
            ExprKind::Unary(rustc_hir::UnOp::Not, operand) => {
                // Only a complement is recorded: boolean `!` is the parser's
                // default reading.
                if let Some(ty) = self.typeck.expr_ty_adjusted_opt(operand) {
                    if ty.peel_refs().is_integral() {
                        let operand = self.operand(ty);
                        self.sites.push((ArithOp::Not, operand));
                    }
                }
                true
            }
            _ => true,
        }
    }
}

impl<'tcx> Visitor<'tcx> for OperatorCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if self.record(expr) {
            rustc_hir::intravisit::walk_expr(self, expr);
        }
    }
}

#[cfg(test)]
#[path = "spec_arith_tests.rs"]
mod tests;
