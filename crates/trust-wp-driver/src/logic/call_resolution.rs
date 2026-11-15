// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What each call of a logic body denotes, as rustc resolved it (D-136).
//!
//! The verifier reads a logic body as TEXT (the `trust-wp:logic_body:`
//! marker) and parses it into a formula whose calls carry only the name they
//! are written with. rustc type-checks the same body inside the closure
//! `trust-wp-macros` emits for it (`spec_tc::logic_body_statement`), so rustc
//! knows the definition each call denotes however it is written: through a
//! `use ... as` rename, a re-export or a glob of one, a `self::` or `super::`
//! path, a fn item bound to a local, or a method of a type a trait bounds.
//! This module records, for every logic function, each call of that closure
//! with the definitions it denotes, and checks that every call of the parsed
//! body has a counterpart there. The callee-precondition walk owes what those
//! definitions require (`logic_fn_verify::callee_preconditions`).
//!
//! The check runs on the body as the identity pass left it and BEFORE
//! qualified calls are inlined (`extract_logic_fn_defs`): an inlined body's
//! calls are written in another function's scope, and Creusot owes a caller
//! nothing for the calls inside its callee's body. The walk reads the body
//! AFTER inlining, so what inlining does to a call is recorded here too
//! (`ParsedCalls`): which calls of the written body the inlined body still
//! holds as themselves, and whether an inlined call's arguments call anything,
//! which the substitution moves under the callee's branches, drops or copies.
//!
//! The same resolution settles what the body MEANS (`settle_spelled_calls`),
//! because the parsed body is also the function's defining axiom and the
//! parser and the encoder read some spellings as builtins whatever the name
//! resolves to: `view(e)` is the view of `e`, a call named `seq` a sequence
//! literal, a call named `Some` the `Option` constructor. A call the identity
//! pass left by its spelling is rewritten to the unique id of the lane's
//! function rustc resolved it to, as the identity pass names a call it
//! resolves; a call whose spelling is read as something rustc says it is not,
//! and a call rustc never resolved whose name the crate binds to something
//! else, make the body MISREAD: it is hidden from every reader of the
//! definition and its own goals are refused.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use rustc_hir::{
    def::{DefKind, Namespace, Res},
    def_id::{DefId, LocalDefId, LOCAL_CRATE},
    intravisit::Visitor,
    Expr, ExprKind, Pat, PatKind, QPath, UseKind,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{GenericArgs, TyCtxt, TyKind, TypeckResults},
};
use rustc_span::Span;
use trust_wp_core::{
    formula::{PureExpr, PureExprDepthLimitedTraversalExt as _},
    logic::{identity::LOGIC_FN_ID_PREFIX, LogicFnDef},
};

/// The depth past which a body is not searched: the encoder's own budget.
const DEPTH_LIMIT: usize = 200;

/// The prefix of every name trust-wp gives a construct it synthesises (a
/// field or tuple projection, a borrow marker). Specification text may not
/// spell one (`creusot_frontend_checks::validate_reserved_binding_names`), so
/// such a call is the parser's own and denotes no user definition.
const RESERVED_PREFIX: &str = "__trust_wp_";

/// The name a call is written with, which is what the parsed body and the
/// type-checked body share: the last path segment of a path call without its
/// turbofish (`crate::m::f::<T>`, `Self::f` and `<T as Tr>::f` are all `f`),
/// the method of a method call. The callee-precondition walk reads calls
/// through this same function.
pub(crate) fn call_spelling(name: &str) -> &str {
    let stem = match name.rfind("::<") {
        Some(turbofish) if name.ends_with('>') => &name[..turbofish],
        _ => name,
    };
    stem.rsplit("::").next().unwrap_or(stem)
}

/// Whether a parsed call named `name` is one trust-wp synthesised and no
/// user definition can answer.
pub(crate) fn is_reserved_call_name(name: &str) -> bool {
    name.starts_with(RESERVED_PREFIX)
}

/// The macros a logic body may invoke whose invocation the parser keeps as a
/// call of the macro's name (`contract_parser` `primary`): the type-checked
/// body expands them, so it holds no call of that name. Every other macro is
/// refused in a logic body, and `pearlite!` is transparent.
const MACRO_CALL_NAMES: &[&str] = &["proof_assert", "seq"];

/// The calls the contract parser reads as a builtin by their spelling alone,
/// with their argument count: a bare `view(e)` is `PureExpr::View` and a bare
/// `final_value(e)` a final value (`contract_parser`
/// `call_or_reference_form`), whatever the name resolves to. Pinned to the
/// parser by `the_builtin_call_spellings_are_the_parsers`.
const BUILTIN_CALL_SPELLINGS: &[(&str, usize)] = &[("view", 1), ("final_value", 1)];

/// The calls the type-check vehicle writes as a helper of its own by their
/// spelling alone (`trust-wp-macros` `spec_tc::encode`, `Expr::Call`), so
/// rustc never resolves the name the body wrote: a one-argument `inv(..)`.
/// Creusot leaves `inv` to rustc (`creusot-std-proc` `pretyping`). The
/// vehicle's `old(..)` is not here: Creusot's pretyping reads that spelling
/// as its intrinsic too, whatever `old` names in scope.
const VEHICLE_HELPER_CALLS: &[(&str, usize)] = &[("inv", 1)];

/// One call of a logic body's type-checked form.
#[derive(Debug, Clone)]
pub(crate) struct TypedCall {
    /// The name the call is written with (`call_spelling`); `None` for an
    /// operator, which the parsed body keeps as an operator, and for a callee
    /// that is not a path.
    pub(crate) spelling: Option<String>,
    /// The definition rustc names and, for a trait method, the impl item
    /// that runs. Empty when the callee is none rustc can name (a function
    /// pointer).
    pub(crate) callees: Vec<DefId>,
    /// The vehicle wrote the call itself (a `::trust_wp_std::` path or a
    /// `__trust_wp_tc_` method), for an operator, a literal, a quantifier or
    /// a Pearlite form of the body: it is the counterpart of a parsed call
    /// only where it stands for one (`inv(x)`), and never of a call written
    /// inside a subterm the vehicle dropped.
    pub(crate) synthesized: bool,
    /// For a call of a path callee (`f(x)`, `m::f(x)`, a local bound to a fn
    /// item), its argument count; `None` for a method, an operator or a
    /// struct literal.
    pub(crate) path_arity: Option<usize>,
    /// The callee path is one unqualified segment (`view(x)`), the only form
    /// the parser reads as a builtin.
    pub(crate) bare: bool,
    /// rustc names the callee by its fn-item type, so `callees[0]` is the
    /// definition the call names; otherwise it is the trait method of an
    /// overloaded call, or nothing.
    pub(crate) fn_item: bool,
}

/// What rustc resolved one logic body's calls to.
#[derive(Debug, Clone, Default)]
pub(crate) struct TypedBody {
    calls: Vec<TypedCall>,
    /// Every name the body binds as a local: the function's parameters and
    /// each binding of a pattern in the type-checked body.
    locals: HashSet<String>,
    /// The vehicle replaced a subterm by an unconstrained value
    /// (`drops_a_subterm`), so a call written in it has no counterpart here.
    dropped_subterm: bool,
}

/// The type-checked form of every logic body that has one, by
/// crate-qualified path. A path several local functions print as has none.
#[derive(Debug, Default)]
pub(crate) struct TypedBodies {
    by_fn: HashMap<String, TypedBody>,
}

/// What a logic function's body calls, as rustc resolved it, and what
/// inlining does to the calls it is written with.
#[derive(Debug, Clone)]
pub(crate) enum LogicBodyCalls {
    /// Every call of the parsed body has a counterpart among `calls`
    /// (`settle_spelled_calls` makes a body with one that has none misread).
    Typed {
        calls: Vec<TypedCall>,
        parsed: ParsedCalls,
    },
    /// The body has no type-checked form: `trust-wp-macros` emitted none (a
    /// body its lowering does not read as Rust), the driver did not find it,
    /// or the function's path names another function too, so which body's
    /// form it is cannot be told. `parsed` is the written body's, or, for a
    /// path several functions print as, the union of theirs.
    Untyped { parsed: ParsedCalls },
    /// The parsed body reads a call as something rustc says it is not, or
    /// cannot say it is (`settle_spelled_calls`); why.
    Misread { why: String },
}

/// The calls of a logic body as the identity pass left it, read against the
/// inlining `extract_logic_fn_defs` then applies to it. Inlining replaces a
/// call by its callee's body with the arguments substituted for the
/// parameters, so the walk, which reads the inlined body, meets calls the
/// written body never made and misses, moves or copies the ones in the
/// arguments.
#[derive(Debug, Clone, Default)]
pub(crate) struct ParsedCalls {
    /// The name of every call of the written body that is not inlined, each
    /// once, triggers aside: the calls the inlined body still holds as
    /// themselves, which alone can be the counterpart of a type-checked call
    /// (logic_fn_callee_precondition_view_beside_inlined_view.rs).
    pub(crate) kept: Vec<String>,
    /// An inlined call whose arguments call something: Creusot evaluates an
    /// argument before the call, and the substitution puts it under the
    /// callee's branches, drops it or copies it
    /// (logic_fn_callee_precondition_inlined_argument_under_branch.rs).
    pub(crate) inlined_calling_argument: Option<String>,
    /// The first call of the written body, inlined or not.
    pub(crate) first: Option<String>,
    /// The body is nested deeper than the search reaches.
    pub(crate) beyond_reach: bool,
}

impl ParsedCalls {
    /// `body`'s calls, with `is_inlined(name, arity)` the inliner's own test
    /// of whether it replaces a call.
    fn of(body: &PureExpr, is_inlined: &dyn Fn(&str, usize) -> bool) -> Self {
        let mut parsed = Self::default();
        let body = without_triggers(body);
        parsed.beyond_reach = body.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
            let (name, args) = match node {
                PureExpr::LogicFnCall { name, args } => (name, args),
                // The inliner replaces path calls only.
                PureExpr::MethodCall { method, .. } => {
                    if !is_reserved_call_name(method) {
                        parsed.first.get_or_insert_with(|| method.clone());
                    }
                    parsed.kept.push(method.clone());
                    return false;
                }
                _ => return false,
            };
            if !is_reserved_call_name(name) {
                parsed.first.get_or_insert_with(|| name.clone());
            }
            if !is_inlined(name, args.len()) {
                parsed.kept.push(name.clone());
                return false;
            }
            if parsed.inlined_calling_argument.is_none() && args.iter().any(calls_anything) {
                parsed.inlined_calling_argument = Some(name.clone());
            }
            false
        });
        parsed
    }

    /// Both bodies' calls: a record found by a path two functions print as
    /// may be either's.
    fn union(mut self, other: Self) -> Self {
        self.kept.extend(other.kept);
        self.inlined_calling_argument = self
            .inlined_calling_argument
            .or(other.inlined_calling_argument);
        self.first = self.first.or(other.first);
        self.beyond_reach |= other.beyond_reach;
        self
    }
}

/// Whether `expr` holds a call trust-wp did not synthesise; past the depth
/// budget, yes.
fn calls_anything(expr: &PureExpr) -> bool {
    expr.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| match node {
        PureExpr::LogicFnCall { name, .. } | PureExpr::MethodCall { method: name, .. } => {
            !is_reserved_call_name(name)
        }
        _ => false,
    })
}

thread_local! {
    /// Per logic function, by crate-qualified path. Session scoped: written
    /// once per extraction, read by the logic lane of the same session.
    static LOGIC_BODY_CALLS: RefCell<HashMap<String, LogicBodyCalls>> =
        RefCell::new(HashMap::new());
}

/// The type-checked form of every logic body in `defs`. A function is found
/// by its path (`def_ids_by_path`), which two functions declared in two
/// blocks of one body share (`host::k`): such a path has no type-checked
/// form, since the one found by it may be the other function's
/// (logic_fn_callee_precondition_block_local_same_path.rs).
pub(crate) fn typed_bodies(
    tcx: TyCtxt<'_>,
    defs: &[LogicFnDef],
    def_ids_by_path: &HashMap<String, DefId>,
) -> TypedBodies {
    let shared = shared_fn_paths(tcx);
    let by_fn = defs
        .iter()
        .filter(|def| !shared.contains(def.full_path()))
        .filter_map(|def| {
            let local = def_ids_by_path.get(def.full_path())?.as_local()?;
            Some((def.full_path().to_string(), typed_body(tcx, local)?))
        })
        .collect();
    TypedBodies { by_fn }
}

/// Record every logic function's calls. `defs` must hold the bodies the
/// identity pass resolved and `settle_spelled_calls` settled, before any
/// inlining; `misread` is what that settling found, and `is_inlined(name,
/// arity, full_path)` is the inliner's own test of whether it replaces a call
/// so named in the body of the function at `full_path`.
pub(crate) fn record_logic_body_calls(
    tcx: TyCtxt<'_>,
    defs: &[LogicFnDef],
    typed: TypedBodies,
    misread: &HashMap<String, String>,
    is_inlined: &dyn Fn(&str, usize, &str) -> bool,
) {
    let mut typed = typed;
    let mut table: HashMap<String, LogicBodyCalls> = HashMap::with_capacity(defs.len());
    for def in defs {
        let parsed = ParsedCalls::of(def.body(), &|name, arity| {
            is_inlined(name, arity, def.full_path())
        });
        let calls = if let Some(why) = misread.get(def.full_path()) {
            LogicBodyCalls::Misread { why: why.clone() }
        } else {
            match (
                typed.by_fn.remove(def.full_path()),
                table.remove(def.full_path()),
            ) {
                // A path several functions print as keeps whichever of them
                // is misread.
                (_, Some(misread @ LogicBodyCalls::Misread { .. })) => misread,
                (Some(TypedBody { calls, .. }), _) => LogicBodyCalls::Typed { calls, parsed },
                (None, other) => LogicBodyCalls::Untyped {
                    parsed: match other {
                        Some(
                            LogicBodyCalls::Untyped { parsed: other }
                            | LogicBodyCalls::Typed { parsed: other, .. },
                        ) => parsed.union(other),
                        _ => parsed,
                    },
                },
            }
        };
        if std::env::var_os("TRUST_WP_LOGIC_CALL_TRACE").is_some() {
            trace_calls(tcx, def.full_path(), &calls);
        }
        table.insert(def.full_path().to_string(), calls);
    }
    LOGIC_BODY_CALLS.with(|cell| *cell.borrow_mut() = table);
}

/// Every crate-qualified path (as `extract_logic_fn_defs` spells one) that
/// more than one local function prints as.
pub(crate) fn shared_fn_paths(tcx: TyCtxt<'_>) -> HashSet<String> {
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    let mut seen = HashSet::new();
    let mut shared = HashSet::new();
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            let path = format!("{crate_name}::{}", tcx.def_path_str(def_id));
            if !seen.insert(path.clone()) {
                shared.insert(path);
            }
        }
    }
    shared
}

fn trace_calls(tcx: TyCtxt<'_>, full_path: &str, calls: &LogicBodyCalls) {
    match calls {
        LogicBodyCalls::Typed { calls, .. } => {
            for call in calls {
                let callees: Vec<String> = call
                    .callees
                    .iter()
                    .map(|&def_id| tcx.def_path_str(def_id))
                    .collect();
                eprintln!(
                    "trust-wp: logic-call {full_path}: {:?} -> {callees:?}",
                    call.spelling
                );
            }
        }
        LogicBodyCalls::Untyped { .. } => eprintln!("trust-wp: logic-call {full_path}: UNTYPED"),
        LogicBodyCalls::Misread { why } => {
            eprintln!("trust-wp: logic-call {full_path}: MISREAD {why}");
        }
    }
}

/// The recorded calls of the logic function at `full_path`.
pub(crate) fn logic_body_calls(full_path: &str) -> Option<LogicBodyCalls> {
    LOGIC_BODY_CALLS.with(|cell| cell.borrow().get(full_path).cloned())
}

/// The type-checked form of `def_id`'s body, or `None` when there is none.
fn typed_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<TypedBody> {
    let closure = crate::callbacks::spec_typecheck::logic_body_tc_closure(tcx, def_id)?;
    let body = tcx.hir_body(closure.body);
    let mut collector = CallCollector {
        tcx,
        typeck: tcx.typeck(def_id),
        owner: def_id.to_def_id(),
        calls: Vec::new(),
        locals: tcx
            .fn_arg_idents(def_id.to_def_id())
            .iter()
            .flatten()
            .map(|ident| ident.name.to_string())
            .collect(),
    };
    collector.visit_expr(body.value);
    Some(TypedBody {
        dropped_subterm: drops_a_subterm(tcx, &collector.calls),
        calls: collector.calls,
        locals: collector.locals,
    })
}

struct CallCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    owner: DefId,
    calls: Vec<TypedCall>,
    locals: HashSet<String>,
}

impl<'tcx> Visitor<'tcx> for CallCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.record(expr);
        rustc_hir::intravisit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
        if let PatKind::Binding(_, _, ident, _) = pat.kind {
            self.locals.insert(ident.name.to_string());
        }
        rustc_hir::intravisit::walk_pat(self, pat);
    }
}

impl<'tcx> CallCollector<'_, 'tcx> {
    fn record(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call(callee, args) => {
                let spelling = path_spelling(callee);
                // A fn item, called directly or through a local it was bound
                // to, is named by the callee's own type; any other callee
                // (a closure, a mapping) by the overloaded call rustc
                // selected.
                let fn_item = match self
                    .typeck
                    .node_type_opt(callee.hir_id)
                    .map(|ty| *ty.kind())
                {
                    Some(TyKind::FnDef(def_id, args)) => Some((def_id, args.skip_binder())),
                    _ => None,
                };
                let named = fn_item.or_else(|| {
                    self.typeck
                        .type_dependent_def_id(expr.hir_id)
                        .map(|def_id| (def_id, self.typeck.node_args(expr.hir_id)))
                });
                let callees =
                    named.map_or_else(Vec::new, |(def_id, args)| self.callees(def_id, args));
                self.calls.push(TypedCall {
                    spelling,
                    callees,
                    synthesized: is_vehicle_path(callee),
                    path_arity: matches!(callee.kind, ExprKind::Path(_)).then_some(args.len()),
                    bare: is_bare_path(callee),
                    fn_item: fn_item.is_some(),
                });
            }
            ExprKind::MethodCall(segment, ..) => {
                let callees = self
                    .typeck
                    .type_dependent_def_id(expr.hir_id)
                    .map_or_else(Vec::new, |def_id| {
                        self.callees(def_id, self.typeck.node_args(expr.hir_id))
                    });
                let spelling = self
                    .helper_spelling(&callees)
                    .unwrap_or_else(|| call_spelling(segment.ident.as_str()).to_string());
                self.calls.push(TypedCall {
                    spelling: Some(spelling),
                    callees,
                    synthesized: segment.ident.as_str().starts_with(VEHICLE_METHOD_PREFIX),
                    path_arity: None,
                    bare: false,
                    fn_item: false,
                });
            }
            // A struct literal is a constructor call in the parsed body.
            ExprKind::Struct(qpath, ..) => {
                let res = self.typeck.qpath_res(qpath, expr.hir_id);
                self.calls.push(TypedCall {
                    spelling: qpath_spelling(qpath),
                    callees: res.opt_def_id().into_iter().collect(),
                    synthesized: false,
                    path_arity: None,
                    bare: false,
                    fn_item: false,
                });
            }
            // An operator a type overloads is a call the parsed body keeps as
            // an operator.
            ExprKind::Binary(..)
            | ExprKind::Unary(..)
            | ExprKind::Index(..)
            | ExprKind::AssignOp(..) => {
                if let Some(def_id) = self.typeck.type_dependent_def_id(expr.hir_id) {
                    let callees = self.callees(def_id, self.typeck.node_args(expr.hir_id));
                    self.calls.push(TypedCall {
                        spelling: None,
                        callees,
                        synthesized: false,
                        path_arity: None,
                        bare: false,
                        fn_item: false,
                    });
                }
            }
            _ => {}
        }
    }

    /// `def_id`, the impl item that runs when it is a trait method rustc can
    /// resolve at `args`, and, for a `trust_wp_std` type-check helper that
    /// stands for a logic trait's method (`x@` is `ViewTc`, `a[i]` is
    /// `IndexTc`), that method and its impl item.
    fn callees(&self, def_id: DefId, args: GenericArgs<'tcx>) -> Vec<DefId> {
        let mut callees = vec![def_id];
        callees.extend(crate::trait_credit::impl_item_that_runs(
            self.tcx, def_id, args, self.owner,
        ));
        if let Some(method) = helper_trait_method(self.tcx, def_id) {
            callees.push(method);
            callees.extend(crate::trait_credit::impl_item_that_runs(
                self.tcx, method, args, self.owner,
            ));
        }
        callees
    }

    /// The name a type-check helper's logic method is written with, which is
    /// how the parsed body spells the call when it keeps one (`index_logic`).
    fn helper_spelling(&self, callees: &[DefId]) -> Option<String> {
        let helper = *callees.first()?;
        let method = helper_trait_method(self.tcx, helper)?;
        Some(self.tcx.item_name(method).to_string())
    }
}

/// For a method of a `trust_wp_std` type-check helper trait whose one
/// supertrait with methods declares exactly one (`ViewTc: View`,
/// `IndexTc<I>: IndexLogic<I>`), that method: the helper is the vehicle's
/// spelling of a call to it, and its blanket impl hides the impl that runs.
fn helper_trait_method(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    if def_id.is_local() || tcx.crate_name(def_id.krate).as_str() != "trust_wp_std" {
        return None;
    }
    if !tcx
        .item_name(def_id)
        .as_str()
        .starts_with(VEHICLE_METHOD_PREFIX)
    {
        return None;
    }
    let helper_trait = tcx.trait_of_assoc(def_id)?;
    let methods_of = |trait_id: DefId| -> Vec<DefId> {
        tcx.associated_items(trait_id)
            .in_definition_order()
            .filter(|item| matches!(item.kind, rustc_middle::ty::AssocKind::Fn { .. }))
            .map(|item| item.def_id)
            .collect()
    };
    // The implicit sizedness supertraits declare no method.
    let supertrait_methods: Vec<Vec<DefId>> = tcx
        .explicit_super_clauses_of(helper_trait)
        .skip_binder()
        .iter()
        .filter_map(|(clause, _)| {
            clause
                .as_trait_clause()
                .map(|tc| tc.skip_binder().trait_ref.def_id)
        })
        .map(methods_of)
        .filter(|methods| !methods.is_empty())
        .collect();
    match supertrait_methods.as_slice() {
        [methods] => match methods.as_slice() {
            [method] => Some(*method),
            _ => None,
        },
        _ => None,
    }
}

/// The prefix of the methods the vehicle calls for Pearlite operators
/// (`x@` is `x.__trust_wp_tc_view()`); specification text may not spell one.
const VEHICLE_METHOD_PREFIX: &str = "__trust_wp_tc_";

/// Whether `callee` is a path the vehicle writes for a helper of its own:
/// global and rooted at `trust_wp_std` (`::trust_wp_std::__spec_tc::inv`,
/// `::trust_wp_std::logic::OrdLogic::lt_log`).
fn is_vehicle_path(callee: &Expr<'_>) -> bool {
    let rooted = |path: &rustc_hir::Path<'_>| {
        path.is_global()
            && path
                .segments
                .get(1)
                .is_some_and(|segment| segment.ident.as_str() == "trust_wp_std")
    };
    match callee.kind {
        ExprKind::Path(QPath::Resolved(None, path)) => rooted(path),
        ExprKind::Path(QPath::TypeRelative(qself, _)) => matches!(
            qself.kind,
            rustc_hir::TyKind::Path(QPath::Resolved(None, path)) if rooted(path)
        ),
        _ => false,
    }
}

/// Whether `callee` is a path of one unqualified segment (`view`), not
/// `m::view`, `::view` or `<T as Tr>::view`.
fn is_bare_path(callee: &Expr<'_>) -> bool {
    matches!(
        callee.kind,
        ExprKind::Path(QPath::Resolved(None, path)) if !path.is_global() && path.segments.len() == 1
    )
}

/// The last segment of a path callee, `None` for any other callee.
fn path_spelling(callee: &Expr<'_>) -> Option<String> {
    match callee.kind {
        ExprKind::Path(ref qpath) => qpath_spelling(qpath),
        _ => None,
    }
}

fn qpath_spelling(qpath: &QPath<'_>) -> Option<String> {
    let segment = match qpath {
        QPath::Resolved(_, path) => path.segments.last()?,
        QPath::TypeRelative(_, segment) => segment,
    };
    Some(call_spelling(segment.ident.as_str()).to_string())
}

/// Whether the vehicle replaced a subterm of the body by an unconstrained
/// value (`__spec_tc::dead`: an array, a literal pattern, a flat `Fn`
/// predicate with no argument before its result, a `pearlite!` it cannot
/// lower), whose calls the type-checked body then does not hold. Pearlite's
/// own `dead` is spelled the same way and counts as a drop.
fn drops_a_subterm(tcx: TyCtxt<'_>, calls: &[TypedCall]) -> bool {
    calls.iter().flat_map(|call| &call.callees).any(|&def_id| {
        !def_id.is_local()
            && tcx.crate_name(def_id.krate).as_str() == "trust_wp_std"
            && tcx.item_name(def_id).as_str() == "dead"
    })
}

/// `body` with every quantifier's trigger patterns removed. A trigger is an
/// instantiation hint: it is never evaluated, owes nothing, and the vehicle
/// drops it (`spec_tc::lower`), so a call in one has no counterpart to meet.
pub(crate) fn without_triggers(body: &PureExpr) -> PureExpr {
    body.rewrite_bottom_up_with_depth_limit(DEPTH_LIMIT, |node| match node {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } if !triggers.is_empty() => PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers: Vec::new(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } if !triggers.is_empty() => PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers: Vec::new(),
        },
        other => other,
    })
}

/// What settling one body's spelled calls found.
#[derive(Debug, PartialEq)]
enum Settled {
    /// Nothing to change.
    Kept,
    /// The body with its renamed calls named by their definitions' ids.
    Rewritten(PureExpr),
    /// The body reads a call as something rustc says it is not, or cannot
    /// say it is; why.
    Misread(String),
}

/// Settle what every logic body in `defs` means against what rustc resolved
/// its calls to (`typed`), and return why each misread body is misread, by
/// crate-qualified path. `defs` must hold the bodies the identity pass
/// resolved, before any inlining.
///
/// A call the identity pass left spelled as written that rustc resolves to a
/// free function of the lane is renamed to that function's unique id, the
/// name the identity pass gives a call it resolves (`np(y)` under
/// `use crate::needs_pos as np;`, logic_fn_body_seq_call_renamed.rs). A body
/// is misread when the parser reads a call's spelling as a builtin rustc says
/// it is not (logic_fn_body_view_call_renamed.rs), when a call left spelled
/// denotes what its spelling does not name, or what the lane never reads
/// (a program function), and when a call rustc never resolved is spelled with
/// a name the crate or the body binds to something else
/// (logic_fn_callee_precondition_alias_onto_inv.rs). So is a settled body
/// holding a call with no counterpart in the type-checked form
/// (`unmatched_call`): the identity pass named it by a definition rustc did
/// not resolve it to (logic_fn_body_block_local_name_shadowing_read_by_caller.rs),
/// or rustc never resolved it. A misread body is hidden
/// (`hide_misread_body`), since it is also the function's defining axiom and
/// every caller unfolds it
/// (logic_fn_body_view_call_renamed_through_uncontracted_callee.rs).
pub(crate) fn settle_spelled_calls(
    tcx: TyCtxt<'_>,
    defs: &mut [LogicFnDef],
    typed: &TypedBodies,
) -> HashMap<String, String> {
    let rebound = rebound_value_names(tcx);
    let lane: HashMap<DefId, (String, usize)> = defs
        .iter()
        .filter_map(|def| {
            let def_id = crate::logic::identity::member_def_id(def.name())?;
            Some((def_id, (def.name().to_string(), def.params().len())))
        })
        .collect();
    let describe = |def_id: DefId| DefinitionFacts::of(tcx, def_id);
    let mut misread = HashMap::new();
    for def in defs.iter_mut() {
        let settled = match typed.by_fn.get(def.full_path()) {
            Some(body) => settle_and_match(def.body(), body, &lane, &rebound, &describe),
            None => match untyped_misread(def.body(), def.params(), &rebound) {
                Some(why) => Settled::Misread(why),
                None => Settled::Kept,
            },
        };
        match settled {
            Settled::Kept => {}
            Settled::Rewritten(body) => def.set_body(body),
            Settled::Misread(why) => {
                hide_misread_body(def);
                misread.insert(def.full_path().to_string(), why);
            }
        }
    }
    misread
}

/// Hide a misread body from every reader of the definition: an opaque
/// function's body is no defining axiom anywhere, and the appended `false`
/// guard is the one an opaque definition carries (`attrs`
/// `append_opaque_guard_if_needed`), which no caller owes and no own goal
/// assumes (`logic_fn_verify::callee_preconditions` `owed_requires`,
/// `own_premises`).
fn hide_misread_body(def: &mut LogicFnDef) {
    if def.is_opaque() {
        return;
    }
    def.set_is_opaque(true);
    def.extend_requires([PureExpr::Bool(false)]);
}

/// What settling reads of a definition rustc resolved a call to.
#[derive(Debug, Clone, PartialEq)]
struct DefinitionFacts {
    local: bool,
    kind: DefinitionKind,
    /// The name the definition is declared with; a constructor's is its
    /// variant's or struct's.
    name: Option<String>,
    /// The definition is `trust_wp_std`'s own.
    std: bool,
    path: String,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum DefinitionKind {
    FreeFn,
    AssocFn,
    Ctor,
    Other,
}

impl DefinitionFacts {
    fn of(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
        let kind = match tcx.def_kind(def_id) {
            DefKind::Fn => DefinitionKind::FreeFn,
            DefKind::AssocFn => DefinitionKind::AssocFn,
            DefKind::Ctor(..) => DefinitionKind::Ctor,
            _ => DefinitionKind::Other,
        };
        Self {
            local: def_id.is_local(),
            kind,
            name: definition_name(tcx, def_id),
            std: !def_id.is_local() && tcx.crate_name(def_id.krate).as_str() == "trust_wp_std",
            path: tcx.def_path_str(def_id),
        }
    }
}

/// The name `def_id` is declared with: a constructor has none of its own and
/// is named by its variant or struct.
fn definition_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    tcx.opt_item_name(def_id)
        .or_else(|| {
            matches!(tcx.def_kind(def_id), DefKind::Ctor(..))
                .then(|| tcx.opt_item_name(tcx.parent(def_id)))
                .flatten()
        })
        .map(|name| name.to_string())
}

/// `settle_typed_body`, then the settled body read against the type-checked
/// form: every call it holds must have a counterpart there
/// (`unmatched_call`), or what the body means is not what rustc checked.
fn settle_and_match(
    body: &PureExpr,
    typed: &TypedBody,
    lane: &HashMap<DefId, (String, usize)>,
    rebound: &ReboundNames,
    describe: &dyn Fn(DefId) -> DefinitionFacts,
) -> Settled {
    let settled = settle_typed_body(body, typed, lane, rebound, describe);
    let read = match &settled {
        Settled::Misread(_) => return settled,
        Settled::Rewritten(rewritten) => rewritten,
        Settled::Kept => body,
    };
    match unmatched_call(read, &typed.calls, !typed.dropped_subterm) {
        Some(why) => Settled::Misread(why),
        None => settled,
    }
}

/// `settle_spelled_calls` for a body with a type-checked form.
fn settle_typed_body(
    body: &PureExpr,
    typed: &TypedBody,
    lane: &HashMap<DefId, (String, usize)>,
    rebound: &ReboundNames,
    describe: &dyn Fn(DefId) -> DefinitionFacts,
) -> Settled {
    // A call the parser reads as a builtin by its spelling.
    for call in &typed.calls {
        let (Some(spelling), Some(arity)) = (call.spelling.as_deref(), call.path_arity) else {
            continue;
        };
        if call.synthesized || !call.bare || !BUILTIN_CALL_SPELLINGS.contains(&(spelling, arity)) {
            continue;
        }
        let named = call
            .callees
            .first()
            .filter(|_| call.fn_item)
            .map(|&d| describe(d));
        if named.as_ref().is_some_and(|facts| {
            facts.std
                && facts.kind == DefinitionKind::FreeFn
                && facts.name.as_deref() == Some(spelling)
        }) {
            continue;
        }
        return Settled::Misread(format!(
            "a call `{spelling}(..)` that rustc resolves to {}, which the contract parser reads \
             as the `{spelling}` builtin",
            named.map_or_else(
                || "no fn item".to_string(),
                |facts| format!("`{}`", facts.path)
            )
        ));
    }
    // A call the vehicle writes as its own helper, so rustc never resolved
    // the name the body wrote.
    for &(name, arity) in VEHICLE_HELPER_CALLS {
        if holds_call(body, name, arity) {
            if let Some(binder) = rebound.binder_of(name, &typed.locals) {
                return Settled::Misread(format!(
                    "a call `{name}(..)`, which the type-check vehicle writes as its own \
                     helper whatever the name denotes, while {binder} binds `{name}`"
                ));
            }
        }
    }
    let mut renamed: HashMap<String, String> = HashMap::new();
    let mut spelled: Vec<(String, Vec<(String, usize)>)> = Vec::new();
    if spelled_calls(body, &mut spelled) {
        return Settled::Misread("a call nested deeper than the body search reaches".to_string());
    }
    for (spelling, written) in &spelled {
        let resolved: Vec<&TypedCall> = typed
            .calls
            .iter()
            .filter(|call| {
                call.path_arity.is_some()
                    && !call.synthesized
                    && call.spelling.as_deref() == Some(spelling.as_str())
            })
            .collect();
        let helper = typed
            .calls
            .iter()
            .any(|call| call.synthesized && call.spelling.as_deref() == Some(spelling.as_str()));
        if resolved.is_empty() {
            // rustc resolved no call so spelled: the vehicle's helper
            // answers it (`inv`, above), or `unmatched_call` finds it.
            // Either way what the name denotes is not rustc's to say, so a
            // name something else binds is read as that something else. A
            // macro's name is not a value's: where no subterm was dropped,
            // every parsed call so named is the macro, since rustc would
            // have resolved any other.
            let only_macros =
                MACRO_CALL_NAMES.contains(&spelling.as_str()) && !typed.dropped_subterm;
            if !helper && !only_macros {
                if let Some(binder) = rebound.binder_of(spelling, &typed.locals) {
                    return Settled::Misread(format!(
                        "a call `{spelling}` rustc did not resolve, while {binder} binds \
                         `{spelling}`"
                    ));
                }
            }
            continue;
        }
        if helper {
            return Settled::Misread(format!(
                "a call spelled `{spelling}` beside a call the type-check vehicle writes under \
                 the same name, so which one a parsed call is cannot be told"
            ));
        }
        if MACRO_CALL_NAMES.contains(&spelling.as_str()) && written.len() != resolved.len() {
            return Settled::Misread(format!(
                "a call `{spelling}(..)` beside the `{spelling}!` macro, which the parser \
                 writes as a call of the same name"
            ));
        }
        match denotation(spelling, &resolved, lane, describe) {
            Denotation::Itself => {}
            Denotation::Lane { id, arity } => {
                if written
                    .iter()
                    .any(|&(_, written_arity)| written_arity != arity)
                {
                    return Settled::Misread(format!(
                        "a call spelled `{spelling}` with an argument count its definition \
                         `{id}` does not take"
                    ));
                }
                for (name, _) in written {
                    renamed.insert(name.clone(), id.clone());
                }
            }
            Denotation::Misread(why) => return Settled::Misread(why),
        }
    }
    if renamed.is_empty() {
        return Settled::Kept;
    }
    Settled::Rewritten(
        body.rewrite_bottom_up_with_depth_limit(DEPTH_LIMIT, |node| match node {
            PureExpr::LogicFnCall { name, args } => match renamed.get(&name) {
                Some(id) => PureExpr::LogicFnCall {
                    name: id.clone(),
                    args,
                },
                None => PureExpr::LogicFnCall { name, args },
            },
            other => other,
        }),
    )
}

/// What the calls rustc resolved under one spelling denote.
enum Denotation {
    /// A definition the spelling names itself: a function or constructor of
    /// another crate, an associated function or a constructor of this one,
    /// called by its own name.
    Itself,
    /// The lane's free function with this unique id and parameter count.
    Lane {
        id: String,
        arity: usize,
    },
    Misread(String),
}

fn denotation(
    spelling: &str,
    resolved: &[&TypedCall],
    lane: &HashMap<DefId, (String, usize)>,
    describe: &dyn Fn(DefId) -> DefinitionFacts,
) -> Denotation {
    let mut target = None;
    for call in resolved {
        let Some(&named) = call.callees.first().filter(|_| call.fn_item) else {
            return Denotation::Misread(format!(
                "a call spelled `{spelling}` whose callee rustc names by no fn item (a function \
                 pointer or an overloaded call)"
            ));
        };
        match target {
            None => target = Some(named),
            Some(first) if first == named => {}
            Some(_) => {
                return Denotation::Misread(format!(
                    "calls spelled `{spelling}` that rustc resolves to different definitions"
                ))
            }
        }
    }
    let Some(def_id) = target else {
        return Denotation::Itself;
    };
    let facts = describe(def_id);
    if facts.local && facts.kind == DefinitionKind::FreeFn {
        return match lane.get(&def_id) {
            Some((id, arity)) => Denotation::Lane {
                id: id.clone(),
                arity: *arity,
            },
            None => Denotation::Misread(format!(
                "a call spelled `{spelling}` that rustc resolves to the local function `{}`, \
                 which the logic lane does not read",
                facts.path
            )),
        };
    }
    let names_itself = facts.name.as_deref() == Some(spelling)
        || (facts.kind == DefinitionKind::Ctor && spelling == "Self");
    if names_itself && facts.kind != DefinitionKind::Other {
        return Denotation::Itself;
    }
    Denotation::Misread(format!(
        "a call spelled `{spelling}` that rustc resolves to `{}`, which the spelling does not \
         name: the parser and the encoder read a spelling on its own terms",
        facts.path
    ))
}

/// Every call of `body` the identity pass left spelled as written (a path
/// call whose name is no unique id and no name of trust-wp's own), grouped
/// by `call_spelling`, with each call's name and argument count; triggers
/// aside, since the vehicle drops them. `true` when the body is nested deeper
/// than the search reaches.
fn spelled_calls(body: &PureExpr, out: &mut Vec<(String, Vec<(String, usize)>)>) -> bool {
    without_triggers(body).any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
        if let PureExpr::LogicFnCall { name, args } = node {
            if !name.starts_with(LOGIC_FN_ID_PREFIX) && !is_reserved_call_name(name) {
                let spelling = call_spelling(name);
                let entry = match out.iter().position(|(s, _)| s == spelling) {
                    Some(at) => &mut out[at].1,
                    None => {
                        out.push((spelling.to_string(), Vec::new()));
                        &mut out.last_mut().expect("just pushed").1
                    }
                };
                entry.push((name.clone(), args.len()));
            }
        }
        false
    })
}

/// Whether `body` holds a path call named exactly `name` with `arity`
/// arguments; past the depth budget, yes.
fn holds_call(body: &PureExpr, name: &str, arity: usize) -> bool {
    body.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
        matches!(node, PureExpr::LogicFnCall { name: called, args } if called == name && args.len() == arity)
    })
}

/// `settle_spelled_calls` for a body with no type-checked form: nothing says
/// what any call denotes, so a body is misread when it holds a call the
/// identity pass named, whose resolution skips the scopes of blocks
/// (logic_fn_body_block_local_name_shadowing_read_by_caller.rs is the typed
/// spelling), or a call left spelled, a view or a final value, spelled with a
/// name the crate or the body binds to something else.
fn untyped_misread(body: &PureExpr, params: &[String], rebound: &ReboundNames) -> Option<String> {
    let mut locals: HashSet<String> = params.iter().cloned().collect();
    let mut spelled: Vec<String> = Vec::new();
    let mut named: Option<String> = None;
    let beyond_reach = body.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
        match node {
            PureExpr::Let { var, .. }
            | PureExpr::Forall { var, .. }
            | PureExpr::Exists { var, .. } => {
                locals.insert(var.clone());
            }
            PureExpr::Closure { params, .. } => {
                locals.extend(params.iter().map(|(param, _)| param.clone()));
            }
            PureExpr::Match { arms, .. } => {
                for arm in arms {
                    locals.extend(arm.pattern.bound_names().into_iter().map(str::to_string));
                }
            }
            PureExpr::LogicFnCall { name, .. } if name.starts_with(LOGIC_FN_ID_PREFIX) => {
                named.get_or_insert_with(|| name.clone());
            }
            PureExpr::LogicFnCall { name, .. } if !is_reserved_call_name(name) => {
                spelled.push(call_spelling(name).to_string());
            }
            PureExpr::View(_) => spelled.push("view".to_string()),
            PureExpr::Final(_) => spelled.push("final_value".to_string()),
            _ => {}
        }
        false
    });
    if beyond_reach {
        return Some(
            "a body nested deeper than the search reaches, with no type-checked form".to_string(),
        );
    }
    if let Some(name) = named {
        return Some(format!(
            "a call `{name}` the verifier named in a body with no type-checked form, so no \
             resolution of rustc's confirms the definition it names"
        ));
    }
    spelled.iter().find_map(|spelling| {
        rebound.binder_of(spelling, &locals).map(|binder| {
            format!(
                "a call spelled `{spelling}` in a body with no type-checked form, while {binder} \
                 binds `{spelling}`"
            )
        })
    })
}

/// The names the crate binds in the value namespace to something the name
/// does not itself name, each with what binds it: a local function, constant
/// or static, an import that renames a definition or brings a local one, a
/// glob import of another crate's module that does either, and, for a glob
/// import whose module is not known, every name. A constructor called by its
/// own name is read as that constructor, typed or not (`denotation`), so a
/// local one binds nothing else. Scopes are not read, so a binding anywhere
/// in the crate counts (the precedent is `trait_refinement::prepare` for type
/// names).
#[derive(Debug, Default)]
struct ReboundNames {
    by_name: HashMap<String, String>,
    /// A glob import whose module is not known: every name may be bound.
    unknown_glob: Option<String>,
}

impl ReboundNames {
    /// What binds `name` otherwise, in the crate or among `locals`.
    fn binder_of(&self, name: &str, locals: &HashSet<String>) -> Option<String> {
        if locals.contains(name) {
            return Some("a local binding of the body".to_string());
        }
        self.by_name
            .get(name)
            .or(self.unknown_glob.as_ref())
            .cloned()
    }
}

fn rebound_value_names(tcx: TyCtxt<'_>) -> ReboundNames {
    let mut rebound = ReboundNames::default();
    let crate_items = tcx.hir_crate_items(());
    for local in crate_items.definitions() {
        let def_id = local.to_def_id();
        let kind = tcx.def_kind(def_id);
        if !matches!(
            kind,
            DefKind::Fn | DefKind::Const { .. } | DefKind::Static { .. }
        ) {
            continue;
        }
        if let Some(name) = definition_name(tcx, def_id) {
            rebound.by_name.entry(name).or_insert_with(|| {
                format!(
                    "the local {} `{}`",
                    kind.descr(def_id),
                    tcx.def_path_str(def_id)
                )
            });
        }
    }
    let renames = |def_id: DefId, name: &str| {
        def_id.is_local() || definition_name(tcx, def_id).as_deref() != Some(name)
    };
    for item_id in crate_items.free_items() {
        let item = tcx.hir_item(item_id);
        // Each leaf of the item's use tree.
        for (path, use_kind) in crate::hir_use::item_use_leaves(item) {
            match use_kind {
                UseKind::Single(ident) => {
                    let name = ident.name.as_str();
                    if let Some(Res::Def(_, def_id)) = path.res.value_ns {
                        if renames(def_id, name) {
                            rebound.by_name.entry(name.to_string()).or_insert_with(|| {
                                format!("an import of `{}` as `{name}`", tcx.def_path_str(def_id))
                            });
                        }
                    }
                }
                UseKind::Glob => {
                    // A glob's path names a module or an enum in the type
                    // namespace; its variants are the enum's children.
                    let module = match path.res.type_ns {
                        Some(Res::Def(DefKind::Mod | DefKind::Enum, module)) => Some(module),
                        _ => crate::callbacks::std_prelude_glob_module(tcx, item),
                    };
                    match module {
                        // Every local definition is examined by name above.
                        Some(module) if module.is_local() => {}
                        Some(module) => {
                            for child in tcx.module_children(module) {
                                let Res::Def(kind, def_id) = child.res else {
                                    continue;
                                };
                                let name = child.ident.name.as_str();
                                if kind.ns() == Some(Namespace::ValueNS) && renames(def_id, name) {
                                    rebound.by_name.entry(name.to_string()).or_insert_with(|| {
                                        format!(
                                            "a glob import of `{}` bringing `{}` as `{name}`",
                                            tcx.def_path_str(module),
                                            tcx.def_path_str(def_id)
                                        )
                                    });
                                }
                            }
                        }
                        None => {
                            rebound.unknown_glob.get_or_insert_with(|| {
                                format!("a glob import of an unknown module at {:?}", item.span)
                            });
                        }
                    }
                }
                UseKind::Nested { .. } => {}
            }
        }
    }
    rebound
}

/// Every call of a specification other than a logic body that the contract
/// parser or the encoder reads, by its spelling, as something rustc resolved
/// it not to be, with where it is written and why: a bare `view(e)` or
/// `final_value(e)` that is not the standard function so named, a call
/// spelled otherwise than the definition rustc resolved it to (a rename, a
/// fn item bound to a local), and the type-check vehicle's own `inv(..)` in a
/// crate that binds `inv` to something else. A clause is read as TEXT, and no
/// pass settles its calls against rustc's resolution as
/// `settle_spelled_calls` settles a logic body's, so the caller refuses the
/// crate (program_ensures_view_call_renamed.rs).
pub(crate) fn misread_specification_calls(tcx: TyCtxt<'_>) -> Vec<(Span, String)> {
    let mut found = Vec::new();
    let mut inv_helper = None;
    for owner in crate::callbacks::spec_typecheck::clause_tc_bodies(tcx) {
        let mut visitor = SpecCallVisitor {
            tcx,
            typeck: tcx.typeck(owner),
            found: &mut found,
            inv_helper: &mut inv_helper,
        };
        visitor.visit_expr(tcx.hir_body_owned_by(owner).value);
    }
    if let Some(span) = inv_helper {
        if let Some(binder) = rebound_value_names(tcx).binder_of("inv", &HashSet::new()) {
            found.push((
                span,
                format!(
                    "a call `inv(..)`, which trust-wp's type-check vehicle writes as its own \
                     invariant helper whatever the name denotes, while {binder} binds `inv`"
                ),
            ));
        }
    }
    found.extend(misread_specification_names(tcx));
    found
}

/// The macros the contract parser reads by their name alone: `seq![..]` is
/// the sequence literal, `pearlite!` is transparent, `proof_assert!` is an
/// assertion (`contract_parser` `primary`, `MACRO_CALL_NAMES`).
const PARSER_READ_MACROS: &[&str] = &["seq", "pearlite", "proof_assert"];

/// The names the contract parser, the encoder or the type-check vehicle read
/// as a builtin when CALLED by a bare name, whatever the name resolves to:
/// `BUILTIN_CALL_SPELLINGS`, `VEHICLE_HELPER_CALLS`, a call named `seq` (the
/// sequence literal) and a call named `Some` (the `Option` constructor).
const SPELLING_READ_CALLS: &[&str] = &["view", "final_value", "inv", "seq", "Some"];

/// Every specification name the parser reads by its spelling where nothing
/// checks the spelling against rustc's resolution (D-240), with where it is
/// written and why. D-136's check (`SpecCallVisitor`) reads the CALLS of the
/// type-check closures the vehicle writes, so four readings escape it:
///
/// * a clause the vehicle writes no closure for (an `impl Trait` or
///   unannotated result or parameter, a chained comparison) calling a name
///   of `SPELLING_READ_CALLS` the crate binds to something else
///   (program_ensures_view_call_renamed_impl_trait_return.rs);
/// * a macro the crate defines, or imports under a name, of
///   `PARSER_READ_MACROS`: the parser reads the prelude's macro, rustc
///   expands the crate's (logic_fn_body_seq_macro_shadowed_by_user_macro.rs);
/// * a bare name the crate imports a constructor or variant under where its
///   own name differs: the encoder reads it as the variant SO NAMED, in a
///   value, a pattern or a call alike (program_ensures_variant_pattern_renamed.rs);
/// * a function or closure carrying a specification whose parameter
///   bindings share a spelling, apart only by hygiene: a clause name is then
///   one of two bindings, read as either
///   (hygienic_duplicate_param_spelling_read_as_other_param.rs).
///
/// Each is refused over the whole crate, as D-136 refuses a misread call:
/// every reader of a clause reads the same text.
fn misread_specification_names(tcx: TyCtxt<'_>) -> Vec<(Span, String)> {
    let mut found = Vec::new();
    let crate_items = tcx.hir_crate_items(());
    for local in crate_items.definitions() {
        if matches!(tcx.def_kind(local), DefKind::Macro(_)) {
            if let Some(name) = tcx.opt_item_name(local.to_def_id()) {
                if PARSER_READ_MACROS.contains(&name.as_str()) {
                    found.push((
                        tcx.def_span(local),
                        format!(
                            "a macro `{name}!` defined by the crate, while the contract parser \
                             reads every `{name}!` of a specification as the prelude's"
                        ),
                    ));
                }
            }
        }
    }
    let mut renamed_ctors: HashMap<String, String> = HashMap::new();
    for item_id in crate_items.free_items() {
        let item = tcx.hir_item(item_id);
        for (path, use_kind) in crate::hir_use::item_use_leaves(item) {
            let UseKind::Single(ident) = use_kind else {
                continue;
            };
            let name = ident.name.as_str();
            if let Some(Res::Def(DefKind::Macro(_), def_id)) = path.res.macro_ns {
                if PARSER_READ_MACROS.contains(&name)
                    && (def_id.is_local() || definition_name(tcx, def_id).as_deref() != Some(name))
                {
                    found.push((
                        item.span,
                        format!(
                            "an import of the macro `{}` as `{name}`, while the contract parser \
                         reads every `{name}!` of a specification as the prelude's",
                            tcx.def_path_str(def_id)
                        ),
                    ));
                }
            }
            for res in [path.res.type_ns, path.res.value_ns].into_iter().flatten() {
                if let Res::Def(kind @ (DefKind::Ctor(..) | DefKind::Variant), def_id) = res {
                    if definition_name(tcx, def_id).as_deref() != Some(name) {
                        // A constructor is shown as the variant or struct it builds.
                        let shown = if matches!(kind, DefKind::Ctor(..)) {
                            tcx.parent(def_id)
                        } else {
                            def_id
                        };
                        renamed_ctors.entry(name.to_string()).or_insert_with(|| {
                            format!("an import of `{}` as `{name}`", tcx.def_path_str(shown))
                        });
                    }
                }
            }
        }
    }
    found.extend(duplicate_parameter_spellings(tcx));

    let texts = specification_texts(tcx);
    let mut typed: HashMap<String, usize> = HashMap::new();
    for body in crate::callbacks::spec_typecheck::clause_tc_bodies(tcx) {
        if let Some((_, text)) = crate::callbacks::spec_typecheck::clause_tag(tcx, body) {
            *typed.entry(text).or_default() += 1;
        }
    }
    let mut written: HashMap<&str, usize> = HashMap::new();
    for (_, text, _) in &texts {
        *written.entry(text.as_str()).or_default() += 1;
    }
    let rebound = rebound_value_names(tcx);
    let no_locals = HashSet::new();
    for (kind, text, span) in &texts {
        // A logic body with no type-checked form is `untyped_misread`'s.
        let untyped = kind != "logic_body"
            && written.get(text.as_str()).copied().unwrap_or(0)
                > typed.get(text).copied().unwrap_or(0);
        for (name, called) in bare_names(text) {
            if let Some(binder) = renamed_ctors.get(name) {
                found.push((
                    *span,
                    format!(
                        "a name `{name}` in a specification, while {binder} binds it: the \
                         contract parser and the encoder read `{name}` as the constructor so \
                         named, not the one rustc resolves"
                    ),
                ));
            } else if untyped && called && SPELLING_READ_CALLS.contains(&name) {
                if let Some(binder) = rebound.binder_of(name, &no_locals) {
                    found.push((
                        *span,
                        format!(
                            "a call `{name}(..)` in a specification with no type-check closure, \
                             which the contract parser reads as the `{name}` builtin, while \
                             {binder} binds `{name}`"
                        ),
                    ));
                }
            }
        }
    }
    found
}

/// Every `trust-wp:` marker text of the crate, as (marker kind, text, the
/// attribute's span), on any node, and every unexpanded attribute's tokens
/// (kind `attr`), as `spec_arith::written_occurrences` counts them.
fn specification_texts(tcx: TyCtxt<'_>) -> Vec<(String, String, Span)> {
    let mut texts = Vec::new();
    for owner in tcx.hir_crate_items(()).owners() {
        for attrs in tcx.hir_attr_map(owner).map.values() {
            for attr in *attrs {
                if let Some(value) = crate::attr_utils::doc_marker_str(attr) {
                    if let Some((kind, rest)) = value
                        .as_str()
                        .strip_prefix("trust-wp:")
                        .and_then(|marker| marker.split_once(':'))
                    {
                        if let Some(span) = crate::attr_utils::attr_span(attr) {
                            texts.push((kind.to_string(), rest.to_string(), span));
                        }
                    }
                }
                if let rustc_attr_ir::Attribute::Tool(item)
                | rustc_attr_ir::Attribute::DeriveHelper(item) = attr
                {
                    if let rustc_attr_ir::AttrArgs::Delimited(args) = &item.args {
                        texts.push((
                            "attr".to_string(),
                            rustc_ast_pretty::pprust::tts_to_string(&args.tokens),
                            item.span,
                        ));
                    }
                }
            }
        }
    }
    texts
}

/// The bare identifiers of a specification text, each with whether it is
/// called (`name(`): not a segment after `::`, not a field or method after
/// `.`, not a path prefix before `::`, not part of a number or a lifetime.
fn bare_names(text: &str) -> Vec<(&str, bool)> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut at = 0;
    let ident_byte = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    while at < bytes.len() {
        let b = bytes[at];
        if b.is_ascii_digit() || b == b'\'' {
            at += 1;
            while at < bytes.len() && ident_byte(bytes[at]) {
                at += 1;
            }
            continue;
        }
        if !(b.is_ascii_alphabetic() || b == b'_') {
            at += 1;
            continue;
        }
        let start = at;
        while at < bytes.len() && ident_byte(bytes[at]) {
            at += 1;
        }
        let name = &text[start..at];
        let before = text[..start].trim_end();
        let after = text[at..].trim_start();
        let qualified =
            before.ends_with("::") || (before.ends_with('.') && !before.ends_with(".."));
        if qualified || after.starts_with("::") || (name == "r" && after.starts_with('#')) {
            continue;
        }
        out.push((name, after.starts_with('(')));
    }
    out
}

/// Every function or closure carrying a `trust-wp:` marker whose parameter
/// bindings (nested pattern bindings among them) share a spelling. Rust
/// allows it only apart by hygiene (`$x` beside a macro's own `x`), and the
/// verifier names a parameter, and a pattern binding's projection
/// (`param_patterns::param_pattern_bindings`), by spelling.
fn duplicate_parameter_spellings(tcx: TyCtxt<'_>) -> Vec<(Span, String)> {
    let mut found = Vec::new();
    for local in tcx.iter_local_def_id() {
        if !matches!(
            tcx.def_kind(local),
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure
        ) || crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local)
        {
            continue;
        }
        let specified = tcx
            .hir_attrs(tcx.local_def_id_to_hir_id(local))
            .iter()
            .filter_map(crate::attr_utils::doc_marker_str)
            .any(|value| value.as_str().starts_with("trust-wp:"));
        if !specified {
            continue;
        }
        let mut names: Vec<String> = Vec::new();
        if let Some(body) = tcx.hir_maybe_body_owned_by(local) {
            for param in body.params {
                param.pat.each_binding(|_, _, _, ident| {
                    names.push(ident.name.to_string());
                });
            }
        } else if tcx.def_kind(local) != DefKind::Closure {
            names.extend(
                tcx.fn_arg_idents(local.to_def_id())
                    .iter()
                    .flatten()
                    .map(|ident| ident.name.to_string()),
            );
        }
        let mut seen = HashSet::new();
        if let Some(name) = names.iter().find(|name| !seen.insert(name.as_str())) {
            found.push((
                tcx.def_span(local),
                format!(
                    "two parameter bindings of `{}` spelled `{name}`, apart only by hygiene, \
                     while a specification names a parameter by its spelling",
                    tcx.def_path_str(local.to_def_id())
                ),
            ));
        }
    }
    found
}

struct SpecCallVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    found: &'a mut Vec<(Span, String)>,
    /// Where the vehicle wrote its `inv` helper for a specification's
    /// `inv(..)`, first seen.
    inv_helper: &'a mut Option<Span>,
}

impl<'tcx> Visitor<'tcx> for SpecCallVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, args) = expr.kind {
            if let Some(spelling) = path_spelling(callee) {
                if is_vehicle_path(callee) {
                    if spelling == "inv" && args.len() == 1 {
                        self.inv_helper.get_or_insert(expr.span);
                    }
                } else {
                    let named = match self
                        .typeck
                        .node_type_opt(callee.hir_id)
                        .map(|ty| *ty.kind())
                    {
                        Some(TyKind::FnDef(def_id, _)) => {
                            Some(DefinitionFacts::of(self.tcx, def_id))
                        }
                        _ => None,
                    };
                    if let Some(why) = misread_spec_call(
                        &spelling,
                        args.len(),
                        is_bare_path(callee),
                        named.as_ref(),
                    ) {
                        self.found.push((expr.span, why));
                    }
                }
            }
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

/// Why a specification's path call spelled `spelling` with `arity` arguments
/// is read as something other than `named`, the definition rustc names by
/// the callee's fn-item type (`None` for any other callee), if it is.
fn misread_spec_call(
    spelling: &str,
    arity: usize,
    bare: bool,
    named: Option<&DefinitionFacts>,
) -> Option<String> {
    let resolved = || {
        named.map_or_else(
            || "no fn item".to_string(),
            |facts| format!("`{}`", facts.path),
        )
    };
    if bare && BUILTIN_CALL_SPELLINGS.contains(&(spelling, arity)) {
        let builtin = named.is_some_and(|facts| {
            facts.std
                && facts.kind == DefinitionKind::FreeFn
                && facts.name.as_deref() == Some(spelling)
        });
        return (!builtin).then(|| {
            format!(
                "a call `{spelling}(..)` in a specification that rustc resolves to {}, which the \
                 contract parser reads as the `{spelling}` builtin",
                resolved()
            )
        });
    }
    let facts = named?;
    let names_itself = facts.name.as_deref() == Some(spelling)
        || (facts.kind == DefinitionKind::Ctor && spelling == "Self");
    (!names_itself).then(|| {
        format!(
            "a call spelled `{spelling}` in a specification that rustc resolves to {}: the \
             contract parser and the encoder read a specification's call by its spelling",
            resolved()
        )
    })
}

/// What a parsed call is counted under against the type-checked calls: the
/// definition an identity-pass id names, or else the call's spelling.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CallKey {
    Resolved(DefId),
    Spelled(String),
}

/// The first call of `body` with no counterpart among `calls`, or why the
/// body could not be searched. Calls are counted: the parsed body may hold no
/// more calls spelled one way (or named by one identity-pass id) than the
/// type-checked form holds calls so spelled (or resolved to that
/// definition). The walk reads a parsed call as denoting what rustc resolved
/// the calls of its spelling to, which is sound only when every parsed call
/// IS one of them: a call inside a subterm the vehicle does not type-check
/// has no resolution of its own, and a same-spelled call elsewhere can
/// denote another definition (a block-scoped `use ... as`,
/// logic_fn_callee_precondition_dropped_subterm_shared_spelling.rs).
/// `complete` is false when the vehicle dropped a subterm (`drops_a_subterm`):
/// a call of a macro's name then has no counterpart (one is expanded), and
/// neither has a call spelled like a helper the vehicle writes for an
/// operator elsewhere (`use crate::f as lt_log;`), so its helpers count for
/// nothing.
fn unmatched_call(body: &PureExpr, calls: &[TypedCall], complete: bool) -> Option<String> {
    let mut typed: HashMap<CallKey, usize> = HashMap::new();
    for call in calls.iter().filter(|call| complete || !call.synthesized) {
        if let Some(spelling) = &call.spelling {
            *typed.entry(CallKey::Spelled(spelling.clone())).or_default() += 1;
        }
        let resolved: HashSet<DefId> = call.callees.iter().copied().collect();
        for def_id in resolved {
            *typed.entry(CallKey::Resolved(def_id)).or_default() += 1;
        }
    }
    let mut parsed: Vec<(CallKey, String)> = Vec::new();
    let mut unresolved_id = None;
    let beyond_reach =
        without_triggers(body).any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
            let name = match node {
                PureExpr::LogicFnCall { name, .. } => name,
                PureExpr::MethodCall { method, .. } => method,
                _ => return false,
            };
            if is_reserved_call_name(name)
                || (complete
                    && matches!(node, PureExpr::LogicFnCall { .. })
                    && MACRO_CALL_NAMES.contains(&name.as_str()))
            {
                return false;
            }
            let key = if name.starts_with(LOGIC_FN_ID_PREFIX) {
                let Some(def_id) = crate::logic::identity::member_def_id(name) else {
                    unresolved_id = Some(name.clone());
                    return true;
                };
                CallKey::Resolved(def_id)
            } else {
                CallKey::Spelled(call_spelling(name).to_string())
            };
            parsed.push((key, name.clone()));
            false
        });
    if let Some(name) = unresolved_id {
        return Some(format!(
            "a call `{name}` that the body's type-checked form does not hold, so what it \
             denotes is unknown"
        ));
    }
    if beyond_reach {
        return Some("a call nested deeper than the body search reaches".to_string());
    }
    let mut counted: HashMap<&CallKey, usize> = HashMap::new();
    for (key, _) in &parsed {
        *counted.entry(key).or_default() += 1;
    }
    parsed.iter().find_map(|(key, name)| {
        let written = counted[key];
        match typed.get(key).copied().unwrap_or(0) {
            0 => Some(format!(
                "a call `{name}` that the body's type-checked form does not hold, so what it \
                 denotes is unknown"
            )),
            held if held < written => Some(format!(
                "{written} calls like `{name}` in the parsed body and {held} in its \
                 type-checked form: a call rustc did not resolve denotes what is unknown, \
                 whatever another call so spelled denotes"
            )),
            _ => None,
        }
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use rustc_hir::def_id::DefIndex;

    use super::*;

    fn local(index: u32) -> DefId {
        DefId {
            krate: LOCAL_CRATE,
            index: DefIndex::from_u32(index),
        }
    }

    fn typed(spelling: &str) -> TypedCall {
        TypedCall {
            spelling: Some(spelling.to_string()),
            callees: vec![local(1)],
            synthesized: false,
            path_arity: None,
            bare: false,
            fn_item: false,
        }
    }

    /// A bare path call `spelling(y)` whose fn item is `callee`.
    fn path_call(spelling: &str, callee: DefId) -> TypedCall {
        TypedCall {
            spelling: Some(spelling.to_string()),
            callees: vec![callee],
            synthesized: false,
            path_arity: Some(1),
            bare: true,
            fn_item: true,
        }
    }

    fn body_of(calls: Vec<TypedCall>) -> TypedBody {
        TypedBody {
            calls,
            locals: HashSet::new(),
            dropped_subterm: false,
        }
    }

    fn facts(local: bool, kind: DefinitionKind, name: &str, std: bool) -> DefinitionFacts {
        DefinitionFacts {
            local,
            kind,
            name: Some(name.to_string()),
            std,
            path: name.to_string(),
        }
    }

    /// `local(1)` is the lane's `pair`, `local(2)` a local program function
    /// `prog`, `local(3)` a local constructor `S`, `local(4)` the standard
    /// library's `view`, `local(5)` the standard library's `Some`, `local(6)`
    /// the standard library's `such_that`. (Locality is the facts', not the
    /// index's.)
    fn describe(def_id: DefId) -> DefinitionFacts {
        match def_id.index.as_u32() {
            1 => facts(true, DefinitionKind::FreeFn, "pair", false),
            2 => facts(true, DefinitionKind::FreeFn, "prog", false),
            3 => facts(true, DefinitionKind::Ctor, "S", false),
            4 => facts(false, DefinitionKind::FreeFn, "view", true),
            5 => facts(false, DefinitionKind::Ctor, "Some", false),
            _ => facts(false, DefinitionKind::FreeFn, "such_that", true),
        }
    }

    fn lane() -> HashMap<DefId, (String, usize)> {
        [(local(1), ("__lfid__pair".to_string(), 1))].into()
    }

    fn settle(body: &PureExpr, typed: &TypedBody, rebound: &ReboundNames) -> Settled {
        settle_typed_body(body, typed, &lane(), rebound, &describe)
    }

    fn rebinding(name: &str) -> ReboundNames {
        ReboundNames {
            by_name: [(name.to_string(), "an import".to_string())].into(),
            unknown_glob: None,
        }
    }

    /// The parser reads exactly these spellings as builtins: a fix that pins
    /// a spelling the parser keeps as a call, or misses one it does not,
    /// fails here.
    #[test]
    fn the_builtin_call_spellings_are_the_parsers() {
        for &(spelling, _) in BUILTIN_CALL_SPELLINGS {
            let parsed = trust_wp_core::contract_parser::parse_contract(&format!("{spelling}(y)"));
            assert!(
                !matches!(parsed, Ok(PureExpr::LogicFnCall { .. })),
                "{spelling}: {parsed:?}"
            );
        }
        for spelling in ["viewx", "inv", "seq", "Some", "resolve"] {
            let parsed = trust_wp_core::contract_parser::parse_contract(&format!("{spelling}(y)"));
            assert!(
                matches!(parsed, Ok(PureExpr::LogicFnCall { .. })),
                "{spelling}: {parsed:?}"
            );
        }
    }

    /// D-240: the names a specification text spells bare, and which it calls.
    #[test]
    fn bare_names_are_the_unqualified_names_of_a_text() {
        assert_eq!(
            bare_names("0 <= view (x) < 6 && x.view() == E::B && 5u32 == B"),
            vec![("view", true), ("x", false), ("x", false), ("B", false)]
        );
        assert_eq!(
            bare_names("match result { B(_) => false, _ => true }"),
            vec![
                ("match", false),
                ("result", false),
                ("B", true),
                ("_", false),
                ("false", false),
                ("_", false),
                ("true", false)
            ]
        );
        assert_eq!(bare_names("0..view(x)"), vec![("view", true), ("x", false)]);
        assert_eq!(bare_names("seq![5].len()"), vec![("seq", false)]);
    }

    /// logic_fn_body_seq_call_renamed.rs: `seq(y)` under
    /// `use crate::pair as seq;` is named by `pair`'s id.
    #[test]
    fn a_renamed_call_is_named_by_the_lane_function_rustc_resolves() {
        let settled = settle(
            &call("seq"),
            &body_of(vec![path_call("seq", local(1))]),
            &ReboundNames::default(),
        );
        assert_eq!(settled, Settled::Rewritten(call("__lfid__pair")));
        // A qualified spelling of the same call too.
        let settled = settle(
            &call("m::np"),
            &body_of(vec![path_call("np", local(1))]),
            &ReboundNames::default(),
        );
        assert_eq!(settled, Settled::Rewritten(call("__lfid__pair")));
    }

    /// logic_fn_body_view_call_renamed.rs and logic_fn_body_view_call_local_fn.rs:
    /// a bare `view(y)` is the builtin only when rustc resolves it to the
    /// standard `view`.
    #[test]
    fn a_view_call_rustc_resolves_elsewhere_is_misread() {
        let none = ReboundNames::default();
        let view = PureExpr::View(Arc::new(PureExpr::Var("y".to_string(), None)));
        for callee in [local(1), local(2)] {
            assert!(matches!(
                settle(&view, &body_of(vec![path_call("view", callee)]), &none),
                Settled::Misread(_)
            ));
        }
        assert_eq!(
            settle(&view, &body_of(vec![path_call("view", local(4))]), &none),
            Settled::Kept
        );
        // `m::view(y)` is a call the parser keeps as one.
        let qualified = TypedCall {
            bare: false,
            ..path_call("view", local(1))
        };
        assert_eq!(
            settle(&call("m::view"), &body_of(vec![qualified]), &none),
            Settled::Rewritten(call("__lfid__pair"))
        );
    }

    /// A call named `seq` beside the `seq!` macro, which the parser writes as
    /// a call of the same name, cannot be told from it.
    #[test]
    fn a_call_named_like_a_macro_beside_the_macro_is_misread() {
        let both = PureExpr::BinOp(
            Arc::new(call("seq")),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(call("seq")),
        );
        assert!(matches!(
            settle(
                &both,
                &body_of(vec![path_call("seq", local(1))]),
                &ReboundNames::default()
            ),
            Settled::Misread(_)
        ));
    }

    /// logic_fn_callee_precondition_alias_onto_inv.rs: the vehicle writes
    /// `inv(y)` as its own helper, so a name the crate or the body binds to
    /// something else is read as that something else.
    #[test]
    fn a_vehicle_helper_call_with_a_rebound_name_is_misread() {
        let helper = TypedCall {
            synthesized: true,
            ..path_call("inv", local(6))
        };
        let body = body_of(vec![helper.clone()]);
        assert!(matches!(
            settle(&call("inv"), &body, &rebinding("inv")),
            Settled::Misread(_)
        ));
        assert_eq!(
            settle(&call("inv"), &body, &ReboundNames::default()),
            Settled::Kept
        );
        let bound_locally = TypedBody {
            calls: vec![helper],
            locals: ["inv".to_string()].into(),
            dropped_subterm: false,
        };
        assert!(matches!(
            settle(&call("inv"), &bound_locally, &ReboundNames::default()),
            Settled::Misread(_)
        ));
    }

    /// A spelling that names the definition rustc resolved it to is read as
    /// before; one that does not, or that denotes a function the lane never
    /// reads, is misread.
    #[test]
    fn a_spelling_is_kept_only_where_it_names_its_definition() {
        let none = ReboundNames::default();
        for (spelling, callee) in [("Some", local(5)), ("S", local(3)), ("Self", local(3))] {
            assert_eq!(
                settle(
                    &call(spelling),
                    &body_of(vec![path_call(spelling, callee)]),
                    &none
                ),
                Settled::Kept,
                "{spelling}"
            );
        }
        for (spelling, callee) in [("st", local(6)), ("Some", local(3)), ("prog", local(2))] {
            assert!(
                matches!(
                    settle(
                        &call(spelling),
                        &body_of(vec![path_call(spelling, callee)]),
                        &none
                    ),
                    Settled::Misread(_)
                ),
                "{spelling}"
            );
        }
        // Two calls of one spelling that denote two definitions.
        let two = PureExpr::BinOp(
            Arc::new(call("np")),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(call("np")),
        );
        assert!(matches!(
            settle(
                &two,
                &body_of(vec![path_call("np", local(1)), path_call("np", local(2))]),
                &none
            ),
            Settled::Misread(_)
        ));
    }

    /// A call rustc did not resolve is read by its spelling only where
    /// nothing binds that name otherwise; a `seq!` literal is the macro
    /// whatever a value named `seq` is, unless a subterm was dropped.
    #[test]
    fn an_unresolved_call_with_a_rebound_name_is_misread() {
        assert!(matches!(
            settle(&call("np"), &body_of(Vec::new()), &rebinding("np")),
            Settled::Misread(_)
        ));
        assert_eq!(
            settle(&call("np"), &body_of(Vec::new()), &ReboundNames::default()),
            Settled::Kept
        );
        assert_eq!(
            settle(&call("seq"), &body_of(Vec::new()), &rebinding("seq")),
            Settled::Kept
        );
        let dropped = TypedBody {
            dropped_subterm: true,
            ..body_of(Vec::new())
        };
        assert!(matches!(
            settle(&call("seq"), &dropped, &rebinding("seq")),
            Settled::Misread(_)
        ));
    }

    /// With no type-checked form, a spelled call, a view or a final value is
    /// misread where the crate or the body binds its name.
    #[test]
    fn an_untyped_body_is_misread_where_a_spelling_is_rebound() {
        let none = ReboundNames::default();
        assert_eq!(untyped_misread(&call("np"), &[], &none), None);
        assert!(untyped_misread(&call("np"), &[], &rebinding("np")).is_some());
        assert!(untyped_misread(&call("np"), &["np".to_string()], &none).is_some());
        let view = PureExpr::View(Arc::new(PureExpr::Var("y".to_string(), None)));
        assert!(untyped_misread(&view, &[], &rebinding("view")).is_some());
        assert_eq!(untyped_misread(&view, &[], &rebinding("np")), None);
        let unknown = ReboundNames {
            by_name: HashMap::new(),
            unknown_glob: Some("a glob import".to_string()),
        };
        assert!(untyped_misread(&call("np"), &[], &unknown).is_some());
        // A call the identity pass named: nothing confirms the definition.
        assert!(untyped_misread(&call("__lfid__k"), &[], &none).is_some());
    }

    /// logic_fn_body_block_local_name_shadowing_read_by_caller.rs: the
    /// identity pass named the call by the root's `k`, rustc resolved it to
    /// the block's, so the settled body has a call with no counterpart and is
    /// misread, hidden from the callers that would unfold it.
    #[test]
    fn a_settled_body_with_an_unmatched_call_is_misread() {
        let none = ReboundNames::default();
        let settle_matched = |body: &PureExpr, typed: &TypedBody| {
            settle_and_match(body, typed, &lane(), &none, &describe)
        };
        assert!(matches!(
            settle_matched(&call("__lfid__k"), &body_of(vec![path_call("k", local(2))])),
            Settled::Misread(_)
        ));
        // A call rustc resolved to what its spelling names is matched.
        assert_eq!(
            settle_matched(&call("Some"), &body_of(vec![path_call("Some", local(5))])),
            Settled::Kept
        );
        // A call in a subterm the vehicle dropped has no counterpart.
        let dropped = TypedBody {
            dropped_subterm: true,
            ..body_of(Vec::new())
        };
        assert!(matches!(
            settle_matched(&call("np"), &dropped),
            Settled::Misread(_)
        ));
    }

    /// program_ensures_view_call_renamed.rs and its siblings: a
    /// specification's call is read by its spelling, so one rustc resolves to
    /// a definition the spelling does not name is misread.
    #[test]
    fn a_specification_call_is_misread_where_its_spelling_names_another_definition() {
        let pair = facts(true, DefinitionKind::FreeFn, "pair", false);
        let std_view = facts(false, DefinitionKind::FreeFn, "view", true);
        let local_view = facts(true, DefinitionKind::FreeFn, "view", false);
        let some = facts(false, DefinitionKind::Ctor, "Some", false);
        let tuple_struct = facts(true, DefinitionKind::Ctor, "S", false);
        // The parser's builtins, bare: only the standard function so named.
        assert_eq!(misread_spec_call("view", 1, true, Some(&std_view)), None);
        assert!(misread_spec_call("view", 1, true, Some(&pair)).is_some());
        assert!(misread_spec_call("view", 1, true, Some(&local_view)).is_some());
        assert!(misread_spec_call("view", 1, true, None).is_some());
        assert!(misread_spec_call("final_value", 1, true, Some(&pair)).is_some());
        // Qualified, the call is kept as one and named by its spelling.
        assert_eq!(misread_spec_call("view", 1, false, Some(&local_view)), None);
        // A rename, onto a builtin's name or any other, and a bound fn item.
        assert!(misread_spec_call("seq", 1, true, Some(&pair)).is_some());
        assert!(misread_spec_call("Some", 1, true, Some(&pair)).is_some());
        assert!(misread_spec_call("g", 1, true, Some(&pair)).is_some());
        // A definition called by its own name, or a constructor by `Self`.
        assert_eq!(misread_spec_call("pair", 1, true, Some(&pair)), None);
        assert_eq!(misread_spec_call("Some", 1, true, Some(&some)), None);
        assert_eq!(
            misread_spec_call("Self", 1, true, Some(&tuple_struct)),
            None
        );
        // A callee rustc names by no fn item is not read by a definition.
        assert_eq!(misread_spec_call("np", 1, true, None), None);
    }

    fn call(name: &str) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args: vec![PureExpr::Var("y".to_string(), None)],
        }
    }

    /// logic_fn_callee_precondition_use_alias.rs: `np(y)` has its
    /// counterpart in the type-checked body whatever it is spelled, and a
    /// call the type-checked body does not hold is unmatched.
    #[test]
    fn a_parsed_call_is_matched_by_its_spelling() {
        let calls = [typed("np")];
        for name in ["np", "m::np", "self::np", "<T as Tr>::np"] {
            assert_eq!(unmatched_call(&call(name), &calls, true), None, "{name}");
        }
        assert!(unmatched_call(&call("other"), &calls, true).is_some());
        let method = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: "get".to_string(),
            args: Vec::new(),
        };
        assert!(unmatched_call(&method, &calls, true).is_some());
        assert_eq!(unmatched_call(&method, &[typed("get")], true), None);
    }

    /// The parser's own names need no counterpart; a macro's name needs none
    /// only when nothing the macro could sit in was dropped.
    #[test]
    fn synthesised_and_macro_names_are_matched_only_as_such() {
        assert_eq!(
            unmatched_call(&call("__trust_wp_tuple_get_0"), &[], false),
            None
        );
        assert_eq!(unmatched_call(&call("proof_assert"), &[], true), None);
        assert!(unmatched_call(&call("proof_assert"), &[], false).is_some());
        // An identity-pass id whose definition rustc resolves no call to.
        assert!(unmatched_call(&call("__lfid__needs_pos"), &[typed("np")], true).is_some());
    }

    /// logic_fn_callee_precondition_dropped_subterm_shared_spelling.rs: a
    /// second `np` the type-checked form does not hold is not answered by
    /// the one it does.
    #[test]
    fn a_parsed_call_needs_a_counterpart_of_its_own() {
        let two = PureExpr::BinOp(
            Arc::new(call("np")),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(call("m::np")),
        );
        assert!(unmatched_call(&two, &[typed("np")], true).is_some());
        assert_eq!(
            unmatched_call(&two, &[typed("np"), typed("np")], true),
            None
        );
    }

    /// A trigger is never evaluated: its calls need no counterpart and do
    /// not count against the body's.
    #[test]
    fn a_trigger_call_needs_no_counterpart() {
        let quantified = |body: PureExpr| PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![vec![call("np")]],
        };
        assert_eq!(
            unmatched_call(&quantified(PureExpr::Bool(true)), &[], true),
            None
        );
        assert_eq!(
            unmatched_call(&quantified(call("np")), &[typed("np")], true),
            None
        );
        assert!(unmatched_call(&quantified(call("np")), &[], true).is_some());
    }

    /// A helper the vehicle wrote answers a parsed call of its spelling
    /// (`inv(x)`) only where no subterm was dropped.
    #[test]
    fn a_vehicle_helper_answers_a_call_only_in_a_complete_form() {
        let helper = TypedCall {
            synthesized: true,
            ..typed("lt_log")
        };
        assert_eq!(
            unmatched_call(&call("lt_log"), &[helper.clone()], true),
            None
        );
        assert!(unmatched_call(&call("lt_log"), &[helper.clone()], false).is_some());
        assert_eq!(
            unmatched_call(&call("lt_log"), &[helper, typed("lt_log")], false),
            None
        );
    }

    #[test]
    fn a_call_is_spelled_by_its_last_segment_without_turbofish() {
        for (name, spelling) in [
            ("f", "f"),
            ("crate::m::f", "f"),
            ("Self::f", "f"),
            ("<T as m::Tr>::f", "f"),
            ("f::<T>", "f"),
            ("S::<T>::f::<U>", "f"),
        ] {
            assert_eq!(call_spelling(name), spelling, "{name}");
        }
    }

    fn inlined(name: &str, _arity: usize) -> bool {
        name.starts_with("H::")
    }

    /// logic_fn_callee_precondition_view_beside_inlined_view.rs and the
    /// inlined-argument cases: an inlined call is not kept, a call beside it
    /// is, and an inlined call whose argument calls something is named.
    #[test]
    fn inlined_calls_are_not_kept_and_a_calling_argument_is_named() {
        let pick = |arg: PureExpr| PureExpr::LogicFnCall {
            name: "H::pick".to_string(),
            args: vec![PureExpr::Bool(false), arg],
        };
        let beside = PureExpr::BinOp(
            Arc::new(call("needs_pos")),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(pick(PureExpr::Var("y".to_string(), None))),
        );
        let parsed = ParsedCalls::of(&beside, &inlined);
        assert_eq!(parsed.kept, vec!["needs_pos".to_string()]);
        assert_eq!(parsed.inlined_calling_argument, None);
        assert_eq!(parsed.first.as_deref(), Some("needs_pos"));
        let parsed = ParsedCalls::of(&pick(call("needs_pos")), &inlined);
        assert_eq!(parsed.kept, vec!["needs_pos".to_string()]);
        assert_eq!(parsed.inlined_calling_argument.as_deref(), Some("H::pick"));
        assert_eq!(parsed.first.as_deref(), Some("H::pick"));
        // A synthesised projection in an argument is no call.
        let projected = pick(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("p".to_string(), None)],
        });
        assert_eq!(
            ParsedCalls::of(&projected, &inlined).inlined_calling_argument,
            None
        );
    }

    /// A path two functions print as is recorded with either body's calls.
    #[test]
    fn a_union_keeps_either_bodys_calls() {
        let one = ParsedCalls::of(&PureExpr::Int(0), &inlined);
        let other = ParsedCalls::of(&call("np"), &inlined);
        assert_eq!(one.union(other).first.as_deref(), Some("np"));
    }
}
