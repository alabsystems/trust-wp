// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The names a parameter PATTERN binds, as projections of the parameter (D-177).
//!
//! A parameter written as a destructuring pattern — `(p, _q): (Int, Int)`,
//! `P { x, y: _ }: P`, `whole @ (p, _)` — is registered under one name for
//! the whole value (`name_unnamed_params` gives it its positional name,
//! `__twp_arg{idx}`; an at-binding keeps its own name), while the
//! definition's body and its clauses still say `p`. Every lane substitutes
//! PARAMETERS only, so `p` was left free and read in the scope of whoever
//! instantiated the text: an unfolded open body or a callee `ensures` said the
//! CALLER's `p`.
//!
//! The rule this module carries out: a definition or a clause that mentions a
//! name its own pattern parameters bind is rewritten so that name is the
//! projection of the parameter Creusot destructures it from (`p` is
//! `__twp_arg1.0`), or it is refused. It is never instantiated with the name
//! free. The projection is spelled as contract text and parsed by the contract
//! parser, so it is the term a tuple parameter's `t.0` is: a binding that
//! holds a `&mut` is read exactly as that field of a tuple parameter is, and
//! refused where that lane places no read (D-179).
//!
//! The positional name is one no source identifier can spell, so the
//! projection's base is never a module item or a capture. A clause that reads
//! a name a CALL binds to an argument by position (`arg0`, `value`, ...)
//! without the function having a parameter of that name is refused
//! ([`refuse_positional_alias_collisions`]).

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_wp_core::{
    contract_parser::parse_contract,
    formula::{
        internal::tuple_lowering::{tuple_field_logic_fn_index, NAMED_FIELD_LOGIC_FN_PREFIX},
        CaptureAvoidingSubstOptions, PureExpr,
    },
};

/// The method the contract parser lowers `e[i]` to (`e.index_logic(i)`).
const INDEX_LOGIC_METHOD: &str = "index_logic";

/// What a function's parameter patterns bind.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ParamPatternBindings {
    /// Binding name -> contract text of the parameter projection it denotes.
    pub(crate) projections: Vec<(String, String)>,
    /// Binding name -> why it has no projection. A text that mentions one of
    /// these is refused.
    pub(crate) unprojectable: Vec<(String, String)>,
    /// The projected bindings whose type holds a `&mut`, projected from a
    /// parameter that holds it without being it. A postcondition reads such a
    /// `&mut` only through `*`, `^` or `@`, each of which the state rule
    /// refuses (D-101); any other read of one in a postcondition, and its
    /// prophecy `^` in any other clause, is refused here (D-179).
    pub(crate) held_mut: Vec<String>,
}

impl ParamPatternBindings {
    pub(crate) fn is_empty(&self) -> bool {
        self.projections.is_empty() && self.unprojectable.is_empty()
    }

    fn names(&self) -> impl Iterator<Item = &str> {
        self.projections
            .iter()
            .chain(self.unprojectable.iter())
            .map(|(name, _)| name.as_str())
    }

    /// The projections as parsed terms. A projection whose text does not parse
    /// (a fallback name outside the identifier grammar) is an `Err`.
    fn projection_terms(&self) -> Result<HashMap<String, PureExpr>, String> {
        self.projections
            .iter()
            .map(|(name, text)| {
                parse_contract(text)
                    .map(|term| (name.clone(), term))
                    .map_err(|e| {
                        format!("the projection `{text}` of pattern binding `{name}` does not parse: {e}")
                    })
            })
            .collect()
    }
}

/// `def_id`'s HIR body with the name every resolver registers for each of its
/// parameters (`name_unnamed_params`: a destructured one is its positional
/// name, `__twp_arg{idx}`).
fn hir_params_and_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<(&'tcx rustc_hir::Body<'tcx>, Vec<String>)> {
    let body_id = tcx.hir_node_by_def_id(def_id).body_id()?;
    let body = tcx.hir_body(body_id);
    let raw: Vec<Option<String>> = body
        .params
        .iter()
        .map(|param| match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, ident, _) => Some(ident.as_str().to_string()),
            _ => None,
        })
        .collect();
    Some((body, crate::mir_analysis::name_unnamed_params(raw)))
}

/// The pattern bindings of `def_id`'s parameters, over the parameter names
/// every name resolver registers for them (`name_unnamed_params` over the HIR
/// parameters, so `__twp_arg{idx}` for a destructured one).
///
/// Only a parameter written as something other than a plain by-value binding
/// contributes. A binding gets a projection when every pattern above it is a
/// tuple, a struct or a tuple struct matched by value (no implicit dereference,
/// no enum variant) and it binds by value. A binding whose type holds a `&mut`
/// is projected only from a parameter the state rule reads as holding one
/// (a tuple or an array: `is_held_mutable_parameter_type`), where the reads
/// through it are placed or refused as a tuple parameter's field is; from a
/// struct parameter, whose `&mut` fields the rule does not classify, it is
/// not. A binding holding a shared reference to a value with interior
/// mutability is not projected either: its referent changes under a shared
/// reference, and no lane places its reads. Anything else is recorded as
/// unprojectable with the reason.
pub(crate) fn param_pattern_bindings(tcx: TyCtxt<'_>, def_id: LocalDefId) -> ParamPatternBindings {
    let mut out = ParamPatternBindings::default();
    let Some((body, names)) = hir_params_and_names(tcx, def_id) else {
        return out;
    };
    if body
        .params
        .iter()
        .all(|param| matches!(param.pat.kind, rustc_hir::PatKind::Binding(_, _, _, None)))
    {
        return out;
    }
    let typeck = tcx.typeck(def_id);
    let reserved: HashSet<&str> = names.iter().map(String::as_str).collect();
    let typing_env = ty::TypingEnv::post_analysis(tcx, def_id.to_def_id());
    for (param, name) in body.params.iter().zip(&names) {
        let walker = Walker {
            tcx,
            typeck,
            typing_env,
            reserved: &reserved,
            root_holds_placed_mut: crate::mir_analysis::is_held_mutable_parameter_type(
                tcx,
                typing_env,
                typeck.pat_ty(param.pat),
            ),
        };
        match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, _, None) => {}
            // The parameter keeps the at-binding's own name; the sub-pattern
            // is destructured from it.
            rustc_hir::PatKind::Binding(_, _, _, Some(sub)) => {
                walk(&walker, sub, name, &mut out);
            }
            _ => walk(&walker, param.pat, name, &mut out),
        }
    }
    out
}

/// What one parameter's pattern is destructured against.
struct Walker<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    /// Every parameter's registered name: a binding spelled like one would be
    /// read as that parameter.
    reserved: &'a HashSet<&'a str>,
    /// Whether the parameter is one the state rule reads as holding a `&mut`
    /// without being it (a tuple or an array holding one).
    root_holds_placed_mut: bool,
}

/// What a value of a binding's type can reach, through its generic arguments
/// and its fields: a `&mut`, and a shared reference to a value with interior
/// mutability. Both are `true` past the depth bound, which is where the walk
/// stops seeing.
#[derive(Default)]
struct Reaches {
    mutable_reference: bool,
    interior_mutable_reference: bool,
}

const REACHES_DEPTH_BOUND: usize = 6;

fn reaches<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    root: ty::Ty<'tcx>,
) -> Reaches {
    fn visit<'tcx>(
        tcx: TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        ty: ty::Ty<'tcx>,
        depth: usize,
        seen: &mut HashSet<ty::Ty<'tcx>>,
        out: &mut Reaches,
    ) {
        if out.mutable_reference && out.interior_mutable_reference {
            return;
        }
        if depth > REACHES_DEPTH_BOUND {
            out.mutable_reference = true;
            out.interior_mutable_reference = true;
            return;
        }
        if !seen.insert(ty) {
            return;
        }
        for arg in ty.walk() {
            let Some(inner) = arg.as_type() else {
                continue;
            };
            match inner.kind() {
                ty::Ref(_, _, ty::Mutability::Mut) => out.mutable_reference = true,
                // A reference under a binder (in a `fn` pointer's signature)
                // is no value this one holds; `is_freeze` cannot be asked of it.
                ty::Ref(_, referent, ty::Mutability::Not)
                    if !referent.has_escaping_bound_vars()
                        && !referent.is_freeze(tcx, typing_env) =>
                {
                    out.interior_mutable_reference = true;
                }
                ty::Adt(adt, args) => {
                    for field in adt.all_fields() {
                        visit(
                            tcx,
                            typing_env,
                            field.ty(tcx, *args).skip_norm_wip(),
                            depth + 1,
                            seen,
                            out,
                        );
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = Reaches::default();
    visit(tcx, typing_env, root, 0, &mut HashSet::new(), &mut out);
    out
}

/// Whether a value of type `ty` can reach a `&mut`, through its generic
/// arguments and its fields (`true` past the depth bound): the one walk that
/// decides both which pattern bindings hold a `&mut` and which parameters
/// the state rule reads as holding one (`is_held_mutable_parameter_type`).
pub(crate) fn reaches_a_mutable_reference<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: ty::Ty<'tcx>,
) -> bool {
    reaches(tcx, typing_env, ty).mutable_reference
}

fn walk<'tcx>(
    walker: &Walker<'_, 'tcx>,
    pat: &'tcx rustc_hir::Pat<'tcx>,
    base: &str,
    out: &mut ParamPatternBindings,
) {
    use rustc_hir::PatKind;
    let typeck = walker.typeck;
    let refuse_all = |out: &mut ParamPatternBindings, why: &str| {
        pat.each_binding(|_, _, _, ident| {
            out.unprojectable
                .push((ident.as_str().to_string(), why.to_string()));
        });
    };
    // A pattern matched through a reference that it does not spell (match
    // ergonomics) binds by reference: `p` is then `&arg.0`, not `arg.0`.
    if typeck
        .pat_adjustments()
        .get(pat.hir_id)
        .is_some_and(|adjustments| !adjustments.is_empty())
    {
        refuse_all(out, "the pattern is matched through a reference");
        return;
    }
    match pat.kind {
        PatKind::Wild | PatKind::Missing => {}
        PatKind::Binding(_, hir_id, ident, sub) => {
            let name = ident.as_str().to_string();
            let by_value = typeck
                .pat_binding_modes()
                .get(hir_id)
                .is_some_and(|mode| matches!(mode.0, rustc_hir::ByRef::No));
            let Reaches {
                mutable_reference: holds_mut,
                interior_mutable_reference: holds_interior_mutable_ref,
            } = reaches(walker.tcx, walker.typing_env, typeck.node_type(hir_id));
            let clashes = walker.reserved.contains(name.as_str())
                || matches!(name.as_str(), "self" | "result")
                || name.starts_with("__trust_wp")
                || name.starts_with("__twp");
            if !by_value {
                out.unprojectable
                    .push((name, "it binds by reference".to_string()));
            } else if holds_mut && !walker.root_holds_placed_mut {
                out.unprojectable.push((
                    name,
                    "its type holds a `&mut`, and the parameter it is projected from is not \
                     one whose held `&mut` the state rule reads (a tuple or an array)"
                        .to_string(),
                ));
            } else if holds_interior_mutable_ref {
                out.unprojectable.push((
                    name,
                    "its type holds a shared reference to a value with interior mutability"
                        .to_string(),
                ));
            } else if clashes {
                out.unprojectable.push((
                    name,
                    "its name is also a parameter's, or reserved".to_string(),
                ));
            } else {
                if holds_mut {
                    out.held_mut.push(name.clone());
                }
                out.projections.push((name, base.to_string()));
            }
            if let Some(sub) = sub {
                walk(walker, sub, base, out);
            }
        }
        PatKind::Tuple(elems, dotdot) => {
            let ty::TyKind::Tuple(tys) = typeck.pat_ty(pat).kind() else {
                refuse_all(out, "the tuple pattern's type is not a tuple");
                return;
            };
            for (index, elem) in positional_indices(elems.len(), dotdot, tys.len()) {
                walk(walker, &elems[elem], &format!("{base}.{index}"), out);
            }
        }
        PatKind::TupleStruct(_, elems, dotdot) => {
            let ty::TyKind::Adt(adt, _) = typeck.pat_ty(pat).kind() else {
                refuse_all(out, "the tuple-struct pattern's type is not a struct");
                return;
            };
            if !adt.is_struct() {
                refuse_all(out, "the pattern names an enum variant or a union");
                return;
            }
            let arity = adt.non_enum_variant().fields.len();
            for (index, elem) in positional_indices(elems.len(), dotdot, arity) {
                walk(walker, &elems[elem], &format!("{base}.{index}"), out);
            }
        }
        PatKind::Struct(_, fields, _) => {
            let ty::TyKind::Adt(adt, _) = typeck.pat_ty(pat).kind() else {
                refuse_all(out, "the struct pattern's type is not a struct");
                return;
            };
            if !adt.is_struct() {
                refuse_all(out, "the pattern names an enum variant or a union");
                return;
            }
            for field in fields {
                let field_name = field.ident.as_str();
                walk(walker, field.pat, &format!("{base}.{field_name}"), out);
            }
        }
        _ => refuse_all(out, "the pattern is not a tuple, struct or binding pattern"),
    }
}

/// `(field index, sub-pattern position)` for a positional pattern of
/// `written` sub-patterns with an optional `..` over `arity` fields.
fn positional_indices(
    written: usize,
    dotdot: rustc_hir::DotDotPos,
    arity: usize,
) -> Vec<(usize, usize)> {
    let split = dotdot.as_opt_usize().unwrap_or(written);
    (0..written)
        .map(|elem| {
            let index = if elem < split {
                elem
            } else {
                arity - (written - elem)
            };
            (index, elem)
        })
        .collect()
}

/// Whether `expr` uses a binding name as a CALL head (`p(x)`), where no
/// projection can stand in for it.
fn calls_a_binding(expr: &PureExpr, names: &HashSet<&str>) -> Option<String> {
    let mut found = None;
    // Used as a visitor: every node is returned unchanged.
    let _ = expr.rewrite_bottom_up(|node| {
        if let PureExpr::LogicFnCall { name, .. } = &node {
            if found.is_none() && names.contains(name.as_str()) {
                found = Some(name.clone());
            }
        }
        node
    });
    found
}

/// `expr` with every free occurrence of a pattern binding replaced by its
/// projection. `Ok(None)` when it mentions none; `Err` when it mentions one
/// with no projection, or calls one.
pub(crate) fn destructure_expr(
    expr: &PureExpr,
    bindings: &ParamPatternBindings,
) -> Result<Option<PureExpr>, String> {
    if bindings.is_empty() {
        return Ok(None);
    }
    let names: HashSet<&str> = bindings.names().collect();
    if let Some(name) = calls_a_binding(expr, &names) {
        return Err(format!("pattern binding `{name}` is called"));
    }
    let free = expr.free_vars();
    if let Some((name, why)) = bindings
        .unprojectable
        .iter()
        .find(|(name, _)| free.contains(name))
    {
        return Err(format!("pattern binding `{name}` has no projection: {why}"));
    }
    if !bindings
        .projections
        .iter()
        .any(|(name, _)| free.contains(name))
    {
        return Ok(None);
    }
    let terms = bindings.projection_terms()?;
    Ok(Some(expr.substitute_capture_avoiding(
        &terms,
        &CaptureAvoidingSubstOptions::default(),
    )))
}

/// The clause text with every free occurrence of a pattern binding spelled as
/// its projection, `(__twp_arg0.0)`.
///
/// Every lane reads clause TEXT and parses it itself, so the text is what must
/// change. The rewrite is a token scan, and it is checked, not trusted: the
/// rewritten text must parse to exactly the term [`destructure_expr`] builds
/// from the original, or the clause is refused (`Err`). `Ok(None)`: the clause
/// mentions no binding (or does not parse at all, which every lane already
/// refuses) and stays as written.
pub(crate) fn destructure_clause_text(
    clause: &str,
    bindings: &ParamPatternBindings,
) -> Result<Option<String>, String> {
    let Ok(original) = parse_contract(clause) else {
        return Ok(None);
    };
    let Some(expected) = destructure_expr(&original, bindings)? else {
        return Ok(None);
    };
    let rewritten = replace_binding_identifiers(clause, &bindings.projections)?;
    match parse_contract(&rewritten) {
        Ok(reparsed) if reparsed == expected => Ok(Some(rewritten)),
        Ok(_) => Err(format!(
            "`{rewritten}` does not denote `{clause}` with its pattern bindings destructured"
        )),
        Err(e) => Err(format!("`{rewritten}` does not parse: {e}")),
    }
}

/// What a refused clause is replaced by: text no contract parser accepts, so
/// every lane that reads the clause takes its existing fail-closed path for an
/// unparseable clause (the owner is not verified; a caller owes a synthetic
/// `false` for a `requires` and is granted nothing for an `ensures`).
fn refused_clause_marker(reason: &str) -> String {
    format!("@@ trust-wp refused this clause: {reason}")
}

/// The first read, in `clause`, of a binding in `held_mut` (one whose type
/// holds a `&mut` its parameter holds without being it) that no lane places
/// (D-179). A postcondition reads such a `&mut` only as the operand of `*`,
/// `^` or `@`, and the state rule refuses each of those in the owner's lane
/// and at every call alike (D-101); any other read (a field through Rust's
/// auto-deref, the reference itself handed to a function or compared) is at
/// a state no lane decides, since the body may have moved the `&mut` out of
/// the parameter before writing through it. Outside a postcondition its
/// prophecy `^` has no reading. `None` for a clause that does not parse:
/// every lane refuses that already.
fn unplaced_held_mut_read(
    clause: &str,
    held_mut: &[String],
    postcondition: bool,
) -> Option<String> {
    if held_mut.is_empty() {
        return None;
    }
    let parsed = parse_contract(clause).ok()?;
    let held = |name: &str| held_mut.iter().any(|binding| binding == name);
    let mut uses: HashMap<String, usize> = HashMap::new();
    let mut operand_uses: HashMap<String, usize> = HashMap::new();
    let mut prophecy = None;
    parsed.for_each_recursive(|node| match node {
        PureExpr::Var(name, _) if held(name) => *uses.entry(name.clone()).or_default() += 1,
        PureExpr::Deref(operand) | PureExpr::Final(operand) | PureExpr::View(operand) => {
            if let PureExpr::Var(name, _) = operand.as_ref() {
                if held(name) {
                    *operand_uses.entry(name.clone()).or_default() += 1;
                    if matches!(node, PureExpr::Final(_)) && prophecy.is_none() {
                        prophecy = Some(name.clone());
                    }
                }
            }
        }
        _ => {}
    });
    if postcondition {
        let mut names: Vec<&String> = uses.keys().collect();
        names.sort();
        names
            .into_iter()
            .find(|name| uses[*name] > operand_uses.get(*name).copied().unwrap_or(0))
            .map(|name| {
                format!(
                    "`{name}` holds a `&mut` its parameter holds without being it, and a \
                     postcondition reads that `&mut` only through `*`, `^` or `@`"
                )
            })
    } else {
        prophecy.map(|name| {
            format!("`^{name}` reads the final value of a `&mut` outside a postcondition")
        })
    }
}

/// A step of the place a clause reads a parameter at: a positional field
/// (`.0`, of a tuple or a tuple struct) or a named one (`.f`), as the logic
/// functions a field access lowers to spell it, or an element (`[i]`, which
/// the parser spells `index_logic`). Every element of an array has one type,
/// so the step does not record which element it reads.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PlaceStep {
    Positional(usize),
    Named(String),
    Element,
}

/// What a place of a parameter that holds a `&mut` is, for a postcondition's
/// read of it (D-181).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HeldPlace {
    /// A value that reaches no `&mut`, reached through none: read at entry,
    /// as a by-value parameter is.
    Value,
    /// One of the `&mut`s the parameter holds: its `*`, `^` and `@` are the
    /// state rule's to read, and it refuses each (D-101).
    MutableReference,
    /// Anything else: a place reached through a held `&mut` (a field by
    /// Rust's auto-deref), one that holds a `&mut` inside it, or one whose
    /// type is not followed.
    Unplaced,
}

/// The steps from the parameter `name` to the place `expr` reads, when
/// `expr` is `name` under field accesses and indexing only (outermost last).
/// An index that itself reads `name` is no step: the read it makes is
/// classified on its own, and a step that dropped it would hide it.
fn place_steps(expr: &PureExpr, name: &str) -> Option<Vec<PlaceStep>> {
    let mut steps = Vec::new();
    let mut at = expr;
    loop {
        match at {
            PureExpr::Var(var, _) if var == name => {
                steps.reverse();
                return Some(steps);
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if method == INDEX_LOGIC_METHOD
                && args.len() == 1
                && !args[0].free_vars().contains(name) =>
            {
                steps.push(PlaceStep::Element);
                at = receiver;
            }
            PureExpr::LogicFnCall { name: field, args } if args.len() == 1 => {
                let step = if let Some(index) = tuple_field_logic_fn_index(field) {
                    PlaceStep::Positional(index)
                } else if let Some(named) = field.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
                    PlaceStep::Named(named.to_string())
                } else {
                    return None;
                };
                steps.push(step);
                at = &args[0];
            }
            _ => return None,
        }
    }
}

/// [`HeldPlace`] of the place `steps` reach from a parameter of type `root`.
/// A step through a shared reference or a box reads its referent, as Rust's
/// auto-deref does; a step through a `&mut` is [`HeldPlace::Unplaced`].
fn classify_held_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    root: ty::Ty<'tcx>,
    steps: &[PlaceStep],
) -> HeldPlace {
    let mut at = root;
    for step in steps {
        loop {
            match at.kind() {
                ty::Ref(_, referent, ty::Mutability::Not) => at = *referent,
                _ if at.is_box() => at = at.expect_boxed_ty(),
                _ => break,
            }
        }
        let next = match (at.kind(), step) {
            (ty::Array(element, _) | ty::Slice(element), PlaceStep::Element) => Some(*element),
            (ty::Tuple(tys), PlaceStep::Positional(index)) => tys.get(*index).copied(),
            (ty::Adt(adt, args), _) if adt.is_struct() => {
                let fields = &adt.non_enum_variant().fields;
                let field = match step {
                    PlaceStep::Positional(index) => fields.iter().nth(*index),
                    PlaceStep::Named(named) => {
                        fields.iter().find(|field| field.name.as_str() == named)
                    }
                    PlaceStep::Element => None,
                };
                field.map(|field| field.ty(tcx, *args).skip_norm_wip())
            }
            _ => None,
        };
        let Some(next) = next else {
            return HeldPlace::Unplaced;
        };
        at = next;
    }
    if matches!(at.kind(), ty::Ref(_, _, ty::Mutability::Mut)) {
        HeldPlace::MutableReference
    } else if reaches_a_mutable_reference(tcx, typing_env, at) {
        HeldPlace::Unplaced
    } else {
        HeldPlace::Value
    }
}

/// Whether the postcondition `clause` reads the parameter `name` (one that
/// holds a `&mut` without being it) other than at a [`HeldPlace::Value`]
/// place, or as the operand of `*`, `^` or `@` at a
/// [`HeldPlace::MutableReference`] place (D-181). Each such read is replaced
/// by `true` bottom-up; a free `name` left over is a read no lane places: a
/// field read through the `&mut` by auto-deref (`t.0.f`), the `&mut` or a
/// value holding it compared or handed to a function (`t.0 == u`, `f(t)`).
fn unplaced_held_mut_param_read(
    clause: &PureExpr,
    name: &str,
    classify: &dyn Fn(&[PlaceStep]) -> HeldPlace,
) -> bool {
    if !clause.free_vars().contains(name) {
        return false;
    }
    let placed = clause.rewrite_bottom_up(|node| {
        let state_operand = match &node {
            PureExpr::Deref(operand) | PureExpr::Final(operand) | PureExpr::View(operand) => {
                place_steps(operand, name)
            }
            _ => None,
        };
        if state_operand.is_some_and(|steps| {
            !steps.is_empty() && classify(&steps) == HeldPlace::MutableReference
        }) {
            return PureExpr::Bool(true);
        }
        if place_steps(&node, name)
            .is_some_and(|steps| !steps.is_empty() && classify(&steps) == HeldPlace::Value)
        {
            return PureExpr::Bool(true);
        }
        node
    });
    placed.free_vars().contains(name)
}

/// Destructure the pattern bindings in a function's own clause texts (D-177):
/// each clause that mentions one is rewritten to name the parameter
/// projection, or replaced by a refusal. The same texts are read by the
/// owner's verification and by every caller, so both see the one rewrite.
/// `clause_kind` is `requires`, `ensures` or `variant`; only an `ensures` is
/// a postcondition.
pub(crate) fn destructure_contract_clauses(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    clause_kind: &str,
    clauses: &mut [String],
) {
    if clauses.is_empty() {
        return;
    }
    let bindings = param_pattern_bindings(tcx, def_id);
    if bindings.is_empty() {
        return;
    }
    let postcondition = clause_kind == "ensures";
    for clause in clauses.iter_mut() {
        let destructured = match unplaced_held_mut_read(clause, &bindings.held_mut, postcondition) {
            Some(reason) => Err(reason),
            None => destructure_clause_text(clause, &bindings),
        };
        match destructured {
            Ok(None) => {}
            Ok(Some(rewritten)) => *clause = rewritten,
            Err(reason) => {
                eprintln!(
                    "trust-wp: error: {}: {clause_kind} `{clause}` names a parameter pattern \
                     binding it cannot be stated over: {reason}; the clause is refused",
                    tcx.def_path_str(def_id.to_def_id())
                );
                *clause = refused_clause_marker(&reason);
            }
        }
    }
}

/// Refuse each of `def_id`'s own clauses that reads, free, a name every call
/// binds to an argument by position (`arg0`, `value`, `rhs`, ...:
/// `mir_analysis::is_positional_alias`) while the function has no parameter
/// of that name (D-179).
///
/// Such a name means something else where the clause is written — a module
/// constant, a static, a closure's capture — and the owner's lane reads it
/// so, while every call substitutes the argument at that position for it:
/// `#[ensures(result == value)]` over a `const value` was proved as `result
/// == 5` and granted to a caller of `f(1, 9)` as `result == 9`. The clause is
/// replaced by text no parser accepts, so the owner is refused and a caller
/// owes `false` for a `requires` and is granted nothing for an `ensures`.
/// The parameter names are the ones every call binds by
/// (`resolve_spec_or_mir_arg_names`); with none, every such name is refused.
pub(crate) fn refuse_positional_alias_collisions(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    clause_kind: &str,
    clauses: &mut [String],
) {
    if clauses.is_empty() {
        return;
    }
    let params = crate::mir_analysis::resolve_spec_or_mir_arg_names(tcx, def_id.to_def_id(), None)
        .unwrap_or_default();
    for clause in clauses.iter_mut() {
        let Ok(parsed) = parse_contract(clause) else {
            continue;
        };
        let mut colliding: Vec<String> = parsed
            .free_vars()
            .into_iter()
            .filter(|name| {
                crate::mir_analysis::is_positional_alias(name)
                    && !params.iter().any(|param| param == name)
            })
            .collect();
        colliding.sort();
        let Some(name) = colliding.first() else {
            continue;
        };
        let reason = format!(
            "it reads `{name}`, which is none of its parameters, and every call binds `{name}` \
             to an argument by position"
        );
        eprintln!(
            "trust-wp: error: {}: {clause_kind} `{clause}` is refused: {reason}",
            tcx.def_path_str(def_id.to_def_id())
        );
        *clause = refused_clause_marker(&reason);
    }
}

/// Refuse each of `def_id`'s own postconditions that reads a `&mut` one of
/// its parameters holds without being it (a tuple or an array holding one:
/// `is_held_mutable_parameter_type`) other than through `*`, `^` or `@`
/// (D-181).
///
/// The state rule refuses those three (D-101), but a field read through the
/// `&mut` by Rust's auto-deref (`t.0.f` of `t: (&mut S, i32)`) is none of
/// them, and every lane read it at entry: `t.0.f == old(t.0.f)` of a body
/// that increments it was verified. The body may move the `&mut` out of the
/// parameter before writing through it, so no lane places such a read in
/// either dialect, as for a pattern binding that holds one (D-179). Compared
/// whole, the owner's lane reads the `&mut` over its current value while a
/// call reads the comparison as which borrow the result holds
/// (tuple_param_held_mut_whole_swap_claimed_unswapped). The
/// clause is replaced by text no parser accepts: the owner is refused, and
/// a caller is granted nothing for it.
pub(crate) fn refuse_unplaced_held_mut_param_reads(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    clause_kind: &str,
    clauses: &mut [String],
) {
    if clause_kind != "ensures" || clauses.is_empty() {
        return;
    }
    let def_id = def_id.to_def_id();
    if !matches!(
        tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Fn
            | rustc_hir::def::DefKind::AssocFn
            | rustc_hir::def::DefKind::Closure
    ) {
        return;
    }
    let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
    let inputs = crate::mir_analysis::input_types(tcx, def_id).unwrap_or_default();
    let held: Vec<(String, ty::Ty<'_>)> = tcx
        .fn_arg_idents(def_id)
        .iter()
        .zip(inputs)
        .filter_map(|(ident, input)| Some((ident.as_ref()?.name.to_string(), input)))
        .filter(|(_, input)| {
            crate::mir_analysis::is_held_mutable_parameter_type(tcx, typing_env, *input)
        })
        .collect();
    if held.is_empty() {
        return;
    }
    for clause in clauses.iter_mut() {
        let Ok(parsed) = parse_contract(clause) else {
            continue;
        };
        let Some((name, _)) = held.iter().find(|(name, root)| {
            unplaced_held_mut_param_read(&parsed, name, &|steps| {
                classify_held_place(tcx, typing_env, *root, steps)
            })
        }) else {
            continue;
        };
        let reason = format!(
            "`{name}` holds a `&mut` without being one, and a postcondition reads that `&mut` \
             only through `*`, `^` or `@`"
        );
        eprintln!(
            "trust-wp: error: {}: {clause_kind} `{clause}` is refused: {reason}",
            tcx.def_path_str(def_id)
        );
        *clause = refused_clause_marker(&reason);
    }
}

/// An impl method that writes no clause of its own is verified against its
/// trait method's clause text, read by the IMPL's parameter names. A trait
/// default's clause over a pattern binding names the parameter the binding is
/// projected from (its positional name, or an at-binding's own name), which
/// the trait's text never spelled; the impl may give that position another name, or give the
/// name to another position. Each inherited clause that mentions such a name
/// is kept only where the impl names the same position the same way, and is
/// otherwise replaced by a refusal: the impl discharges nothing, and its
/// refinement against the trait's text fails closed
/// (trait_default_pattern_clause_fallback_name_read_by_impl_param).
pub(crate) fn refuse_inherited_projections_on_renamed_params(
    tcx: TyCtxt<'_>,
    contracts: &mut [crate::contracts::FunctionContract],
    trait_contracts: &[crate::contracts::TraitMethodContract],
) {
    for contract in contracts.iter_mut() {
        let Some(trait_method) = tcx
            .opt_associated_item(contract.def_id)
            .and_then(|assoc| assoc.trait_item_def_id())
        else {
            continue;
        };
        let Some(trait_contract) = trait_contracts
            .iter()
            .find(|trait_contract| trait_contract.method_def_id == trait_method)
        else {
            continue;
        };
        // Only the text `apply_trait_contract_inheritance` copied is the
        // trait's; an impl's own clauses name its own parameters.
        if contract.requires != trait_contract.requires
            || contract.ensures != trait_contract.ensures
        {
            continue;
        }
        let Some((trait_body, trait_names)) = trait_method
            .as_local()
            .and_then(|local| hir_params_and_names(tcx, local))
        else {
            continue;
        };
        let impl_names = hir_params_and_names(tcx, contract.local_def_id)
            .map(|(_, names)| names)
            .unwrap_or_default();
        let renamed: HashSet<&str> = trait_body
            .params
            .iter()
            .zip(&trait_names)
            .enumerate()
            .filter(|(_, (param, _))| {
                !matches!(param.pat.kind, rustc_hir::PatKind::Binding(_, _, _, None))
            })
            .filter(|(position, (_, name))| impl_names.get(*position) != Some(*name))
            .map(|(_, (_, name))| name.as_str())
            .collect();
        if renamed.is_empty() {
            continue;
        }
        for (clause_kind, clauses) in [
            ("requires", &mut contract.requires),
            ("ensures", &mut contract.ensures),
        ] {
            for clause in clauses.iter_mut() {
                let Ok(parsed) = parse_contract(clause) else {
                    continue;
                };
                let free = parsed.free_vars();
                let Some(name) = renamed.iter().find(|name| free.contains(**name)) else {
                    continue;
                };
                let reason = format!(
                    "it is inherited from `{}` and names that method's parameter `{name}`, \
                     which this impl names differently",
                    tcx.def_path_str(trait_method)
                );
                eprintln!(
                    "trust-wp: error: {}: {clause_kind} `{clause}` is refused: {reason}",
                    tcx.def_path_str(contract.def_id)
                );
                *clause = refused_clause_marker(&reason);
            }
        }
    }
}

/// Rewrite or refuse each clause of the closure `def_id` that names a binding
/// its function binds more than once (D-238): a capture of one is renamed to
/// the name only the capture substitution answers
/// (`binding_identity::capture_clause_name`), and a clause naming one the
/// closure does not capture, or one of another hygiene, is refused. Every
/// call site reads a closure's clause in its caller's body, where a parameter
/// keeps its source name (D-237); read as written, such a name was the
/// parameter. As for a pattern binding, the rewrite is a token scan checked by
/// reparsing: the new text must parse to the original with each name renamed,
/// or the clause is refused.
pub(crate) fn resolve_closure_clause_names(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    clause_kind: &str,
    clauses: &mut [String],
) {
    if clauses.is_empty() || !tcx.is_closure_like(def_id.to_def_id()) {
        return;
    }
    for clause in clauses.iter_mut() {
        let Ok(original) = parse_contract(clause) else {
            continue;
        };
        let mut names: Vec<String> = original
            .free_vars()
            .into_iter()
            .filter(|name| !matches!(name.as_str(), "result" | "self"))
            .collect();
        names.sort();
        let mut renames: Vec<(String, String)> = Vec::new();
        let mut refusal = None;
        for name in names {
            match crate::mir_analysis::binding_identity::closure_clause_name(tcx, def_id, &name) {
                crate::mir_analysis::binding_identity::ClosureClauseName::AsWritten => {}
                crate::mir_analysis::binding_identity::ClosureClauseName::Capture(renamed) => {
                    renames.push((name, renamed));
                }
                crate::mir_analysis::binding_identity::ClosureClauseName::Refused(reason) => {
                    refusal = Some(reason);
                    break;
                }
            }
        }
        let outcome = match refusal {
            Some(reason) => Err(reason),
            None if renames.is_empty() => continue,
            None => rename_clause_identifiers(clause, &original, &renames),
        };
        match outcome {
            Ok(rewritten) => *clause = rewritten,
            Err(reason) => {
                eprintln!(
                    "trust-wp: error: {}: {clause_kind} `{clause}` of a closure is refused: \
                     {reason}",
                    tcx.def_path_str(def_id.to_def_id())
                );
                *clause = refused_clause_marker(&reason);
            }
        }
    }
}

/// `clause` with each free identifier of `renames` spelled as its new name,
/// checked to parse to `original` with those names renamed.
fn rename_clause_identifiers(
    clause: &str,
    original: &PureExpr,
    renames: &[(String, String)],
) -> Result<String, String> {
    let rewritten = replace_binding_identifiers(clause, renames)?;
    let mut expected = original.clone();
    for (name, renamed) in renames {
        expected = trust_wp_core::formula::rename_free_var(
            &expected,
            name,
            renamed,
            &CaptureAvoidingSubstOptions::default(),
        );
    }
    match parse_contract(&rewritten) {
        Ok(reparsed) if reparsed == expected => Ok(rewritten),
        Ok(_) => Err(format!(
            "`{rewritten}` does not denote `{clause}` with its captures renamed"
        )),
        Err(e) => Err(format!("`{rewritten}` does not parse: {e}")),
    }
}

/// Replace each identifier token that names a binding, and is not a field or
/// method name (`.p`), a path segment (`a::p`, `p::a`), a macro (`p!`) or a
/// lifetime (`'p`), by `(projection)`. A binding spelled as a call head
/// (`p(..)`) is an `Err`.
fn replace_binding_identifiers(
    text: &str,
    projections: &[(String, String)],
) -> Result<String, String> {
    let lookup: HashMap<&str, &str> = projections
        .iter()
        .map(|(name, projection)| (name.as_str(), projection.as_str()))
        .collect();
    let bytes = text.as_bytes();
    let is_ident_start = |b: u8| b.is_ascii_alphabetic() || b == b'_';
    let is_ident_continue = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut out = String::with_capacity(text.len());
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        if !is_ident_start(byte) || (index > 0 && is_ident_continue(bytes[index - 1])) {
            let ch = text[index..].chars().next().unwrap_or(' ');
            out.push(ch);
            index += ch.len_utf8();
            continue;
        }
        let start = index;
        while index < bytes.len() && is_ident_continue(bytes[index]) {
            index += 1;
        }
        let word = &text[start..index];
        let Some(projection) = lookup.get(word) else {
            out.push_str(word);
            continue;
        };
        let before = text[..start].trim_end();
        let after = text[index..].trim_start();
        let qualified = before.ends_with('.')
            || before.ends_with("::")
            || before.ends_with('\'')
            || before.ends_with('#')
            || after.starts_with("::")
            || (after.starts_with('!') && !after.starts_with("!="));
        if qualified {
            out.push_str(word);
        } else if after.starts_with('(') {
            return Err(format!("pattern binding `{word}` is called"));
        } else {
            out.push('(');
            out.push_str(projection);
            out.push(')');
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tuple_binding() -> ParamPatternBindings {
        ParamPatternBindings {
            projections: vec![
                ("a".to_string(), "arg0.0".to_string()),
                ("b".to_string(), "arg0.1".to_string()),
            ],
            unprojectable: Vec::new(),
            held_mut: Vec::new(),
        }
    }

    #[test]
    fn a_clause_over_a_pattern_binding_names_the_parameter_projection() {
        let rewritten = destructure_clause_text("result == a", &tuple_binding())
            .expect("destructurable")
            .expect("mentions a binding");
        assert_eq!(rewritten, "result == (arg0.0)");
    }

    #[test]
    fn a_clause_that_mentions_no_binding_is_left_as_written() {
        assert_eq!(
            destructure_clause_text("result == x && x.a > 0", &tuple_binding()),
            Ok(None)
        );
    }

    #[test]
    fn field_method_and_path_spellings_are_not_the_binding() {
        let rewritten = destructure_clause_text("s.a == a && t.a() == b@", &tuple_binding())
            .expect("destructurable")
            .expect("mentions a binding");
        assert_eq!(rewritten, "s.a == (arg0.0) && t.a() == (arg0.1)@");
    }

    #[test]
    fn a_binder_that_shadows_a_binding_is_refused_not_rewritten() {
        // The token scan cannot see scopes; the reparse check catches it.
        assert!(destructure_clause_text(
            "forall<a: Int> a >= 0 ==> result@ >= a && result == b",
            &tuple_binding()
        )
        .is_err());
    }

    #[test]
    fn a_called_binding_is_refused() {
        assert!(destructure_clause_text("a(1) == result", &tuple_binding()).is_err());
    }

    #[test]
    fn an_unprojectable_binding_refuses_the_clause_that_mentions_it() {
        let bindings = ParamPatternBindings {
            projections: vec![("a".to_string(), "arg0.0".to_string())],
            unprojectable: vec![("r".to_string(), "it binds by reference".to_string())],
            held_mut: Vec::new(),
        };
        assert!(destructure_clause_text("result == *r", &bindings).is_err());
        assert_eq!(
            destructure_clause_text("result == a", &bindings),
            Ok(Some("result == (arg0.0)".to_string()))
        );
    }

    #[test]
    fn a_body_binding_is_substituted_only_where_free() {
        let body = parse_contract("{ let a = 1; a } + b").expect("parses");
        let destructured = destructure_expr(&body, &tuple_binding())
            .expect("destructurable")
            .expect("mentions b");
        assert!(!destructured.free_vars().contains("b"));
        assert!(destructured.free_vars().contains("arg0"));
        assert!(!destructured.free_vars().contains("a"));
    }

    #[test]
    fn the_refusal_marker_is_refused_by_every_contract_parser() {
        let marker = refused_clause_marker("pattern binding `a` has no projection");
        assert!(parse_contract(&marker).is_err());
        assert!(trust_wp_core::contract_parser::parse_contract_spanned(&marker).is_err());
        assert!(trust_wp_core::contract_parser::parse_contract_body(&marker).is_err());
        assert!(
            trust_wp_core::contract_parser::parse_contract_body_with_leading_exprs(&marker)
                .is_err()
        );
    }

    #[test]
    fn a_projection_that_does_not_parse_refuses() {
        let bindings = ParamPatternBindings {
            projections: vec![("a".to_string(), "$anon_arg0.0".to_string())],
            unprojectable: Vec::new(),
            held_mut: Vec::new(),
        };
        assert!(destructure_expr(&parse_contract("a + 1").expect("parses"), &bindings).is_err());
    }

    #[test]
    fn a_held_mut_binding_is_read_in_a_postcondition_only_through_a_state_operator() {
        let held = vec!["p".to_string()];
        // Each of these the state rule refuses with D-101's reason.
        for clause in ["*p == old(*p) + 1", "^p == *p + 1", "p@ == old(p@)"] {
            assert_eq!(
                unplaced_held_mut_read(clause, &held, true),
                None,
                "{clause}"
            );
        }
        for clause in [
            "p.f == old(p.f)",
            "p == p",
            "f(p) == 1",
            "*p == 1 && p.f == 2",
        ] {
            assert!(
                unplaced_held_mut_read(clause, &held, true).is_some(),
                "{clause}"
            );
        }
        assert_eq!(unplaced_held_mut_read("q.f == 1", &held, true), None);
    }

    #[test]
    fn a_held_mut_binding_is_read_at_entry_outside_a_postcondition_but_not_its_prophecy() {
        let held = vec!["p".to_string()];
        for clause in ["*p < 100", "p.f < 100", "p@ == 1"] {
            assert_eq!(
                unplaced_held_mut_read(clause, &held, false),
                None,
                "{clause}"
            );
        }
        assert!(unplaced_held_mut_read("^p == 1", &held, false).is_some());
    }

    /// `t: (&mut S, i32)`: `t.0` is the held `&mut`, anything through it is
    /// read by auto-deref, `t.1` is a value.
    fn tuple_holding_a_mut(steps: &[PlaceStep]) -> HeldPlace {
        match steps.first() {
            Some(PlaceStep::Positional(0)) if steps.len() == 1 => HeldPlace::MutableReference,
            Some(PlaceStep::Positional(1)) => HeldPlace::Value,
            _ => HeldPlace::Unplaced,
        }
    }

    fn unplaced_tuple_read(clause: &str) -> bool {
        let parsed = parse_contract(clause).expect("parses");
        unplaced_held_mut_param_read(&parsed, "t", &tuple_holding_a_mut)
    }

    #[test]
    fn a_field_access_chain_names_its_steps_from_the_parameter() {
        let parsed = parse_contract("t.0.f").expect("parses");
        assert_eq!(
            place_steps(&parsed, "t"),
            Some(vec![
                PlaceStep::Positional(0),
                PlaceStep::Named("f".to_string())
            ])
        );
        assert_eq!(place_steps(&parsed, "u"), None);
        let parsed = parse_contract("*t.0").expect("parses");
        assert_eq!(place_steps(&parsed, "t"), None);
    }

    #[test]
    fn a_held_mut_of_a_tuple_parameter_is_read_only_through_a_state_operator_or_at_a_value() {
        // The state rule refuses each `*`, `^` and `@` of `t.0` (D-101); a
        // value beside it, a name that is not the parameter, and a binder
        // that shadows it are no read of the `&mut`.
        for clause in [
            "*t.0 == old(*t.0) + 1",
            "^t.0 == *t.0",
            "t.0@ == 1",
            "(*t.0)@ == old((*t.0)@)",
            "t.1 == t.1 + 0",
            "u.0.f == 1",
            "forall<t: Int> t == t",
        ] {
            assert!(!unplaced_tuple_read(clause), "{clause}");
        }
        for clause in [
            "t.0.f == old(t.0.f)",
            "old(t.0.f) == 1",
            "t.0 == t.0",
            "f(t) == 1",
            "resolve(t)",
            "*t.0 == 1 && t.0.f == 2",
            "{ let u = t.0; *u == 1 }",
            "match t { (a, b) => *a == b }",
        ] {
            assert!(unplaced_tuple_read(clause), "{clause}");
        }
    }

    /// `a: [&mut S; 2]`: every element is a held `&mut`.
    fn array_of_mut(steps: &[PlaceStep]) -> HeldPlace {
        match steps {
            [PlaceStep::Element] => HeldPlace::MutableReference,
            _ => HeldPlace::Unplaced,
        }
    }

    #[test]
    fn an_element_of_an_array_parameter_is_a_place_and_its_index_is_read_on_its_own() {
        let parsed = parse_contract("a[i].f").expect("parses");
        assert_eq!(
            place_steps(&parsed, "a"),
            Some(vec![PlaceStep::Element, PlaceStep::Named("f".to_string())])
        );
        let parsed = parse_contract("a[a[0].f]").expect("parses");
        assert_eq!(place_steps(&parsed, "a"), None);
        let unplaced = |clause: &str| {
            let parsed = parse_contract(clause).expect("parses");
            unplaced_held_mut_param_read(&parsed, "a", &array_of_mut)
        };
        // The state rule refuses each `*`, `^` and `@` of an element (D-101).
        for clause in ["^a[0] == *a[0] + 1", "*a[i] == old(*a[i])", "a[0]@ == 1"] {
            assert!(!unplaced(clause), "{clause}");
        }
        for clause in ["a[0].f == 1", "a[0] == a[1]", "*a[a[0].f] == 1", "a@ == a@"] {
            assert!(unplaced(clause), "{clause}");
        }
    }

    #[test]
    fn a_trailing_rest_keeps_positions_and_a_leading_rest_counts_from_the_end() {
        assert_eq!(
            positional_indices(2, rustc_hir::DotDotPos::new(Some(1)), 4),
            vec![(0, 0), (3, 1)]
        );
        assert_eq!(
            positional_indices(2, rustc_hir::DotDotPos::new(None), 2),
            vec![(0, 0), (1, 1)]
        );
    }
}
