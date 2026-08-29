// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand},
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::PureExpr;
use trust_wp_driver::StdSpec;

use super::mut_ref_local_for_operand;
use crate::mir_analysis::{
    call_resolve::{arg_names_for_def_id, extract_closure_def_id_from_fn_call},
    extract::call_resolve_shared::{resolve_call, ResolvedCallKind},
    translate::ExprLookup,
};

pub(in crate::mir_analysis::extract) fn spec_mutates_closure_state(spec: &StdSpec) -> bool {
    spec.ensures.iter().any(|ens| {
        ens.contains("postcondition_mut(")
            || ens.contains("postcondition_once(")
            || ens.contains(".postcondition_mut(")
            || ens.contains(".postcondition_once(")
    })
}

fn param_aliases_for_arg_index(param_names: Option<&[String]>, arg_index: usize) -> Vec<String> {
    let mut aliases = vec![format!("arg{arg_index}")];
    if arg_index == 0 {
        aliases.push("self".to_string());
    }
    if let Some(name) = param_names.and_then(|names| names.get(arg_index)) {
        if !aliases.iter().any(|alias| alias == name) {
            aliases.push(name.clone());
        }
    }
    aliases
}

fn expr_root_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => {
            expr_root_var_name(inner)
        }
        _ => None,
    }
}

fn deref_root_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Deref(inner) => expr_root_var_name(inner),
        PureExpr::Final(inner) | PureExpr::View(inner) => deref_root_var_name(inner),
        _ => None,
    }
}

fn collect_mutating_ref_aliases(expr: &PureExpr, vars: &mut HashSet<String>) {
    expr.for_each_recursive(|node| match node {
        PureExpr::Final(inner) => {
            if let Some(name) = expr_root_var_name(inner) {
                vars.insert(name.to_string());
            }
        }
        PureExpr::Old(inner) => {
            if let Some(name) = deref_root_var_name(inner) {
                vars.insert(name.to_string());
            }
        }
        _ => {}
    });
}

pub(in crate::mir_analysis::extract) fn spec_mentions_post_state_for_aliases(
    spec: &StdSpec,
    aliases: &[String],
) -> bool {
    if aliases.is_empty() {
        return false;
    }

    if spec_mutates_closure_state(spec)
        && aliases
            .iter()
            .any(|alias| alias == "self" || alias == "arg0")
    {
        return true;
    }

    let mut parse_failed = false;
    let mut mutating_aliases = HashSet::new();
    for ensures in &spec.ensures {
        if let Ok(expr) = trust_wp_core::contract_parser::parse_contract(ensures) {
            collect_mutating_ref_aliases(&expr, &mut mutating_aliases);
        } else {
            parse_failed = true;
            break;
        }
    }

    if parse_failed {
        return true;
    }

    aliases
        .iter()
        .any(|alias| mutating_aliases.contains(alias.as_str()))
}

pub(in crate::mir_analysis::extract) fn all_mut_ref_arg_positions(
    body: &Body<'_>,
    args: &[Spanned<Operand<'_>>],
) -> Vec<usize> {
    args.iter()
        .enumerate()
        .filter_map(|(idx, arg)| mut_ref_local_for_operand(body, &arg.node).map(|_| idx))
        .collect()
}

pub(in crate::mir_analysis::extract) fn spec_mutating_ref_arg_positions<'tcx>(
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    spec: &StdSpec,
    param_names: Option<&[String]>,
) -> Vec<usize> {
    all_mut_ref_arg_positions(body, args)
        .into_iter()
        .filter(|idx| {
            let aliases = param_aliases_for_arg_index(param_names, *idx);
            spec_mentions_post_state_for_aliases(spec, &aliases)
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
pub(in crate::mir_analysis::extract) fn resolved_call_mutating_ref_arg_positions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: Local,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    local_exprs: &impl ExprLookup,
) -> Vec<usize> {
    if let Some(closure_def_id) = extract_closure_def_id_from_fn_call(func) {
        if let Some(spec) = user_specs.get(&closure_def_id) {
            return if args
                .first()
                .and_then(|arg| mut_ref_local_for_operand(body, &arg.node))
                .is_some()
                && spec_mutates_closure_state(spec)
            {
                vec![0]
            } else {
                Vec::new()
            };
        }
    }

    let resolved = resolve_call(
        tcx,
        body,
        bb,
        func,
        args,
        destination,
        user_specs,
        trait_specs,
        extern_specs,
        None,
        local_exprs,
    );
    let Some(def_id) = resolved.def_id else {
        return Vec::new();
    };

    match resolved.kind {
        ResolvedCallKind::DirectSpec(spec) | ResolvedCallKind::ExternSpec(spec) => {
            let param_names =
                arg_names_for_def_id(tcx, def_id).or_else(|| spec.param_names.clone());
            spec_mutating_ref_arg_positions(body, args, &spec, param_names.as_deref())
        }
        ResolvedCallKind::ArrayLen(_)
        | ResolvedCallKind::TryBranch
        | ResolvedCallKind::BoxNew
        | ResolvedCallKind::IntPassthrough(_)
        | ResolvedCallKind::LayoutIntrinsic(_)
        | ResolvedCallKind::MappingFromClosure
        | ResolvedCallKind::MapInvFromClosure
        | ResolvedCallKind::Opaque => Vec::new(),
    }
}
