// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What owes a precondition among the definitions rustc resolved a logic
//! body's calls to (`logic::call_resolution`), in the terms the
//! callee-precondition walk reads (`logic_fn_verify::callee_preconditions`,
//! D-136).

use std::collections::HashSet;

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE},
};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::logic::LogicFnDef;

use super::super::logic_fn_verify::{BodyCallees, LogicBodyCallees, RecordedBody, ResolvedCallee};
use crate::logic::call_resolution::{
    logic_body_calls, shared_fn_paths, LogicBodyCalls, ParsedCalls,
};

/// The resolved calls of every logic function in `logic_fns`, each callee
/// classified: one of `logic_fns` by path, a standard logic function by its
/// resolved path, a callee whose precondition no logic body may owe (a
/// program function with a `requires`, a logic function the lane never read),
/// or one that owes nothing. `program_fns_with_requires` are the crate's
/// program functions with a precondition (`program_callees`).
pub(super) fn logic_body_callees(
    tcx: TyCtxt<'_>,
    logic_fns: &[LogicFnDef],
    program_fns_with_requires: &HashSet<DefId>,
) -> LogicBodyCallees {
    let logic_paths: HashSet<&str> = logic_fns.iter().map(LogicFnDef::full_path).collect();
    let shared_paths = shared_fn_paths(tcx);
    let classify = |def_id: DefId| {
        classify_callee(
            tcx,
            def_id,
            &logic_paths,
            &shared_paths,
            program_fns_with_requires,
        )
    };
    let mut out = LogicBodyCallees::default();
    for logic_fn in logic_fns {
        let resolved = match logic_body_calls(logic_fn.full_path()) {
            Some(LogicBodyCalls::Typed { calls, parsed }) => {
                let mut body = BodyCallees::default();
                if let Some(why) = inlining_refusal(&parsed) {
                    body.refuse(why);
                }
                body.keep_written_calls(parsed.kept);
                for call in calls {
                    let callees = if call.callees.is_empty() {
                        vec![ResolvedCallee::Refused(
                            "a call through a callee rustc does not name (a function pointer)"
                                .to_string(),
                        )]
                    } else {
                        call.callees.iter().copied().map(classify).collect()
                    };
                    body.push(call.spelling, callees);
                }
                RecordedBody::Typed(body)
            }
            Some(LogicBodyCalls::Untyped { parsed }) => RecordedBody::Untyped {
                written_call: parsed.first.or_else(|| {
                    parsed
                        .beyond_reach
                        .then(|| "a call nested deeper than the body search reaches".to_string())
                }),
            },
            Some(LogicBodyCalls::Misread { why }) => RecordedBody::Misread(why),
            None => RecordedBody::Untyped { written_call: None },
        };
        out.insert(logic_fn.full_path(), resolved);
    }
    out
}

/// Why the walk, which reads the body after inlining, cannot place the
/// written body's calls: an inlined call's arguments call something, and
/// the substitution moves them under the callee's branches, drops them or
/// copies them, where Creusot evaluates each once before the call
/// (logic_fn_callee_precondition_inlined_argument_under_branch.rs,
/// logic_fn_callee_precondition_inlined_argument_dropped_refilled.rs).
fn inlining_refusal(parsed: &ParsedCalls) -> Option<String> {
    if parsed.beyond_reach {
        return Some("a call nested deeper than the body search reaches".to_string());
    }
    parsed.inlined_calling_argument.as_ref().map(|name| {
        format!(
            "a call `{name}` the verifier inlines, whose arguments call a function: the inlined \
             body evaluates an argument where its callee reads the parameter, and Creusot \
             evaluates it once, before the call"
        )
    })
}

/// A local callee is matched to its logic function by path, which is sound
/// only for a path no other local function prints as: two functions declared
/// in two blocks of one body share one (`host::k`), and the one the lane read
/// may not be the one called (logic_fn_callee_precondition_block_local_same_path.rs).
fn classify_callee(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    logic_paths: &HashSet<&str>,
    shared_paths: &HashSet<String>,
    program_fns_with_requires: &HashSet<DefId>,
) -> ResolvedCallee {
    if !matches!(
        tcx.def_kind(def_id),
        DefKind::Fn | DefKind::AssocFn | DefKind::Closure
    ) {
        // A constructor, a struct or variant a literal names.
        return ResolvedCallee::Free;
    }
    let relative = tcx.def_path_str(def_id);
    let attrs = tcx.get_all_attrs(def_id);
    let is_logic = crate::logic::has_logic_marker(attrs);
    let has_requires = !crate::logic::extract_requires(attrs).is_empty();
    if def_id.is_local() {
        let full = format!("{}::{relative}", tcx.crate_name(LOCAL_CRATE));
        if shared_paths.contains(&full) {
            return ResolvedCallee::Refused(format!(
                "denotes a function printed `{full}`, a path another local function shares, so \
                 which definition's precondition it owes cannot be told"
            ));
        }
        if logic_paths.contains(full.as_str()) {
            return ResolvedCallee::Logic(full);
        }
        if program_fns_with_requires.contains(&def_id) {
            return ResolvedCallee::Refused(format!(
                "denotes the program function `{full}`, which has a precondition and which a \
                 logic body cannot call"
            ));
        }
        if is_logic && has_requires {
            return ResolvedCallee::Refused(format!(
                "denotes the logic function `{full}`, whose definition the logic lane did not \
                 read"
            ));
        }
        return ResolvedCallee::Free;
    }
    if is_logic {
        if has_requires {
            return ResolvedCallee::Refused(format!(
                "denotes the logic function `{relative}` of another crate, whose precondition \
                 the logic lane does not read"
            ));
        }
        return ResolvedCallee::Std(relative);
    }
    if is_creusot_total_seq_method(tcx, def_id) {
        return ResolvedCallee::Std(relative);
    }
    let requires = crate::callbacks::thread_locals::EXTERN_SPECS.with(|specs| {
        trust_wp_driver::lookup_spec_with_extern(Some(&specs.borrow()), &relative)
            .is_some_and(|spec| !spec.requires.is_empty())
    });
    if requires {
        return ResolvedCallee::Refused(format!(
            "denotes the program function `{relative}`, which has a precondition and which a \
             logic body cannot call"
        ));
    }
    ResolvedCallee::Std(relative)
}

/// The methods of `trust_wp_std`'s `Seq` that Creusot declares `#[logic]`
/// with no `requires` (creusot-std `logic/seq.rs`): out of range the value is
/// unspecified, not a violation. `trust_wp_std` implements `Seq` as executable
/// Rust, so these carry no logic marker, and the program-side table gives each
/// the precondition its executable form panics without (`Seq::tail` on an
/// empty sequence). A logic body's call owes what Creusot declares, which is
/// nothing (logic_fn_std_seq_total_methods_control.rs). Every other function
/// of another crate the program table gives a precondition stays refused
/// (logic_fn_std_program_method_precondition.rs).
const CREUSOT_TOTAL_SEQ_METHODS: &[&str] = &[
    "index_logic",
    "tail",
    "pop_front",
    "pop_back",
    "subsequence",
    "set",
];

/// Whether `def_id` is one of `CREUSOT_TOTAL_SEQ_METHODS`: a method of an
/// impl, inherent or of a trait, whose self type is `trust_wp_std`'s `Seq`.
fn is_creusot_total_seq_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(impl_id) = tcx.impl_of_assoc(def_id) else {
        return false;
    };
    let Some(adt) = tcx.type_of(impl_id).skip_binder().ty_adt_def() else {
        return false;
    };
    !adt.did().is_local()
        && tcx.crate_name(adt.did().krate).as_str() == "trust_wp_std"
        && tcx.item_name(adt.did()).as_str() == "Seq"
        && CREUSOT_TOTAL_SEQ_METHODS.contains(&tcx.item_name(def_id).as_str())
}
