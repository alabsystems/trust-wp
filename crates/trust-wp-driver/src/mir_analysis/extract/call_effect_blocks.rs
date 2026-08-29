// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Block-scoped call effect collection for assumption/obligation filtering.
//!
//! This module provides [`collect_call_effects_for_blocks`], a generalized
//! version of [`super::loop_body::collect_loop_body_call_obligations`] that
//! collects **full** [`CallEffects`] (obligations + assumptions) from a given
//! set of basic blocks.
//!
//! Used by `callbacks/parsing/extraction.rs` to filter loop-body call
//! assumptions out of the function-level verification path. (#2496)
//!
//! ## Why a separate module?
//!
//! `loop_body.rs` collects obligations only (for loop induction). This module
//! collects full effects (for function-level filtering). The setup logic
//! (local_exprs seeding, pre-target walk) is duplicated rather than extracted
//! because the two modules have different callers and different evolution
//! paths.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::PureExpr;
use trust_wp_driver::{lookup_spec_with_extern, StdSpec};

use super::{
    super::{
        call_resolve::{
            arg_names_for_def_id, extract_call_def_id, resolve_trait_method_def_id,
            ufcs_path_for_call,
        },
        effects::CallEffects,
        spec_apply::{apply_postconditions_with_effects, collect_precondition_obligations},
        translate::{translate_rvalue_typed, ty_to_expr_sort_enriched},
    },
    helpers::translate_rvalue_with_enum_variants,
    translate_call_args_for_substitutions_with_tcx,
};

/// Collect full call effects (obligations + postcondition-derived assumptions)
/// from a specified set of basic blocks. (#2496)
///
/// This is the generalized version of `collect_loop_body_call_obligations`:
/// instead of returning only precondition obligations, it returns a complete
/// [`CallEffects`] including postcondition-derived assumptions.
///
/// Used to compute non-loop call effects for function-level verification,
/// ensuring that loop-body assumptions don't leak into the post-loop VC.
///
/// # Arguments
/// * `allowed_blocks` - Set of basic blocks to walk (typically non-loop blocks)
///
/// Note: mapping_closure detection is not replicated here (it requires the
/// full extraction context). Mapping closure filtering is tracked separately.
pub(crate) fn collect_call_effects_for_blocks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    allowed_blocks: &HashSet<BasicBlock>,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> CallEffects {
    // Build local_exprs from arguments and debug info (same as loop_body.rs).
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    let mut local_names: HashMap<Local, String> = HashMap::new();
    let param_locals: HashSet<Local> = (0..arg_names.len())
        .map(|i| Local::from_usize(i + 1))
        .collect();

    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
        local_names.insert(local, name.clone());
    }

    // Seed with debug info variable names for symbolic resolution.
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty() && !param_locals.contains(&place.local) {
                let name = var_debug.name.to_string();
                let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
                local_exprs.insert(place.local, PureExpr::Var(name.clone(), sort));
                local_names.insert(place.local, name);
            }
        }
    }

    // Walk from bb0 through allowed blocks to resolve pre-block temporaries,
    // so that argument expressions at call sites translate correctly.
    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut worklist = vec![BasicBlock::from_u32(0)];
    while let Some(bb) = worklist.pop() {
        if !allowed_blocks.contains(&bb) || !visited.insert(bb) {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    if let Some(expr) = translate_rvalue_with_enum_variants(
                        tcx,
                        rvalue,
                        &local_exprs,
                        Some(body),
                        None,
                        None,
                    )
                    .or_else(|| translate_rvalue_typed(tcx, rvalue, &local_exprs, Some(body)))
                    {
                        local_exprs.insert(place.local, expr);
                    }
                }
            }
        }
        if let TerminatorKind::Call { destination, .. } = &bb_data.terminator().kind {
            if destination.projection.is_empty() && !param_locals.contains(&destination.local) {
                local_exprs.entry(destination.local).or_insert_with(|| {
                    call_result_local_expr(tcx, body, destination.local, &local_names)
                });
            }
        }
        for succ in bb_data.terminator().successors() {
            worklist.push(succ);
        }
    }

    // Fixpoint resolution over ALL allowed blocks (#nested-mutref reborrow arg).
    //
    // The reachability walk above is limited to blocks reachable from bb0 *via
    // successors within `allowed_blocks`*. When the allowed set is the post-loop
    // (or non-loop) slice, blocks behind a loop are unreachable from bb0 through
    // that successor graph, so their assignments — notably reborrow temps like
    // `_t = &mut *x` materialized just before a `mem::replace(x, y)` call — never
    // populate `local_exprs`. Their call arguments then fall back to opaque
    // `argN` placeholders, divorcing the call's pre-state from the caller place
    // (`*x` ↔ `arg0`), which loses the chain needed to prove postconditions such
    // as `^*x == 1` (inferred_invariants::nested_borrows).
    //
    // Resolve every allowed block's straight-line assignments to a fixpoint.
    // SOUND: `translate_rvalue_*` is an exact (value-preserving) translation —
    // a reborrow `&mut *x` of an existing place `x` is *defined* to be `x` (same
    // location), so this only adds correct expression bindings, never a
    // spurious aliasing. It is precisely the REBORROW_OF_PLACE case (a fresh
    // borrow `&mut local` has no `Deref` of a tracked place and does not resolve
    // to a caller place here).
    let mut changed = true;
    while changed {
        changed = false;
        for &bb in allowed_blocks {
            for stmt in &body.basic_blocks[bb].statements {
                if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                    if place.projection.is_empty() && !local_exprs.contains_key(&place.local) {
                        if let Some(expr) = translate_rvalue_with_enum_variants(
                            tcx,
                            rvalue,
                            &local_exprs,
                            Some(body),
                            None,
                            None,
                        )
                        .or_else(|| translate_rvalue_typed(tcx, rvalue, &local_exprs, Some(body)))
                        {
                            local_exprs.insert(place.local, expr);
                            changed = true;
                        }
                    }
                }
            }
        }
    }

    let mut effects = CallEffects::new();

    // Walk allowed blocks collecting call effects.
    for &bb in allowed_blocks {
        let bb_data = &body.basic_blocks[bb];
        let Some(ref terminator) = bb_data.terminator else {
            continue;
        };

        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            if let Some(def_id) = extract_call_def_id(func) {
                let translated_args = translate_call_args_for_substitutions_with_tcx(
                    args,
                    &local_exprs,
                    Some(body),
                    Some(tcx),
                );

                let hir_param_names = arg_names_for_def_id(tcx, def_id);

                let extern_opt = if extern_specs.is_empty() {
                    None
                } else {
                    Some(extern_specs)
                };
                let spec = user_specs
                    .get(&def_id)
                    .or_else(|| trait_specs.get(&def_id))
                    .cloned()
                    .or_else(|| {
                        ufcs_path_for_call(tcx, func)
                            .and_then(|ufcs_path| lookup_spec_with_extern(extern_opt, &ufcs_path))
                    })
                    .or_else(|| {
                        let path = tcx.def_path_str(def_id);
                        lookup_spec_with_extern(extern_opt, &path)
                    })
                    .or_else(|| {
                        let trait_method_id = resolve_trait_method_def_id(tcx, def_id)?;
                        let trait_path = tcx.def_path_str(trait_method_id);
                        lookup_spec_with_extern(extern_opt, &trait_path)
                    });

                if let Some(spec) = spec {
                    let param_names = hir_param_names.or_else(|| spec.param_names.clone());

                    // Collect precondition obligations.
                    collect_precondition_obligations(
                        &spec.requires,
                        &translated_args,
                        param_names.as_deref(),
                        &mut effects,
                    );

                    // Collect postcondition-derived assumptions. (#2496)
                    // Build the result variable from the call destination.
                    if !spec.ensures.is_empty() {
                        let result_var =
                            call_result_local_expr(tcx, body, destination.local, &local_names);
                        apply_postconditions_with_effects(
                            &spec.ensures,
                            &result_var,
                            &translated_args,
                            param_names.as_deref(),
                            &mut effects,
                            true,
                        );
                    }
                }
            }
        }
    }

    effects
}

fn call_result_local_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
    local_names: &HashMap<Local, String>,
) -> PureExpr {
    let name = local_names
        .get(&local)
        .cloned()
        .unwrap_or_else(|| format!("_call_{}", local.as_u32()));
    PureExpr::Var(
        name,
        ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty),
    )
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;

    use super::*;

    static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

    struct CallEffectsCallbacks {
        fn_name: String,
        assumptions_debug: Option<String>,
        ran: bool,
    }

    impl Callbacks for CallEffectsCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let suffix = format!("::{}", self.fn_name);

            for local_def_id in tcx.hir_body_owners() {
                let def_path = tcx.def_path_str(local_def_id);
                if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                    continue;
                }

                let body = tcx.optimized_mir(local_def_id.to_def_id());
                let allowed_blocks: HashSet<BasicBlock> = body.basic_blocks.indices().collect();
                let user_specs = HashMap::new();
                let trait_specs = HashMap::new();
                let extern_specs = HashMap::new();
                let effects = collect_call_effects_for_blocks(
                    tcx,
                    body,
                    &["self".to_string()],
                    &allowed_blocks,
                    &user_specs,
                    &trait_specs,
                    &extern_specs,
                );

                self.assumptions_debug = Some(format!("{:#?}", effects.assumptions));
                self.ran = true;
                return Compilation::Stop;
            }

            Compilation::Stop
        }
    }

    fn collect_assumptions_debug(source: &str, fn_name: &str) -> String {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_call_effect_blocks_{}_{}",
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
            "trust_wp_call_effect_blocks_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = CallEffectsCallbacks {
            fn_name: fn_name.to_string(),
            assumptions_debug: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);

        let _ = fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "failed to locate function `{fn_name}`");
        callbacks
            .assumptions_debug
            .expect("call effects should be collected")
    }

    #[test]
    fn pre_loop_vec_len_assumption_preserves_typed_field_receiver() {
        let source = r#"
pub struct MyMap {
    buckets: Vec<i32>,
}

impl MyMap {
    pub fn resize(&mut self) -> usize {
        let n = self.buckets.len();
        n * 2
    }
}
"#;

        let assumptions = collect_assumptions_debug(source, "resize");

        assert!(
            assumptions.contains("__trust_wp_field_buckets"),
            "Vec::len postcondition should be tied to self.buckets, got {assumptions}"
        );
        assert!(
            !assumptions.contains("\"arg0\""),
            "Vec::len receiver should not fall back to arg0, got {assumptions}"
        );
    }
}
