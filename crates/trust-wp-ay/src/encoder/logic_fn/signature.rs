// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use ay_dpll::api::{FuncDecl, Sort};
use trust_wp_core::{
    formula::{intern_sort_name, ExprSort},
    logic::LogicFnDef,
};

use super::param_sort_infer::{
    collect_cross_fn_seq_params, infer_param_datatypes_from_body, infer_seq_like_params,
};
use crate::encoder::{
    sort_context::is_seq_family_sort,
    unsoundness::{self, UnsoundnessCategory},
    AYEncoder,
};

impl AYEncoder {
    /// Preseed the sort resolver with the logic function's return sort hint.
    ///
    /// This enables `infer_expr_sort_impl` (the raw AST-level inference) to
    /// resolve the function's return sort via sort hints when the function
    /// hasn't been fully declared yet (ordering dependency between logic
    /// functions). Previously only Bool and Seq were preseeded; now all
    /// non-Int sorts are preseeded since Int is the default fallback and
    /// preseeding it provides no information. (#994, #2231)
    pub(super) fn preseed_logic_fn_return_sort_hint(&mut self, logic_fn: &LogicFnDef) {
        let Some(return_sort) = logic_fn.return_sort() else {
            return;
        };
        // Skip Int: it's the default fallback and preseeding it provides no
        // additional information to the sort resolver.
        if matches!(return_sort, ExprSort::Int) {
            return;
        }
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(logic_fn.name());
        self.record_sort_hint(smt_name, return_sort.clone());
    }

    pub(super) fn declare_logic_fn_signature(&mut self, logic_fn: &LogicFnDef) -> FuncDecl {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(logic_fn.name());

        if let Some(func_decl) = self.logic_func_decl_cloned(&smt_name) {
            return func_decl;
        }

        // Infer return sort from body expression, using declared function
        // signatures for LogicFnCall nodes. (#1965)
        //
        // `infer_expr_sort_with_context` checks declared logic functions for
        // the return sort of already-declared functions, so when function `f`
        // calls function `g` (declared earlier in the same batch), `g`'s
        // actual return sort is used instead of the Sort::Int default.
        //
        // Bracket with unsoundness snapshot/restore for
        // `SortFallbackToIntFromLogicFn`: this is an analytical scan of the
        // body during declaration, not an encoding step. When the body
        // contains recursive calls (e.g., `lemma_fib_bound` recursing on
        // itself) or calls to functions not yet declared, the AST-level
        // inference falls through to the demoting fallback even though the
        // final declaration uses the authoritative `logic_fn.return_sort()`
        // or sort_hint. Same rationale as the bracket pattern in
        // `result_binding.rs::assert_result_scalar_binding`. (#2671 follow-up,
        // analogous to #2062 collect_all_sort_hints suppression)
        let before_body_infer = unsoundness::snapshot();
        let mut return_sort = self.infer_expr_sort_with_context(logic_fn.body(), None);
        unsoundness::restore_category(
            &before_body_infer,
            UnsoundnessCategory::SortFallbackToIntFromLogicFn,
        );
        // Sort hints override syntactic inference when the body's sort can't be
        // determined purely syntactically. This happens for logic functions that
        // call other logic functions (e.g., `uses_simple() -> simple()` where
        // simple() returns Bool but LogicFnCall defaults to Int). (#544, #994)
        //
        // Check all hint variants (Bool, Seq, FMap), not just Bool. Logic
        // functions returning Seq or FMap whose bodies contain nested
        // LogicFnCalls (which default to Int) were getting Int return sort,
        // causing sort mismatches at call sites. (#994)
        if return_sort == Sort::Int {
            if let Some(sort) = logic_fn.return_sort() {
                return_sort = self.sort_from_param_sort(sort);
            } else if let Some(hint) = self.sort_hint_cloned(&smt_name) {
                return_sort = self.sort_from_expr_sort(hint);
            }
        }

        let mut inferred_seq_params = infer_seq_like_params(logic_fn);

        // Cross-function Seq inference (#1572): if a param is passed to an
        // already-declared logic function at a Seq-sorted position, mark it as
        // Seq. For example, `lemma_num_of_pos_increasing` passes `t` to
        // `num_of_pos(i,j,t)` where position 2 is Seq. Without this,
        // `infer_seq_like_params` misses params that are only used as arguments
        // to other functions (no direct Seq method calls like `.len()`,
        // `.index()`, etc.).
        {
            let param_set: HashSet<&str> = logic_fn.params().iter().map(String::as_str).collect();
            for expr in logic_fn
                .requires()
                .iter()
                .chain(logic_fn.ensures().iter())
                .chain(std::iter::once(logic_fn.body()))
            {
                collect_cross_fn_seq_params(
                    expr,
                    &param_set,
                    self.logic_funcs_ref(),
                    &mut inferred_seq_params,
                );
            }
        }

        // Datatype inference from match patterns (#2002): scan the body for
        // `match param { Ctor1(..) => .., Ctor2(..) => .. }` patterns to infer
        // Datatype sorts for parameters that would otherwise default to Int.
        // This resolves sort mismatches when logic functions on custom ADTs
        // (e.g., List::len(self)) are called with Datatype-sorted arguments.
        let inferred_dt_params = infer_param_datatypes_from_body(logic_fn)
            .into_iter()
            .map(|(param, dt)| (param, self.canonical_declared_datatype(&dt)))
            .collect::<std::collections::HashMap<_, _>>();
        for dt in inferred_dt_params.values() {
            self.ensure_datatype_declared(dt);
        }

        let old_param_var_sorts: Vec<(String, Option<Sort>)> = logic_fn
            .params()
            .iter()
            .map(|param| (param.clone(), self.remove_var_sort(param)))
            .collect();

        // Reuse already-declared function domains for passthrough parameters
        // before the declaration falls back to Int. This handles logic
        // functions that only forward a parameter into another declared
        // function and therefore never accumulate direct body-local evidence.
        // (#2002)
        self.preseed_logic_param_domain_sorts(logic_fn);

        // Resolve parameter sorts from LogicFnDef hints, falling back to Int.
        //
        // Priority: Datatype (from match patterns) > Seq (from method name heuristic)
        // > explicit param_sorts > sort_hints > Int default.
        //
        // Datatype inference is definitive: if a parameter is matched against
        // constructors (e.g., `match self { Cons(..) => .., Nil => .. }`),
        // it IS a Datatype — even if the prescan heuristically tagged it as Seq
        // because of ambiguous method names like `sum`, `len`, `get`. (#2002)
        let param_sorts: Vec<Sort> = logic_fn
            .params()
            .iter()
            .enumerate()
            .map(|(i, param_name)| {
                // Datatype inference from match patterns takes highest priority
                // because constructor patterns are definitive evidence of ADT sort.
                // This overrides Seq hints from ambiguous method names (#994, #2002).
                if let Some(dt) = inferred_dt_params.get(param_name.as_str()) {
                    return Sort::Datatype(dt.clone());
                }
                let resolved = self.resolve_logic_param_sort(logic_fn, i);
                // Seq heuristic override: promote Int→Seq when body method names
                // (.len(), .contains(), etc.) suggest a sequence parameter.
                //
                // GUARD: skip promotion when the parameter has an explicit sort
                // hint from the driver (param_sorts) that resolved to Int. Types
                // like FSet, HashSet, and Ghost share method names (.contains(),
                // .len()) with Seq but are Int-model types. Promoting them to
                // Seq(Int) creates sort mismatches in recursive calls where FSet
                // operations return Sort::Int. (#2701, #2567)
                let has_explicit_int_hint = logic_fn
                    .param_sorts()
                    .get(i)
                    .and_then(|s| s.as_ref())
                    .is_some_and(|sort| {
                        matches!(sort, ExprSort::Datatype(id) if {
                            let name = trust_wp_core::formula::resolve_sort_name(*id);
                            let bare = name.rsplit("::").next().unwrap_or(&name);
                            super::super::sort_context::sort_mapping::is_int_model_type(bare)
                        })
                    });
                if resolved == Sort::Int
                    && inferred_seq_params.contains(param_name)
                    && !has_explicit_int_hint
                {
                    self.sort_from_param_sort(ExprSort::Seq)
                } else {
                    resolved
                }
            })
            .collect();
        for (name, old_sort) in old_param_var_sorts {
            self.restore_var_sort(&name, old_sort);
        }
        // Reserved native datatype names (OptionInt/ResultIntInt) must not
        // reach ay as opaque `declare_fun` signature sorts — AY 0.4 registers
        // them on sight and rejects the later declare-datatype upgrade,
        // breaking every constructor/selector lookup in the VC. Mirror
        // `normalize_sort`'s variable-path canonicalization. (#2706 residual)
        let param_sorts: Vec<Sort> = param_sorts
            .into_iter()
            .map(|s| self.canonicalize_reserved_uf_sort(s))
            .collect();
        let return_sort = self.canonicalize_reserved_uf_sort(return_sort);
        let func_decl = self
            .solver
            .declare_fun(&smt_name, &param_sorts, return_sort.clone());

        // Propagate declared return sort as a sort hint for dependent functions.
        // When function `g` returns Bool, recording ExprSort::Bool for "logic_g"
        // allows `declare_logic_fn_signature` for function `f` (which calls `g`)
        // to find `g`'s return sort through the sort_hints fallback even if
        // `infer_expr_sort` didn't reach the nested LogicFnCall. (#1965)
        match &return_sort {
            Sort::Bool => {
                self.record_sort_hint_if_absent(smt_name.clone(), ExprSort::Bool);
            }
            s if is_seq_family_sort(s) => {
                self.record_sort_hint_if_absent(smt_name.clone(), ExprSort::Seq);
            }
            Sort::Uninterpreted(n) if n == "FMap" => {
                self.record_sort_hint_if_absent(smt_name.clone(), ExprSort::FMap);
            }
            Sort::Datatype(dt) => {
                self.record_sort_hint_if_absent(
                    smt_name.clone(),
                    ExprSort::Datatype(intern_sort_name(&dt.name)),
                );
            }
            Sort::Uninterpreted(n) => {
                self.record_sort_hint_if_absent(
                    smt_name.clone(),
                    ExprSort::Datatype(intern_sort_name(n)),
                );
            }
            _ => {}
        }

        self.register_logic_func(smt_name, func_decl.clone());
        func_decl
    }
}
