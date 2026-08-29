// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded structural-induction schema emitter for recursive-datatype logic
//! functions.
//!
//! # What this proves
//!
//! For a goal that needs the bounded "every in-range index is defined" fact
//!
//! ```text
//! forall l i. 0 <= i < len(l) ==> is-Some(get(l, i))
//! ```
//!
//! over a list-shaped recursive datatype (`Nil` / `Cons(head, tail)`) with
//! `len : List -> Int` and `get : List x Int -> Option<_>` recursive `#[logic]`
//! functions, the bare loop/function VC cannot discharge it: the defining
//! equations of `len`/`get` are (deliberately) NOT asserted as global
//! quantified axioms for recursive datatype logic fns (they would make
//! satisfiable counterexample queries fail closed), so `get(l, i)` stays a free
//! uninterpreted application and the obligation is `sat` (unprovable).
//!
//! # The schema (CARDINAL SOUNDNESS)
//!
//! The unconditionally-sound elimination rule for the well-founded inductive
//! datatype `List` is
//!
//! ```text
//! ( P(Nil) /\ forall x tl. P(tl) ==> P(Cons(x, tl)) )  ==>  forall l. P(l)
//! ```
//!
//! Instantiated with `P(l) := forall i. 0 <= i < len(l) ==> is-Some(get(l, i))`.
//!
//! Naively asserting the schema as one axiom does NOT help an SMT solver: the
//! nested-quantifier antecedent bodies `P(...)` are not E-matchable triggers, so
//! the conclusion never fires. Instead we DISCHARGE the schema's premises with
//! two isolated sub-proofs and only THEN assert the flattened, E-matchable
//! conclusion into the live solver:
//!
//!   * BASE: prove `P(Nil)` (UNSAT of its negation). `len(Nil) = 0` makes the
//!     `0 <= i < 0` bound unsatisfiable, so the implication is vacuously true.
//!   * STEP: prove `P(tl) ==> P(Cons(x, tl))` for fresh `x, tl` (UNSAT of its
//!     negation, with `P(tl)` asserted as the induction hypothesis). The
//!     defining equations `len(Cons) = 1 + len(tl)` and
//!     `get(Cons, j) = ite(j == 0, Some(head), get(tl, j - 1))` reduce the goal
//!     to either the `Some(head)` head case or the IH at `j - 1`.
//!
//! Both sub-proofs run against a *fresh, isolated* sub-encoder seeded ONLY with
//! the datatype declarations + the `len`/`get` defining equations over the two
//! constructors. The defining equations are GENUINE instances of the registered
//! logic-fn definitions (substituting the constructor terms into the verbatim
//! bodies), so the sub-proofs establish a real theorem. Once `P(Nil)` and the
//! step are both proven, `forall l i. 0 <= i < len(l) ==> is-Some(get(l, i))` is
//! a valid consequence of the datatype's induction principle, so asserting it in
//! the live solver is SOUND — it can only ever add a true fact, never
//! manufacture a spurious UNSAT.
//!
//! The bound `0 <= i < len(l)` is load-bearing: the UNBOUNDED
//! `forall l i. is-Some(get(l, i))` is FALSE (`get(Nil, 0) = None`), so it is
//! NEVER emitted — and the base/step sub-proofs would fail for it anyway
//! (`P(Nil)` would require `is-Some(get(Nil, 0))`, which is `is-Some(None)`).

use ay_dpll::api::{DatatypeSort, SolveResult, Sort, Term};
use trust_wp_core::{
    formula::{BinOp, MatchArm, Pattern, PureExpr},
    logic::{LogicFnDef, LogicMode},
};

use crate::encoder::AYEncoder;

/// A list-shaped recursive datatype recognised for structural induction: a
/// nullary `Nil`-like constructor and a `Cons`-like constructor with a head
/// field and exactly one recursively-typed tail field.
struct ListShape {
    datatype: DatatypeSort,
    /// Name of the nullary base constructor (e.g. `Nil`).
    nil_ctor: String,
    /// Name of the cons constructor (e.g. `Cons`).
    cons_ctor: String,
    /// SMT selector name of the recursive tail field of the cons constructor.
    cons_tail_selector: String,
    /// SMT selector name of the head field of the cons constructor.
    cons_head_selector: String,
    /// Sort of the head field.
    head_sort: Sort,
}

/// The detected target: the `len`/`get` recursive logic fns over a list shape,
/// plus the Option-payload datatype `get` returns.
struct InductionTarget {
    shape: ListShape,
    len_smt: String,
    get_smt: String,
    /// The Option<_> datatype that `get` returns (must have Some/None).
    option: DatatypeSort,
}

impl AYEncoder {
    /// Detect and emit the bounded structural-induction conclusion
    /// `forall l i. 0 <= i < len(l) ==> is-Some(get(l, i))` for the registered
    /// `len`/`get` recursive logic fns, when (and only when) the obligation
    /// `goal_exprs` actually reference `get(.., ..)` over a list shape AND the
    /// base/step sub-proofs both succeed.
    ///
    /// Returns `true` iff the conclusion was emitted (both sub-proofs passed).
    /// Inert (returns `false`, asserts nothing) when the shape/pattern is not
    /// recognised or either sub-proof fails — never a false-UNSAT.
    pub(crate) fn emit_bounded_get_some_structural_induction(
        &mut self,
        goal_exprs: &[PureExpr],
        logic_fns: Option<&[LogicFnDef]>,
        _mode_overrides: Option<&[LogicMode]>,
    ) -> bool {
        let Some(logic_fns) = logic_fns else {
            return false;
        };
        // Only attempt when the goal actually contains a get(..) application
        // (the fact is otherwise inert; this also keeps the sub-proof off the
        // hot path for unrelated obligations).
        let Some(target) = self.detect_induction_target(goal_exprs, logic_fns) else {
            return false;
        };

        // Discharge base + step in an isolated sub-encoder.
        if !self.structural_induction_subproofs_pass(&target) {
            return false;
        }

        // Both premises proven — assert the flattened, E-matchable conclusion
        // into the live solver. SOUND: it is a genuine theorem (validated by the
        // two sub-proofs) about the well-founded datatype.
        self.assert_flattened_get_some_conclusion(&target);

        // The bounded `is-Some(get(l,i))` fact only closes a `get(l,i) == Some(c)`
        // goal once it is bridged to the Option payload. Emit the two
        // payload-reconstruction lemmas (keyed on `get(l,i)`):
        //   L2: is-Some(get(l,i)) ==> get(l,i) == Some(option_some_value(get(l,i)))
        //   L3: is-Some(get(l,i)) ==>
        //          tuple_get_0_placeholder(get(l,i)) == option_some_value(get(l,i))
        // Both are GENUINE consequences of the native Option datatype semantics
        // (L2 is its very reconstruction; L3 equates the generic positional `.0`
        // placeholder with the native `Some`-payload selector — the same value on
        // the `Some` branch). Guarded by `is-Some`, so vacuously true on `None`;
        // SOUND — they only add true facts, never a spurious UNSAT.
        self.assert_get_option_payload_lemmas(&target);
        true
    }

    /// Prove the ABSTRACT cons-step lemma for the all-zero property
    /// ```text
    /// forall x tl. ( x == 0
    ///              /\ forall j. 0 <= j < len(tl) ==> get(tl, j) == Some(0) )
    ///          ==> forall i. 0 <= i < len(Cons(x, tl)) ==> get(Cons(x, tl), i) == Some(0)
    /// ```
    /// in an isolated sub-encoder (UNSAT of its negation). Returns `true` iff the
    /// lemma is a genuine theorem of the `len`/`get` definitions. Asserts NOTHING
    /// into `self` — a pure sub-encoder check.
    ///
    /// Used by loop preservation to discharge the universal-preservation lemma
    /// `P(^loop_l)` for a cons-tail prophecy loop (`while let Cons(v,n)=l {*v=0; l=n}`):
    /// the main VC has all the pieces (`^loop_l==Cons(^value,^loop_l_prime)`,
    /// `^value==0`, the layer-5 `get` unfoldings, and the IH `P(^loop_l_prime)`) and
    /// `P` instantiates at the decremented index, but ay's DPLL(T) cannot combine
    /// them into a conflict within its per-obligation budget. The isolated proof
    /// (tiny search space, top-level skolemized negation) converges in <1s.
    ///
    /// SOUNDNESS: this lemma is UNCONDITIONALLY valid, so a `true` return does NOT
    /// by itself justify asserting `P(^loop_l)` — the CALLER must independently gate
    /// on the concrete antecedents (`^loop_l==Cons(^value,^loop_l_prime)`,
    /// `^value==0`, `P(^loop_l_prime)`) being present in the main VC, which makes the
    /// injected `P(^loop_l)` a genuine consequence of the main context. (#994)
    pub(crate) fn all_zero_cons_step_lemma_holds(
        &mut self,
        goal_exprs: &[PureExpr],
        logic_fns: Option<&[LogicFnDef]>,
    ) -> bool {
        let Some(logic_fns) = logic_fns else {
            return false;
        };
        let Some(target) = self.detect_induction_target(goal_exprs, logic_fns) else {
            return false;
        };
        // `x == 0` needs an Int head; `Some(0)` needs an Int Option payload.
        if target.shape.head_sort != Sort::Int {
            return false;
        }
        let some_field_int = target
            .option
            .constructors
            .iter()
            .find(|c| c.name == "Some")
            .and_then(|c| c.fields.first())
            .is_some_and(|f| f.sort == Sort::Int);
        if !some_field_int {
            return false;
        }
        self.subproof_all_zero_step_holds(&target)
    }

    /// Discharge the step `(x==0 /\ P(tl)) ==> P(Cons(x,tl))` for fresh `x, tl`
    /// with `P(l) = forall i. 0<=i<len(l) ==> get(l,i)==Some(0)`. Two-edit clone of
    /// [`subproof_step_holds`]: adds the head hypothesis `x==0` and swaps the
    /// `is-Some(..)` predicate for `.. == Some(0)`. Returns `true` iff UNSAT.
    fn subproof_all_zero_step_holds(&self, target: &InductionTarget) -> bool {
        let Some(mut e) = self.seed_subencoder(target) else {
            return false;
        };
        let shape = &target.shape;
        let option = &target.option;
        let list_sort = Sort::Datatype(shape.datatype.clone());
        let Some(len_decl) = e.logic_func_decl_cloned(&target.len_smt) else {
            return false;
        };
        let Some(get_decl) = e.logic_func_decl_cloned(&target.get_smt) else {
            return false;
        };

        let x = e.solver.fresh_var("azl_x", shape.head_sort.clone());
        let tl = e.solver.fresh_var("azl_tl", list_sort);

        // Head hypothesis: x == 0.
        let z = e.solver.int_const(0);
        let heq = e.eq_term(x, z);
        e.solver.assert_term(heq);

        // IH: forall j. 0<=j<len(tl) ==> get(tl,j) == Some(0).
        let j = e.solver.fresh_var("azl_j", Sort::Int);
        let z0 = e.solver.int_const(0);
        let lo = e.solver.le(z0, j);
        let len_tl = e.solver.apply(&len_decl, &[tl]);
        let hi = e.solver.lt(j, len_tl);
        let bound = e.solver.and(lo, hi);
        let g_tl = e.solver.apply(&get_decl, &[tl, j]);
        let some0_c = e.solver.int_const(0);
        let some0 = e.solver.datatype_constructor(option, "Some", &[some0_c]);
        let ih_eq = e.eq_term(g_tl, some0);
        let ih_body = e.solver.implies(bound, ih_eq);
        let ih = e.solver.forall_with_triggers(&[j], ih_body, &[&[g_tl]]);
        e.solver.assert_term(ih);

        // Negated P(Cons(x,tl)): 0 <= sk < len(Cons) && get(Cons,sk) != Some(0).
        let Some(cons) = self.construct_cons(&mut e, shape, x, tl) else {
            return false;
        };
        let sk = e.solver.fresh_var("azl_sk", Sort::Int);
        let z1 = e.solver.int_const(0);
        let lo2 = e.solver.le(z1, sk);
        e.solver.assert_term(lo2);
        let len_cons = e.solver.apply(&len_decl, &[cons]);
        let hi2 = e.solver.lt(sk, len_cons);
        e.solver.assert_term(hi2);
        let Some(cons2) = self.construct_cons(&mut e, shape, x, tl) else {
            return false;
        };
        let g = e.solver.apply(&get_decl, &[cons2, sk]);
        let some0g_c = e.solver.int_const(0);
        let some0g = e.solver.datatype_constructor(option, "Some", &[some0g_c]);
        let eqg = e.eq_term(g, some0g);
        let neg = e.solver.not(eqg);
        e.solver.assert_term(neg);

        matches!(e.check_sat(), SolveResult::Unsat(_))
    }

    /// Prove the ABSTRACT len-preservation cons-step lemma
    /// ```text
    /// forall xp xc tlp tlc. len(tlp) == len(tlc)
    ///                   ==> len(Cons(xp, tlp)) == len(Cons(xc, tlc))
    /// ```
    /// in an isolated sub-encoder. Returns `true` iff UNSAT (a genuine theorem of
    /// `len(Cons(_,t)) == 1 + len(t)`). Asserts NOTHING into `self`.
    ///
    /// Used by loop preservation to discharge the LEN-preservation conditional
    /// `len(^loop_l)==len(loop_l) => len(^old_l)==len(old_l)` of a cons-tail
    /// prophecy loop: with `^loop_l==Cons(_,^loop_l_prime)` (G2) and the current
    /// cons structure, `len(^loop_l)==len(loop_l)` follows from the IH
    /// `len(^loop_l_prime)==len(loop_l_prime)`, so the assumed invariant discharges
    /// the consequent. SOUNDNESS: unconditionally valid; the CALLER gates on the
    /// cons-tail shape + G2 (see `cons_tail_len_preservation_gate`).
    pub(crate) fn all_zero_len_preservation_lemma_holds(
        &mut self,
        goal_exprs: &[PureExpr],
        logic_fns: Option<&[LogicFnDef]>,
    ) -> bool {
        let Some(logic_fns) = logic_fns else {
            return false;
        };
        let Some(target) = self.detect_induction_target(goal_exprs, logic_fns) else {
            return false;
        };
        self.subproof_len_preservation_step_holds(&target)
    }

    /// Discharge `(len(tlp)==len(tlc)) => (len(Cons(xp,tlp))==len(Cons(xc,tlc)))`
    /// for fresh `xp, xc, tlp, tlc`. Returns `true` iff UNSAT.
    fn subproof_len_preservation_step_holds(&self, target: &InductionTarget) -> bool {
        let Some(mut e) = self.seed_subencoder(target) else {
            return false;
        };
        let shape = &target.shape;
        let list_sort = Sort::Datatype(shape.datatype.clone());
        let Some(len_decl) = e.logic_func_decl_cloned(&target.len_smt) else {
            return false;
        };

        let xp = e.solver.fresh_var("lp_xp", shape.head_sort.clone());
        let xc = e.solver.fresh_var("lp_xc", shape.head_sort.clone());
        let tlp = e.solver.fresh_var("lp_tlp", list_sort.clone());
        let tlc = e.solver.fresh_var("lp_tlc", list_sort);

        // IH: len(tlp) == len(tlc).
        let len_tlp = e.solver.apply(&len_decl, &[tlp]);
        let len_tlc = e.solver.apply(&len_decl, &[tlc]);
        let ih = e.eq_term(len_tlp, len_tlc);
        e.solver.assert_term(ih);

        // Negated goal: len(Cons(xp,tlp)) != len(Cons(xc,tlc)).
        let Some(cons_p) = self.construct_cons(&mut e, shape, xp, tlp) else {
            return false;
        };
        let Some(cons_c) = self.construct_cons(&mut e, shape, xc, tlc) else {
            return false;
        };
        let len_cp = e.solver.apply(&len_decl, &[cons_p]);
        let len_cc = e.solver.apply(&len_decl, &[cons_c]);
        let eq = e.eq_term(len_cp, len_cc);
        let neg = e.solver.not(eq);
        e.solver.assert_term(neg);

        matches!(e.check_sat(), SolveResult::Unsat(_))
    }

    /// Emit L2 (Option reconstruction) and L3 (positional `.0` placeholder ↔
    /// native `Some`-payload bridge) as quantified lemmas keyed on `get(l, i)`.
    fn assert_get_option_payload_lemmas(&mut self, target: &InductionTarget) {
        let shape = &target.shape;
        let option = &target.option;
        let list_sort = Sort::Datatype(shape.datatype.clone());
        let Some(get_decl) = self.logic_func_decl_cloned(&target.get_smt) else {
            return;
        };
        // Only emit when the Option payload selector is Int (the placeholder's
        // return sort); higher-arity or non-Int payloads have no `.0` placeholder
        // counterpart.
        let some_field_int = option
            .constructors
            .iter()
            .find(|c| c.name == "Some")
            .and_then(|c| c.fields.first())
            .is_some_and(|f| f.sort == Sort::Int);
        if !some_field_int {
            return;
        }

        // forall l i. body, with g := get(l, i) as the trigger.
        let l = self.solver.fresh_var("si_payload_l", list_sort);
        let i = self.solver.fresh_var("si_payload_i", Sort::Int);
        let g = self.solver.apply(&get_decl, &[l, i]);
        let Ok(is_some) = self.solver.try_datatype_tester("Some", g) else {
            return;
        };
        let Ok(osv) = self
            .solver
            .try_datatype_selector("option_some_value", g, Sort::Int)
        else {
            return;
        };

        // L2: is-Some(g) ==> g == Some(osv).
        let some_osv = self.solver.datatype_constructor(option, "Some", &[osv]);
        let recon = self.eq_term(g, some_osv);
        let l2_body = self.solver.implies(is_some, recon);
        let l2 = self.solver.forall_with_triggers(&[l, i], l2_body, &[&[g]]);
        self.assert_solver_term("bounded_get_option_reconstruction", l2);

        // L3: is-Some(g) ==> tuple_get_0_placeholder(g) == osv.
        // Build the placeholder application through the registered placeholder
        // path so the SMT symbol matches the one created on the goal's `.0`
        // access. The bridge is only sound for the positional `.0` accessor over
        // an Option receiver, which is exactly this `get(l,i)` term.
        let placeholder_name =
            trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
        if let Ok(tuple_get_0) = self.apply_logic_fn(&placeholder_name, &[g], None, None) {
            if self.solver.get_sort(tuple_get_0) == Sort::Int {
                // Re-derive is-Some / osv on `g` (the apply above may have moved
                // E-graph state; the terms are structurally identical).
                if let (Ok(is_some2), Ok(osv2)) = (
                    self.solver.try_datatype_tester("Some", g),
                    self.solver
                        .try_datatype_selector("option_some_value", g, Sort::Int),
                ) {
                    let bridge_eq = self.eq_term(tuple_get_0, osv2);
                    let l3_body = self.solver.implies(is_some2, bridge_eq);
                    let l3 = self.solver.forall_with_triggers(&[l, i], l3_body, &[&[g]]);
                    self.assert_solver_term("bounded_get_tuple0_option_bridge", l3);
                }
            }
        }
    }

    /// Recognise the `len`/`get` recursive logic fns + list shape + Option
    /// payload, but only if some `goal_expr` references `get(.., ..)`.
    fn detect_induction_target(
        &mut self,
        goal_exprs: &[PureExpr],
        logic_fns: &[LogicFnDef],
    ) -> Option<InductionTarget> {
        // Find a recursive single-datatype-param `get`-like fn whose body is a
        // match returning Some(..)/get(..)/None over the index, and a recursive
        // single-datatype-param `len`-like fn over the SAME datatype.
        let get_fn = logic_fns.iter().find(|lf| {
            lf.is_recursive()
                && !lf.is_opaque()
                && lf.params().len() == 2
                && body_matches_canonical_get(lf.body(), lf.name(), lf.params())
        })?;
        let get_smt = trust_wp_core::logic::logic_fn_smt_name(get_fn.name());

        // The goal must reference get(.., ..) — otherwise the fact is inert and
        // we skip the sub-proof cost.
        if !goal_exprs
            .iter()
            .any(|e| expr_references_logic_call(e, get_fn.name(), &get_smt))
        {
            return None;
        }

        let len_fn = logic_fns.iter().find(|lf| {
            lf.is_recursive()
                && !lf.is_opaque()
                && lf.params().len() == 1
                && body_matches_canonical_len(lf.body(), lf.name(), lf.params())
        })?;
        let len_smt = trust_wp_core::logic::logic_fn_smt_name(len_fn.name());

        // Recover the list shape from the get-fn's declared datatype param.
        let get_decl = self.logic_func_decl_cloned(&get_smt)?;
        let list_sort = get_decl.domain().first()?.clone();
        let shape = self.list_shape_from_sort(&list_sort)?;

        // Recover the Option payload datatype from get's range.
        let opt_sort = get_decl.range().clone();
        let option = self.option_datatype_from_sort(&opt_sort)?;

        // The len-fn must operate over the SAME list datatype.
        let len_decl = self.logic_func_decl_cloned(&len_smt)?;
        let len_dom = len_decl.domain().first()?;
        if !sorts_name_eq(len_dom, &list_sort) {
            return None;
        }

        Some(InductionTarget {
            shape,
            len_smt,
            get_smt,
            option,
        })
    }

    /// Resolve a `Sort` to a `ListShape` (Nil-like nullary ctor + Cons-like ctor
    /// with one recursively-typed tail field and a head field).
    fn list_shape_from_sort(&self, sort: &Sort) -> Option<ListShape> {
        let dt = match sort {
            Sort::Datatype(dt) => dt.clone(),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned()?,
            _ => return None,
        };
        if dt.constructors.len() != 2 {
            return None;
        }
        // Nullary base constructor.
        let nil = dt.constructors.iter().find(|c| c.fields.is_empty())?;
        // Cons constructor: exactly one recursive (same-datatype) field + others.
        let cons = dt.constructors.iter().find(|c| !c.fields.is_empty())?;
        // Identify the recursive tail field (sort names back to this datatype)
        // and require exactly one head field (the classic List(head, tail)).
        if cons.fields.len() != 2 {
            return None;
        }
        let tail_field = cons
            .fields
            .iter()
            .find(|f| sort_names_datatype(&f.sort, &dt.name))?;
        let head_field = cons
            .fields
            .iter()
            .find(|f| !sort_names_datatype(&f.sort, &dt.name))?;
        Some(ListShape {
            nil_ctor: nil.name.clone(),
            cons_ctor: cons.name.clone(),
            cons_tail_selector: tail_field.name.clone(),
            cons_head_selector: head_field.name.clone(),
            head_sort: head_field.sort.clone(),
            datatype: dt,
        })
    }

    /// Resolve a `Sort` to an Option-shaped datatype (Some(payload) / None).
    fn option_datatype_from_sort(&self, sort: &Sort) -> Option<DatatypeSort> {
        let dt = match sort {
            Sort::Datatype(dt) => dt.clone(),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned()?,
            _ => return None,
        };
        let has_some = dt.constructors.iter().any(|c| c.name == "Some");
        let has_none = dt.constructors.iter().any(|c| c.name == "None");
        (has_some && has_none).then_some(dt)
    }

    /// Run the base (`P(Nil)`) and step (`P(tl) ==> P(Cons(x,tl))`) sub-proofs in
    /// an isolated sub-encoder. Returns `true` iff BOTH are UNSAT (proven).
    fn structural_induction_subproofs_pass(&self, target: &InductionTarget) -> bool {
        self.subproof_base_holds(target) && self.subproof_step_holds(target)
    }

    /// Build a fresh sub-encoder seeded with the datatypes + len/get defining
    /// equations over Nil and Cons(head, tail).
    fn seed_subencoder(&self, target: &InductionTarget) -> Option<AYEncoder> {
        let mut e = AYEncoder::try_new_pure_with_quantifiers().ok()?;
        let list = &target.shape.datatype;
        let option = &target.option;
        e.ensure_datatype_declared(list);
        e.ensure_datatype_declared(option);
        let list_sort = Sort::Datatype(list.clone());
        let opt_sort = Sort::Datatype(option.clone());
        e.get_or_declare_logic_func(&target.len_smt, &[list_sort.clone()], Sort::Int);
        e.get_or_declare_logic_func(&target.get_smt, &[list_sort.clone(), Sort::Int], opt_sort);
        self.seed_defining_equations(&mut e, target)?;
        Some(e)
    }

    /// Emit the genuine defining equations of `len`/`get` for Nil and Cons.
    ///
    /// These mirror the registered recursive logic-fn definitions:
    ///   len(Nil)            = 0
    ///   len(Cons(x, tl))    = 1 + len(tl)
    ///   get(Nil, i)         = None
    ///   get(Cons(x, tl), i) = ite(i == 0, Some(x), get(tl, i - 1))
    /// They are TRUE instances of the definitions, so seeding them is sound.
    fn seed_defining_equations(&self, e: &mut AYEncoder, target: &InductionTarget) -> Option<()> {
        let shape = &target.shape;
        let option = &target.option;
        let list_sort = Sort::Datatype(shape.datatype.clone());

        let len_decl = e.logic_func_decl_cloned(&target.len_smt)?;
        let get_decl = e.logic_func_decl_cloned(&target.get_smt)?;

        // --- len(Nil) = 0 ---
        let nil = e
            .solver
            .datatype_constructor(&shape.datatype, &shape.nil_ctor, &[]);
        let len_nil = e.solver.apply(&len_decl, &[nil]);
        let zero = e.solver.int_const(0);
        let eq = e.eq_term(len_nil, zero);
        e.solver.assert_term(eq);

        // --- get(Nil, i) = None  (forall i) ---
        let i = e.solver.fresh_var("si_i", Sort::Int);
        let nil = e
            .solver
            .datatype_constructor(&shape.datatype, &shape.nil_ctor, &[]);
        let get_nil = e.solver.apply(&get_decl, &[nil, i]);
        let none = e.solver.datatype_constructor(option, "None", &[]);
        let eq = e.eq_term(get_nil, none);
        let ax = e.solver.forall_with_triggers(&[i], eq, &[&[get_nil]]);
        e.solver.assert_term(ax);

        // --- len(Cons(x, tl)) = 1 + len(tl) ---
        let x = e.solver.fresh_var("si_x", shape.head_sort.clone());
        let tl = e.solver.fresh_var("si_tl", list_sort.clone());
        let cons = self.construct_cons(e, shape, x, tl)?;
        let len_cons = e.solver.apply(&len_decl, &[cons]);
        let len_tl = e.solver.apply(&len_decl, &[tl]);
        let one = e.solver.int_const(1);
        let one_plus = e.solver.add(one, len_tl);
        let eq = e.eq_term(len_cons, one_plus);
        let ax = e.solver.forall_with_triggers(&[x, tl], eq, &[&[len_cons]]);
        e.solver.assert_term(ax);

        // --- get(Cons(x, tl), j) = ite(j == 0, Some(x), get(tl, j - 1)) ---
        let x = e.solver.fresh_var("si_x2", shape.head_sort.clone());
        let tl = e.solver.fresh_var("si_tl2", list_sort.clone());
        let j = e.solver.fresh_var("si_j", Sort::Int);
        let cons = self.construct_cons(e, shape, x, tl)?;
        let get_cons = e.solver.apply(&get_decl, &[cons, j]);
        let zero = e.solver.int_const(0);
        let j_eq_0 = e.solver.eq(j, zero);
        let some_x = e.solver.datatype_constructor(option, "Some", &[x]);
        let one = e.solver.int_const(1);
        let j_minus_1 = e.solver.sub(j, one);
        let get_tl = e.solver.apply(&get_decl, &[tl, j_minus_1]);
        let ite = e.solver.ite(j_eq_0, some_x, get_tl);
        let eq = e.eq_term(get_cons, ite);
        let ax = e
            .solver
            .forall_with_triggers(&[x, tl, j], eq, &[&[get_cons]]);
        e.solver.assert_term(ax);

        Some(())
    }

    /// Build `Cons(head, tail)` respecting the constructor's field order (head
    /// field then tail field, or vice versa) so the term is well-sorted.
    fn construct_cons(
        &self,
        e: &mut AYEncoder,
        shape: &ListShape,
        head: Term,
        tail: Term,
    ) -> Option<Term> {
        let cons = shape
            .datatype
            .constructors
            .iter()
            .find(|c| c.name == shape.cons_ctor)?;
        let mut args = Vec::with_capacity(cons.fields.len());
        for f in &cons.fields {
            if f.name == shape.cons_head_selector {
                args.push(head);
            } else if f.name == shape.cons_tail_selector {
                args.push(tail);
            } else {
                return None;
            }
        }
        Some(
            e.solver
                .datatype_constructor(&shape.datatype, &shape.cons_ctor, &args),
        )
    }

    /// Prove `P(Nil)`: UNSAT of `exists i. 0<=i<len(Nil) && !is-Some(get(Nil,i))`.
    fn subproof_base_holds(&self, target: &InductionTarget) -> bool {
        let Some(mut e) = self.seed_subencoder(target) else {
            return false;
        };
        let shape = &target.shape;
        let nil = e
            .solver
            .datatype_constructor(&shape.datatype, &shape.nil_ctor, &[]);
        let Some(len_decl) = e.logic_func_decl_cloned(&target.len_smt) else {
            return false;
        };
        let Some(get_decl) = e.logic_func_decl_cloned(&target.get_smt) else {
            return false;
        };
        let sk = e.solver.fresh_var("base_sk", Sort::Int);
        let zero = e.solver.int_const(0);
        let lo = e.solver.le(zero, sk);
        e.solver.assert_term(lo);
        let len_nil = e.solver.apply(&len_decl, &[nil]);
        let hi = e.solver.lt(sk, len_nil);
        e.solver.assert_term(hi);
        let nil = e
            .solver
            .datatype_constructor(&shape.datatype, &shape.nil_ctor, &[]);
        let g = e.solver.apply(&get_decl, &[nil, sk]);
        let Ok(is_some) = e.solver.try_datatype_tester("Some", g) else {
            return false;
        };
        let neg = e.solver.not(is_some);
        e.solver.assert_term(neg);
        matches!(e.check_sat(), SolveResult::Unsat(_))
    }

    /// Prove the step `P(tl) ==> P(Cons(x, tl))`: assert the IH `P(tl)` and the
    /// negated `P(Cons(x, tl))`, expect UNSAT.
    fn subproof_step_holds(&self, target: &InductionTarget) -> bool {
        let Some(mut e) = self.seed_subencoder(target) else {
            return false;
        };
        let shape = &target.shape;
        let list_sort = Sort::Datatype(shape.datatype.clone());
        let Some(len_decl) = e.logic_func_decl_cloned(&target.len_smt) else {
            return false;
        };
        let Some(get_decl) = e.logic_func_decl_cloned(&target.get_smt) else {
            return false;
        };

        let x = e.solver.fresh_var("step_x", shape.head_sort.clone());
        let tl = e.solver.fresh_var("step_tl", list_sort);

        // IH: forall i. 0<=i<len(tl) ==> is-Some(get(tl,i)).
        let ih_i = e.solver.fresh_var("ih_i", Sort::Int);
        let zero = e.solver.int_const(0);
        let lo = e.solver.le(zero, ih_i);
        let len_tl = e.solver.apply(&len_decl, &[tl]);
        let hi = e.solver.lt(ih_i, len_tl);
        let bound = e.solver.and(lo, hi);
        let g_tl = e.solver.apply(&get_decl, &[tl, ih_i]);
        let Ok(is_some_tl) = e.solver.try_datatype_tester("Some", g_tl) else {
            return false;
        };
        let ih_body = e.solver.implies(bound, is_some_tl);
        let ih = e.solver.forall_with_triggers(&[ih_i], ih_body, &[&[g_tl]]);
        e.solver.assert_term(ih);

        // Negated P(Cons(x, tl)): 0<=k<len(Cons) && !is-Some(get(Cons,k)).
        let Some(cons) = self.construct_cons(&mut e, shape, x, tl) else {
            return false;
        };
        let sk = e.solver.fresh_var("step_sk", Sort::Int);
        let zero = e.solver.int_const(0);
        let lo = e.solver.le(zero, sk);
        e.solver.assert_term(lo);
        let len_cons = e.solver.apply(&len_decl, &[cons]);
        let hi = e.solver.lt(sk, len_cons);
        e.solver.assert_term(hi);
        let Some(cons2) = self.construct_cons(&mut e, shape, x, tl) else {
            return false;
        };
        let g = e.solver.apply(&get_decl, &[cons2, sk]);
        let Ok(is_some) = e.solver.try_datatype_tester("Some", g) else {
            return false;
        };
        let neg = e.solver.not(is_some);
        e.solver.assert_term(neg);
        matches!(e.check_sat(), SolveResult::Unsat(_))
    }

    /// Assert the flattened conclusion
    /// `forall l i. 0<=i<len(l) ==> is-Some(get(l,i))` triggered on `get(l,i)`.
    fn assert_flattened_get_some_conclusion(&mut self, target: &InductionTarget) {
        let shape = &target.shape;
        let list_sort = Sort::Datatype(shape.datatype.clone());
        let Some(len_decl) = self.logic_func_decl_cloned(&target.len_smt) else {
            return;
        };
        let Some(get_decl) = self.logic_func_decl_cloned(&target.get_smt) else {
            return;
        };
        let l = self.solver.fresh_var("si_concl_l", list_sort);
        let i = self.solver.fresh_var("si_concl_i", Sort::Int);
        let zero = self.solver.int_const(0);
        let lo = self.solver.le(zero, i);
        let len_l = self.solver.apply(&len_decl, &[l]);
        let hi = self.solver.lt(i, len_l);
        let bound = self.solver.and(lo, hi);
        let g = self.solver.apply(&get_decl, &[l, i]);
        let Ok(is_some) = self.solver.try_datatype_tester("Some", g) else {
            return;
        };
        let body = self.solver.implies(bound, is_some);
        let ax = self.solver.forall_with_triggers(&[l, i], body, &[&[g]]);
        self.assert_solver_term("bounded_get_some_structural_induction", ax);
    }
}

/// Sort names back to the named recursive datatype (`Datatype(name)` or the
/// `Uninterpreted(name)` carrier form).
fn sort_names_datatype(sort: &Sort, name: &str) -> bool {
    match sort {
        Sort::Datatype(dt) => dt.name == name,
        Sort::Uninterpreted(n) => n == name,
        _ => false,
    }
}

fn sorts_name_eq(a: &Sort, b: &Sort) -> bool {
    fn sort_name(s: &Sort) -> Option<&str> {
        match s {
            Sort::Datatype(dt) => Some(dt.name.as_str()),
            Sort::Uninterpreted(n) => Some(n.as_str()),
            _ => None,
        }
    }
    sort_name(a) == sort_name(b)
}

/// Whether `expr` references a logic-fn call by either its rust name or SMT name.
fn expr_references_logic_call(expr: &PureExpr, rust_name: &str, smt_name: &str) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| match node {
        PureExpr::LogicFnCall { name, .. } => {
            let smt = trust_wp_core::logic::logic_fn_smt_name(name);
            if name == rust_name || smt == smt_name {
                found = true;
            }
        }
        PureExpr::MethodCall { method, .. } if method == rust_name => {
            found = true;
        }
        _ => {}
    });
    found
}

/// CARDINAL SOUNDNESS: the emitter seeds its sub-encoder with the EXACT
/// defining equations
///   len(Nil) = 0,  len(Cons(x, tl)) = 1 + len(tl)
/// so it must only fire for a `len` whose body computes precisely that. This
/// verifies the canonical shape
///   match self { Cons(_, tl) => 1 + tl.len(), Nil => 0 }
/// (recursive call by either method `recv.len()` or `len(recv)` form), binding
/// the tail to the recursive call's receiver/argument. Any deviation (e.g. a
/// `2 + ...`, a subtraction, or a different recursion site) is rejected, so the
/// hardcoded defining equation can never misrepresent the real definition.
fn body_matches_canonical_len(body: &PureExpr, fn_name: &str, params: &[String]) -> bool {
    let PureExpr::Match { scrutinee, arms } = strip_wrappers(body) else {
        return false;
    };
    if !scrutinee_is_param(scrutinee, params) || arms.len() != 2 {
        return false;
    }
    let mut zero_arm = false;
    let mut cons_arm = false;
    for arm in arms {
        if is_nullary_base_arm(arm) {
            zero_arm = matches!(strip_wrappers(&arm.body), PureExpr::Int(0));
        } else if let Some(tail) = cons_tail_binding(arm) {
            // body must be `1 + <recursion on tail>`.
            cons_arm = match strip_wrappers(&arm.body) {
                PureExpr::BinOp(l, BinOp::Add, r) => {
                    (is_one(l) && is_self_recursion_on(r, fn_name, &tail))
                        || (is_one(r) && is_self_recursion_on(l, fn_name, &tail))
                }
                _ => false,
            };
        } else {
            return false;
        }
    }
    zero_arm && cons_arm
}

/// CARDINAL SOUNDNESS: companion of [`body_matches_canonical_len`] for `get`.
/// Seeds `get(Nil, i) = None` and
///   get(Cons(x, tl), j) = ite(j == 0, Some(x), get(tl, j - 1))
/// so it must only fire for a `get` whose body computes precisely that:
///   match self {
///     Cons(x, tl) => match ix == 0 { true => Some(x), false => get(tl, ix - 1) },
///     Nil => None,
///   }
/// The index parameter (`ix`) is the 2nd param; the head binding feeds `Some(x)`
/// and the tail binding feeds the recursive `get(tl, ix - 1)`. Any deviation is
/// rejected.
fn body_matches_canonical_get(body: &PureExpr, fn_name: &str, params: &[String]) -> bool {
    let PureExpr::Match { scrutinee, arms } = strip_wrappers(body) else {
        return false;
    };
    if !scrutinee_is_param(scrutinee, params) || arms.len() != 2 {
        return false;
    }
    let Some(index_param) = params.get(1) else {
        return false;
    };
    let mut none_arm = false;
    let mut cons_arm = false;
    for arm in arms {
        if is_nullary_base_arm(arm) {
            none_arm = body_is_none(&arm.body);
        } else if let Some((head, tail)) = cons_head_tail_bindings(arm) {
            cons_arm = cons_get_arm_matches(&arm.body, fn_name, &head, &tail, index_param);
        } else {
            return false;
        }
    }
    none_arm && cons_arm
}

/// The cons arm of `get`: `match ix == 0 { true => Some(head), false => get(tail, ix - 1) }`
/// (or the equivalent `ite`). Verifies the `Some(head)` head case and the
/// `get(tail, ix - 1)` recursion exactly.
fn cons_get_arm_matches(
    arm_body: &PureExpr,
    fn_name: &str,
    head: &str,
    tail: &str,
    index_param: &str,
) -> bool {
    let body = strip_wrappers(arm_body);
    // Form 1: nested `match ix == 0 { true => .., false => .. }`.
    if let PureExpr::Match { scrutinee, arms } = body {
        if !is_index_eq_zero(scrutinee, index_param) || arms.len() != 2 {
            return false;
        }
        let mut some_head = false;
        let mut rec = false;
        for a in arms {
            match &a.pattern {
                Pattern::Literal(PureExpr::Bool(true)) => {
                    some_head = is_some_of(&a.body, head);
                }
                Pattern::Literal(PureExpr::Bool(false)) => {
                    rec = is_get_recursion_on_tail(&a.body, fn_name, tail, index_param);
                }
                _ => return false,
            }
        }
        return some_head && rec;
    }
    // Form 2: `ite(ix == 0, Some(head), get(tail, ix - 1))`.
    if let PureExpr::Ite(cond, then_e, else_e) = body {
        return is_index_eq_zero(cond, index_param)
            && is_some_of(then_e, head)
            && is_get_recursion_on_tail(else_e, fn_name, tail, index_param);
    }
    false
}

/// `Some(head)` for the bound head variable.
fn is_some_of(expr: &PureExpr, head: &str) -> bool {
    match strip_wrappers(expr) {
        PureExpr::LogicFnCall { name, args } => {
            name.rsplit("::").next().unwrap_or(name) == "Some"
                && args.len() == 1
                && is_var(&args[0], head)
        }
        _ => false,
    }
}

/// `get(tail, ix - 1)` — recursion on the tail binding with the predecessor
/// index. The recursion site must be the tail binding (structurally smaller),
/// which is what makes the induction well-founded.
fn is_get_recursion_on_tail(expr: &PureExpr, fn_name: &str, tail: &str, index_param: &str) -> bool {
    let (recv, idx) = match strip_wrappers(expr) {
        PureExpr::LogicFnCall { name, args } if name == fn_name && args.len() == 2 => {
            (&args[0], &args[1])
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == fn_name && args.len() == 1 => (receiver.as_ref(), &args[0]),
        _ => return false,
    };
    is_var(strip_wrappers(recv), tail) && is_index_minus_one(idx, index_param)
}

/// `ix - 1` for the index parameter.
fn is_index_minus_one(expr: &PureExpr, index_param: &str) -> bool {
    matches!(
        strip_wrappers(expr),
        PureExpr::BinOp(l, BinOp::Sub, r) if is_var(l, index_param) && is_one(r)
    )
}

/// `ix == 0` (either scrutinee form).
fn is_index_eq_zero(expr: &PureExpr, index_param: &str) -> bool {
    matches!(
        strip_wrappers(expr),
        PureExpr::BinOp(l, BinOp::Eq, r)
            if (is_var(l, index_param) && matches!(strip_wrappers(r), PureExpr::Int(0)))
                || (is_var(r, index_param) && matches!(strip_wrappers(l), PureExpr::Int(0)))
    )
}

/// A self-recursive call `f(tail)` / `tail.f()` on the bound tail variable.
fn is_self_recursion_on(expr: &PureExpr, fn_name: &str, tail: &str) -> bool {
    match strip_wrappers(expr) {
        PureExpr::LogicFnCall { name, args } if name == fn_name && args.len() == 1 => {
            is_var(strip_wrappers(&args[0]), tail)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == fn_name && args.is_empty() => is_var(strip_wrappers(receiver), tail),
        _ => false,
    }
}

fn is_one(expr: &PureExpr) -> bool {
    matches!(strip_wrappers(expr), PureExpr::Int(1))
}

fn is_var(expr: &PureExpr, name: &str) -> bool {
    matches!(strip_wrappers(expr), PureExpr::Var(n, _) if n == name)
}

fn scrutinee_is_param(scrutinee: &PureExpr, params: &[String]) -> bool {
    matches!(strip_wrappers(scrutinee), PureExpr::Var(n, _) if params.first().is_some_and(|p| p == n))
}

/// A nullary base-case arm: `Nil` / `None` constructor with no field bindings.
fn is_nullary_base_arm(arm: &MatchArm) -> bool {
    matches!(
        constructor_name(&arm.pattern).as_deref(),
        Some("Nil") | Some("None")
    ) && !arm_binds_fields(&arm.pattern)
}

/// For a `Cons(_, tl)` arm, return the tail binding name.
fn cons_tail_binding(arm: &MatchArm) -> Option<String> {
    let (_head, tail) = cons_head_tail_bindings(arm)?;
    Some(tail)
}

/// For a `Cons(head, tail)` 2-field arm, return `(head_binding, tail_binding)`.
/// The head may be a wildcard (then a fresh sentinel is unused — only `len`
/// uses the head-less form); `get` requires a real head binding, enforced by
/// [`is_some_of`] downstream.
fn cons_head_tail_bindings(arm: &MatchArm) -> Option<(String, String)> {
    let Pattern::Constructor {
        inner: Some(inner), ..
    } = &arm.pattern
    else {
        return None;
    };
    let Pattern::Tuple(elems) = inner.as_ref() else {
        return None;
    };
    if elems.len() != 2 {
        return None;
    }
    let head = binding_name(&elems[0]).unwrap_or_else(|| "_".to_string());
    let tail = binding_name(&elems[1])?;
    Some((head, tail))
}

fn binding_name(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Binding(n) => Some(n.clone()),
        _ => None,
    }
}

fn strip_wrappers(expr: &PureExpr) -> &PureExpr {
    let mut cur = expr;
    loop {
        match cur {
            PureExpr::Deref(i) | PureExpr::View(i) | PureExpr::Old(i) | PureExpr::Final(i) => {
                cur = i;
            }
            other => return other,
        }
    }
}

fn constructor_name(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Constructor { name, .. } => {
            Some(name.rsplit("::").next().unwrap_or(name).to_string())
        }
        Pattern::Alias { pattern, .. } => constructor_name(pattern),
        _ => None,
    }
}

fn arm_binds_fields(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Constructor { inner: Some(_), .. })
}

/// Whether a match-arm body denotes the `None` Option constructor.
fn body_is_none(body: &PureExpr) -> bool {
    match strip_wrappers(body) {
        PureExpr::LogicFnCall { name, args } => {
            args.is_empty() && name.rsplit("::").next().unwrap_or(name) == "None"
        }
        PureExpr::Var(name, _) => name.rsplit("::").next().unwrap_or(name) == "None",
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{MatchArm, Pattern};

    use super::*;

    fn cons_pat() -> Pattern {
        Pattern::Constructor {
            name: "Cons".to_string(),
            inner: Some(Box::new(Pattern::Tuple(vec![
                Pattern::Binding("x".to_string()),
                Pattern::Binding("tl".to_string()),
            ]))),
        }
    }
    fn nil_pat() -> Pattern {
        Pattern::Constructor {
            name: "Nil".to_string(),
            inner: None,
        }
    }
    fn v(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    /// `match self { Cons(_, tl) => 1 + tl.len(), Nil => 0 }` is canonical len.
    #[test]
    fn canonical_len_accepts_genuine_len() {
        let body = PureExpr::Match {
            scrutinee: Arc::new(v("self")),
            arms: vec![
                MatchArm {
                    pattern: cons_pat(),
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Int(1)),
                        BinOp::Add,
                        Arc::new(PureExpr::MethodCall {
                            receiver: Arc::new(v("tl")),
                            method: "len".to_string(),
                            args: vec![],
                        }),
                    ),
                },
                MatchArm {
                    pattern: nil_pat(),
                    body: PureExpr::Int(0),
                },
            ],
        };
        assert!(body_matches_canonical_len(
            &body,
            "len",
            &["self".to_string()]
        ));
    }

    /// SOUNDNESS GUARD: a `len`-shaped body that returns `2 + tl.len()` (or any
    /// non-canonical arithmetic) must be REJECTED — the emitter seeds
    /// `len(Cons)=1+len(tl)`, which would misrepresent this body.
    #[test]
    fn canonical_len_rejects_wrong_constant() {
        let body = PureExpr::Match {
            scrutinee: Arc::new(v("self")),
            arms: vec![
                MatchArm {
                    pattern: cons_pat(),
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Int(2)),
                        BinOp::Add,
                        Arc::new(PureExpr::MethodCall {
                            receiver: Arc::new(v("tl")),
                            method: "len".to_string(),
                            args: vec![],
                        }),
                    ),
                },
                MatchArm {
                    pattern: nil_pat(),
                    body: PureExpr::Int(0),
                },
            ],
        };
        assert!(!body_matches_canonical_len(
            &body,
            "len",
            &["self".to_string()]
        ));
    }

    /// SOUNDNESS GUARD: a non-zero base case must be REJECTED (would invalidate
    /// the vacuity of `len(Nil)=0`).
    #[test]
    fn canonical_len_rejects_nonzero_base() {
        let body = PureExpr::Match {
            scrutinee: Arc::new(v("self")),
            arms: vec![
                MatchArm {
                    pattern: cons_pat(),
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Int(1)),
                        BinOp::Add,
                        Arc::new(PureExpr::MethodCall {
                            receiver: Arc::new(v("tl")),
                            method: "len".to_string(),
                            args: vec![],
                        }),
                    ),
                },
                MatchArm {
                    pattern: nil_pat(),
                    body: PureExpr::Int(7),
                },
            ],
        };
        assert!(!body_matches_canonical_len(
            &body,
            "len",
            &["self".to_string()]
        ));
    }

    fn canonical_get_body() -> PureExpr {
        PureExpr::Match {
            scrutinee: Arc::new(v("self")),
            arms: vec![
                MatchArm {
                    pattern: cons_pat(),
                    body: PureExpr::Match {
                        scrutinee: Arc::new(PureExpr::BinOp(
                            Arc::new(v("ix")),
                            BinOp::Eq,
                            Arc::new(PureExpr::Int(0)),
                        )),
                        arms: vec![
                            MatchArm {
                                pattern: Pattern::Literal(PureExpr::Bool(true)),
                                body: PureExpr::LogicFnCall {
                                    name: "Some".to_string(),
                                    args: vec![v("x")],
                                },
                            },
                            MatchArm {
                                pattern: Pattern::Literal(PureExpr::Bool(false)),
                                body: PureExpr::LogicFnCall {
                                    name: "get".to_string(),
                                    args: vec![
                                        v("tl"),
                                        PureExpr::BinOp(
                                            Arc::new(v("ix")),
                                            BinOp::Sub,
                                            Arc::new(PureExpr::Int(1)),
                                        ),
                                    ],
                                },
                            },
                        ],
                    },
                },
                MatchArm {
                    pattern: nil_pat(),
                    body: v("None"),
                },
            ],
        }
    }

    #[test]
    fn canonical_get_accepts_genuine_get() {
        assert!(body_matches_canonical_get(
            &canonical_get_body(),
            "get",
            &["self".to_string(), "ix".to_string()]
        ));
    }

    /// SOUNDNESS GUARD: a `get` whose Cons-head case returns `Some(ix)` (wrong
    /// payload, not the head binding) must be REJECTED.
    #[test]
    fn canonical_get_rejects_wrong_head() {
        let PureExpr::Match { scrutinee, arms } = canonical_get_body() else {
            unreachable!()
        };
        let mut arms = arms;
        // Tamper the head case to Some(ix).
        if let PureExpr::Match {
            arms: inner_arms, ..
        } = &mut arms[0].body
        {
            inner_arms[0].body = PureExpr::LogicFnCall {
                name: "Some".to_string(),
                args: vec![v("ix")],
            };
        }
        let body = PureExpr::Match { scrutinee, arms };
        assert!(!body_matches_canonical_get(
            &body,
            "get",
            &["self".to_string(), "ix".to_string()]
        ));
    }

    /// SOUNDNESS GUARD: a `get` whose recursion is on the WRONG index
    /// (`ix + 1` instead of `ix - 1`) must be REJECTED — the seeded equation
    /// `get(Cons,j)=ite(j==0,Some,get(tl,j-1))` would misrepresent it.
    #[test]
    fn canonical_get_rejects_wrong_recursion_index() {
        let PureExpr::Match { scrutinee, arms } = canonical_get_body() else {
            unreachable!()
        };
        let mut arms = arms;
        if let PureExpr::Match {
            arms: inner_arms, ..
        } = &mut arms[0].body
        {
            inner_arms[1].body = PureExpr::LogicFnCall {
                name: "get".to_string(),
                args: vec![
                    v("tl"),
                    PureExpr::BinOp(Arc::new(v("ix")), BinOp::Add, Arc::new(PureExpr::Int(1))),
                ],
            };
        }
        let body = PureExpr::Match { scrutinee, arms };
        assert!(!body_matches_canonical_get(
            &body,
            "get",
            &["self".to_string(), "ix".to_string()]
        ));
    }
}
