// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 query generator.
//!
//! High-level API for building complete SMT verification condition queries.

use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    sync::Arc,
};

use super::{
    context::SmtContext,
    expr_printer::write_expr_ctx,
    formula_printer::write_formula,
    preamble::{generate_bitwise_preamble, generate_seq_preamble, needs_bitwise_preamble_expr},
    sort_inference::{
        collect_applied_symbols, collect_vars_with_sorts, is_formula_shaped, is_seq_var,
        AppliedSymbol,
    },
    sorts::VarSort,
    var_collect::collect_vars_formula,
};
use crate::formula::{BinOp, Formula, PureExpr};

/// A well-definedness side condition lifted out of term position.
struct HoistedSideCondition {
    condition: PureExpr,
    /// `LetObligation` marks something the full encoder *checks*; `LetAssume`
    /// marks something it assumes. The rendered query treats both as
    /// assumptions and says so.
    is_obligation: bool,
}

/// Lift well-definedness side conditions out of *term* position.
///
/// The driver wraps a term like `a / b` in `LetAssume { assumption: b != 0, .. }`
/// so the divisor guard travels with the value. The printer renders that as
/// `(=> assumption body)` — correct where the node stands for a formula, and
/// ill-sorted where it stands for a term: `(=> Bool Int)`, which every solver
/// rejects. Any contract containing a division hit this, so the emitted query
/// was unusable for a large and ordinary class of functions.
///
/// The fix is to put the condition where SMT-LIB can hold it — a top-level
/// assertion — and leave the term itself in place. Only term-position nodes
/// move: a `LetAssume` whose body is a formula still prints as the implication
/// it is, so no well-sorted query changes meaning. Under a negated
/// postcondition the two are equal outright (`¬(g ⇒ P)` is `g ∧ ¬P`); in a term
/// there was no well-sorted meaning to preserve, and assuming the guard is what
/// the full encoder does with it.
fn hoist_term_side_conditions(expr: &PureExpr, out: &mut Vec<HoistedSideCondition>) -> PureExpr {
    // Never cross a binder. A guard sitting inside a `forall` body, a match arm
    // or a `let` may mention names that binder introduces; lifting it to a
    // top-level assertion would leave those names free and undeclared, trading
    // one unparseable query for another. Pruning leaves such a node exactly as
    // it was — still an implication, still what the printer wrote before.
    let crosses_a_binder = |node: &PureExpr| {
        !matches!(
            node,
            PureExpr::Forall { .. }
                | PureExpr::Exists { .. }
                | PureExpr::Match { .. }
                | PureExpr::Let { .. }
                | PureExpr::Closure { .. }
        )
    };
    expr.rewrite_bottom_up_prune(crosses_a_binder, |node| match node {
        PureExpr::LetAssume { assumption, body } if !is_formula_shaped(&body) => {
            out.push(HoistedSideCondition {
                condition: (*assumption).clone(),
                is_obligation: false,
            });
            (*body).clone()
        }
        PureExpr::LetObligation { obligation, body } if !is_formula_shaped(&body) => {
            out.push(HoistedSideCondition {
                condition: (*obligation).clone(),
                is_obligation: true,
            });
            (*body).clone()
        }
        other => other,
    })
}

/// The clause set after well-definedness side conditions have been lifted out
/// of term position.
///
/// It owns the rewritten expressions, so every later phase — sort inference,
/// declarations, applied symbols, the printed body — reads the one shape the
/// query is actually built from.
struct HoistedClauses {
    requires: Vec<PureExpr>,
    ensures: Vec<PureExpr>,
    result: Option<PureExpr>,
    side_conditions: Vec<HoistedSideCondition>,
}

impl HoistedClauses {
    /// Lift the side conditions out of every clause first, so nothing
    /// downstream ever sees the pre-hoist shape.
    fn hoist(requires: &[PureExpr], ensures: &[PureExpr], result_expr: Option<&PureExpr>) -> Self {
        let mut side_conditions: Vec<HoistedSideCondition> = Vec::new();
        let requires: Vec<PureExpr> = requires
            .iter()
            .map(|clause| hoist_term_side_conditions(clause, &mut side_conditions))
            .collect();
        let ensures: Vec<PureExpr> = ensures
            .iter()
            .map(|clause| hoist_term_side_conditions(clause, &mut side_conditions))
            .collect();
        let result = result_expr.map(|expr| hoist_term_side_conditions(expr, &mut side_conditions));
        Self {
            requires,
            ensures,
            result,
            side_conditions,
        }
    }

    /// Every expression the query mentions, in the order the emitter needs
    /// them: requires, ensures, side conditions, result.
    fn all_exprs(&self) -> Vec<&PureExpr> {
        let mut all_exprs: Vec<&PureExpr> = Vec::new();
        all_exprs.extend(self.requires.iter());
        all_exprs.extend(self.ensures.iter());
        for condition in &self.side_conditions {
            all_exprs.push(&condition.condition);
        }
        if let Some(result) = &self.result {
            all_exprs.push(result);
        }
        all_exprs
    }
}

/// Infer the sort of every variable the query will name.
///
/// Collects under the names the printer will actually emit. `infer_var_sorts`
/// returns the *original* names, so a query mentioning `x_view`, `v_current`
/// or `old_n` declared `x`, `v` and `n` instead and the emitted text
/// referenced undeclared symbols — not parseable by any solver.
/// `collect_vars_with_sorts` applies the same RustHorn name transformations as
/// `write_expr_ctx`, which is what makes declarations and uses line up.
fn infer_query_var_sorts(all_exprs: &[&PureExpr]) -> HashMap<String, VarSort> {
    let mut var_sorts: HashMap<String, VarSort> = HashMap::new();
    for expr in all_exprs {
        let sorts = collect_vars_with_sorts(expr);
        for (name, sort) in sorts {
            match var_sorts.entry(name) {
                std::collections::hash_map::Entry::Vacant(slot) => {
                    slot.insert(sort);
                }
                // Int wins a mixed-context tie, matching `insert_var_sort`.
                std::collections::hash_map::Entry::Occupied(mut slot) => {
                    if *slot.get() != VarSort::Int && sort == VarSort::Int {
                        slot.insert(VarSort::Int);
                    }
                }
            }
        }
    }
    // 'result' default depends on ensures - if ensures use it in Bool context, use Bool
    // Otherwise default to Int for arithmetic results.
    // This belongs here, on the finalised map: `result_sort` reads it back when
    // the applied symbols are collected.
    var_sorts
        .entry("result".to_string())
        .or_insert(VarSort::Int);
    var_sorts
}

/// Generates SMT-LIB2 output from formulas
pub struct SmtGenerator {
    output: String,
    declared_vars: HashSet<String>,
}

impl SmtGenerator {
    /// Create a new generator
    #[must_use]
    pub fn new() -> Self {
        Self {
            output: String::new(),
            declared_vars: HashSet::new(),
        }
    }

    /// Get the generated output
    #[must_use]
    pub fn output(&self) -> &str {
        &self.output
    }

    /// Consume the generator and return the output
    #[must_use]
    pub fn into_output(self) -> String {
        self.output
    }

    /// Add a comment
    pub fn comment(&mut self, text: &str) {
        writeln!(self.output, "; {text}").expect("write to String buffer");
    }

    /// Set the logic (default is `QF_LIA` for quantifier-free linear integer arithmetic)
    pub fn set_logic(&mut self, logic: &str) {
        writeln!(self.output, "(set-logic {logic})").expect("write to String buffer");
    }

    /// Declare an integer variable
    pub fn declare_int(&mut self, name: &str) {
        if self.declared_vars.insert(name.to_string()) {
            writeln!(self.output, "(declare-const {name} Int)").expect("write to String buffer");
        }
    }

    /// Declare a boolean variable
    pub fn declare_bool(&mut self, name: &str) {
        if self.declared_vars.insert(name.to_string()) {
            writeln!(self.output, "(declare-const {name} Bool)").expect("write to String buffer");
        }
    }

    /// Declare a variable with inferred sort
    pub fn declare_var(&mut self, name: &str, sort: VarSort) {
        match sort {
            VarSort::Int => self.declare_int(name),
            VarSort::Bool => self.declare_bool(name),
            VarSort::Seq => self.declare_seq(name),
        }
    }

    /// Declare an uninterpreted function.
    ///
    /// A nullary one is still `(declare-fun f () Int)` — SMT-LIB's declaration
    /// grammar takes an (possibly empty) argument list — but it is *applied* as
    /// the bare identifier `f`, which is what `write_expr_ctx` emits.
    pub fn declare_fn(&mut self, name: &str, params: &[VarSort], result: VarSort) {
        if !self.declared_vars.insert(name.to_string()) {
            return;
        }
        let params = params
            .iter()
            .map(|sort| sort.smt_name())
            .collect::<Vec<_>>()
            .join(" ");
        writeln!(
            self.output,
            "(declare-fun {name} ({params}) {})",
            result.smt_name()
        )
        .expect("write to String buffer");
    }

    /// Declare a sequence variable
    pub fn declare_seq(&mut self, name: &str) {
        if self.declared_vars.insert(name.to_string()) {
            writeln!(self.output, "(declare-const {name} Seq)").expect("write to String buffer");
        }
    }

    /// Declare all variables used in an expression with inferred sorts.
    ///
    /// Uses a single AST traversal via [`collect_vars_with_sorts`] to collect
    /// variable names and infer their sorts. View variables (`*_view`) get Seq sort,
    /// variables in boolean contexts get Bool, and arithmetic contexts get Int.
    ///
    /// Performance: O(n) single traversal instead of O(2n) dual traversal (#223).
    pub fn declare_vars_in_expr(&mut self, expr: &PureExpr) {
        let vars_with_sorts = collect_vars_with_sorts(expr);
        for (var, sort) in vars_with_sorts {
            self.declare_var(&var, sort);
        }
    }

    /// Declare all variables used in a formula.
    ///
    /// Variables ending in `_view` are declared as Seq sort (for `Seq<T>` logical views).
    /// All other variables are declared as Int.
    pub fn declare_vars_in_formula(&mut self, formula: &Formula) {
        let vars = collect_vars_formula(formula);
        for var in vars {
            if is_seq_var(&var) {
                self.declare_seq(&var);
            } else {
                self.declare_int(&var);
            }
        }
    }

    /// Assert a formula
    pub fn assert_formula(&mut self, formula: &Formula) {
        self.output.push_str("(assert ");
        write_formula(&mut self.output, formula);
        self.output.push_str(")\n");
    }

    /// Assert an expression (as a pure formula)
    pub fn assert_expr(&mut self, expr: &PureExpr) {
        self.output.push_str("(assert ");
        write_expr_ctx(&mut self.output, expr, SmtContext::Normal);
        self.output.push_str(")\n");
    }

    /// Assert the negation of an expression
    pub fn assert_not_expr(&mut self, expr: &PureExpr) {
        self.output.push_str("(assert (not ");
        write_expr_ctx(&mut self.output, expr, SmtContext::Normal);
        self.output.push_str("))\n");
    }

    /// Add check-sat command
    pub fn check_sat(&mut self) {
        writeln!(self.output, "(check-sat)").expect("write to String buffer");
    }

    /// Add get-model command (for counterexamples)
    pub fn get_model(&mut self) {
        writeln!(self.output, "(get-model)").expect("write to String buffer");
    }

    /// Add exit command
    pub fn exit(&mut self) {
        writeln!(self.output, "(exit)").expect("write to String buffer");
    }

    /// Generate a complete VC query for a function.
    ///
    /// The verification strategy is:
    /// - Assert preconditions
    /// - Assert the assignment result = body
    /// - Assert NOT postcondition
    /// - If unsat, the postcondition holds
    ///
    /// Each phase below emits one block of the query and owns the blank line
    /// that follows it. Two orderings here are load-bearing and must not be
    /// rearranged:
    ///
    /// * `declare_query_vars` runs *before* `collect_query_symbols`, because
    ///   symbol collection skips any name already in `declared_vars`. Flipped,
    ///   a variable that happens to share a name with an applied symbol is
    ///   emitted as `(declare-fun foo (Int) Int)` where `(declare-const foo
    ///   Int)` belonged — a query that parses and asks the wrong question.
    /// * the two preambles sit on opposite sides of sort inference: bitwise is
    ///   decided from the expressions, Seq from the inferred sorts. They are
    ///   deliberately not one method.
    pub fn generate_vc(
        &mut self,
        function_name: &str,
        requires: &[PureExpr],
        ensures: &[PureExpr],
        result_expr: Option<&PureExpr>,
    ) {
        self.comment(&format!("Verification condition for: {function_name}"));
        // Use ALL logic to support both Int and Bool
        self.set_logic("ALL");
        self.output.push('\n');

        let clauses = HoistedClauses::hoist(requires, ensures, result_expr);
        let (requires, ensures, result_expr) = (
            clauses.requires.as_slice(),
            clauses.ensures.as_slice(),
            clauses.result.as_ref(),
        );
        let all_exprs = clauses.all_exprs();

        self.emit_bitwise_preamble_if_needed(&all_exprs);
        let var_sorts = infer_query_var_sorts(&all_exprs);
        self.emit_seq_preamble_if_needed(&var_sorts);
        self.declare_query_vars(&var_sorts);
        let (applied, conflicts) = self.collect_query_symbols(&clauses, &var_sorts);
        self.declare_applied_symbols(&applied, &conflicts);

        self.assert_preconditions(requires);
        self.assert_side_conditions(&clauses.side_conditions);
        self.assert_result_assignment(result_expr);
        self.assert_negated_postconditions(ensures);

        self.check_sat();
        self.comment("unsat = postcondition verified");
        self.comment("sat = potential counterexample (run get-model)");

        self.note_unpinned_symbols(requires, ensures, &clauses.side_conditions, result_expr);
    }

    /// Declare the bitwise uninterpreted functions, if any clause needs them.
    fn emit_bitwise_preamble_if_needed(&mut self, all_exprs: &[&PureExpr]) {
        if all_exprs
            .iter()
            .any(|expr| needs_bitwise_preamble_expr(expr))
        {
            self.comment("Bitwise UF declarations");
            self.output.push_str(&generate_bitwise_preamble());
            self.output.push('\n');
        }
    }

    /// Declare the `Seq` uninterpreted functions, if any variable is a Seq (#1539).
    fn emit_seq_preamble_if_needed(&mut self, var_sorts: &HashMap<String, VarSort>) {
        if var_sorts.values().any(|s| *s == VarSort::Seq) {
            self.comment("Seq UF declarations (legacy encoding for --emit-smt)");
            self.output.push_str(&generate_seq_preamble());
            self.output.push('\n');
        }
    }

    /// Declare every variable the query names.
    ///
    /// Must precede [`Self::collect_query_symbols`]: declaring a name here is
    /// what stops it being collected as an applied symbol as well.
    fn declare_query_vars(&mut self, var_sorts: &HashMap<String, VarSort>) {
        self.comment("Variable declarations");
        // Deterministic order: a HashMap iterates arbitrarily, and a query
        // whose declaration block reshuffles between runs is useless to diff.
        let mut declarations: Vec<(&String, &VarSort)> = var_sorts.iter().collect();
        declarations.sort_by_key(|(name, _)| *name);
        for (var, sort) in declarations {
            self.declare_var(var, *sort);
        }
        self.output.push('\n');
    }

    /// Collect the symbols the body applies by name, and the ones applied at
    /// more than one signature.
    ///
    /// Logic functions, type-invariant predicates and user methods are applied
    /// by name in the body; without these the query names symbols it never
    /// declares and no solver will read it.
    ///
    /// Clauses are read as formulas; the result expression is read at the sort
    /// `result` was declared at, because the body asserts `(= result <expr>)`
    /// rather than asserting the expression itself.
    ///
    /// Reads `self.declared_vars`, so the variable declarations must already be
    /// emitted — see [`Self::declare_query_vars`].
    fn collect_query_symbols(
        &self,
        clauses: &HoistedClauses,
        var_sorts: &HashMap<String, VarSort>,
    ) -> (Vec<AppliedSymbol>, Vec<String>) {
        let result_sort = var_sorts.get("result").copied().unwrap_or(VarSort::Int);
        let mut applied: Vec<AppliedSymbol> = Vec::new();
        // One symbol used at two different signatures cannot be declared once.
        // `method_smt_name` passes user method names through unqualified, so
        // two receiver types sharing a method name share an SMT symbol — the
        // ordinary case, not an edge case. Declaring the first and staying
        // quiet would produce a query that parses and is wrong; naming the
        // clash is the honest option for a debug artifact.
        let mut conflicts: Vec<String> = Vec::new();
        let mut collect_from = |expr: &PureExpr,
                                used_at: VarSort,
                                applied: &mut Vec<AppliedSymbol>| {
            for symbol in collect_applied_symbols(expr, used_at, var_sorts) {
                if self.declared_vars.contains(&symbol.name) {
                    continue;
                }
                match applied.iter().find(|seen| seen.name == symbol.name) {
                    Some(seen) => {
                        if (seen.params.as_slice(), seen.result) != (&symbol.params, symbol.result)
                            && !conflicts.contains(&symbol.name)
                        {
                            conflicts.push(symbol.name.clone());
                        }
                    }
                    None => applied.push(symbol),
                }
            }
        };
        for clause in clauses
            .requires
            .iter()
            .chain(clauses.ensures.iter())
            .chain(clauses.side_conditions.iter().map(|c| &c.condition))
        {
            collect_from(clause, VarSort::Bool, &mut applied);
        }
        if let Some(result) = &clauses.result {
            collect_from(result, result_sort, &mut applied);
        }
        // Deterministic: this block is diffed between runs. Sorting an empty
        // Vec is a no-op, so doing it here rather than under the emitter's
        // non-empty guard keeps the ordering out of the emitter entirely.
        applied.sort_by(|left, right| left.name.cmp(&right.name));
        (applied, conflicts)
    }

    /// Declare the collected symbols, and note any applied at two signatures.
    fn declare_applied_symbols(&mut self, applied: &[AppliedSymbol], conflicts: &[String]) {
        if applied.is_empty() {
            return;
        }
        self.comment("Uninterpreted symbols (logic functions, type invariants, methods)");
        for symbol in applied {
            self.declare_fn(&symbol.name, &symbol.params, symbol.result);
        }
        for name in conflicts {
            self.comment(&format!(
                "NOTE: `{name}` is applied at more than one signature here; the first is declared, so this query needs it fixed by hand"
            ));
        }
        self.output.push('\n');
    }

    /// Assert the preconditions.
    fn assert_preconditions(&mut self, requires: &[PureExpr]) {
        if !requires.is_empty() {
            self.comment("Preconditions");
            for req in requires {
                self.assert_expr(req);
            }
            self.output.push('\n');
        }
    }

    /// Assert the well-definedness side conditions lifted out of term position.
    fn assert_side_conditions(&mut self, side_conditions: &[HoistedSideCondition]) {
        if !side_conditions.is_empty() {
            self.comment(
                "Well-definedness side conditions, lifted out of the terms that carried them",
            );
            self.comment(
                "(the full encoder discharges the obligations separately; here they are assumed)",
            );
            for condition in side_conditions {
                if condition.is_obligation {
                    self.comment("obligation:");
                }
                self.assert_expr(&condition.condition);
            }
            self.output.push('\n');
        }
    }

    /// Assert `result = body`, if a body was provided.
    fn assert_result_assignment(&mut self, result_expr: Option<&PureExpr>) {
        if let Some(result) = result_expr {
            self.comment("Result assignment");
            let result_var = PureExpr::Var("result".to_string(), None);
            let eq = PureExpr::BinOp(Arc::new(result_var), BinOp::Eq, Arc::new(result.clone()));
            self.assert_expr(&eq);
            self.output.push('\n');
        }
    }

    /// Assert the negation of the postconditions — unsat is what verifies them.
    fn assert_negated_postconditions(&mut self, ensures: &[PureExpr]) {
        if !ensures.is_empty() {
            self.comment("Negated postconditions (unsat = verified)");
            if ensures.len() == 1 {
                self.assert_not_expr(&ensures[0]);
            } else {
                // Flat n-ary (and ...) instead of left-skewed binary tree (#506 F2).
                // SMT-LIB2 `and` accepts n arguments: (and e0 e1 ... en)
                self.output.push_str("(assert (not (and");
                for e in ensures {
                    self.output.push(' ');
                    write_expr_ctx(&mut self.output, e, SmtContext::Normal);
                }
                self.output.push_str(")))\n");
            }
            self.output.push('\n');
        }
    }
}

impl SmtGenerator {
    /// Append the note that this query cannot decide the obligation, if so.
    ///
    /// A symbol the postcondition talks about but nothing else constrains
    /// makes the query trivially satisfiable, whatever the real verdict is.
    /// `--help` sends people here to "read the obligation", and the failure
    /// hint does too, so a file that quietly solves the opposite way is worse
    /// than no file: for a verification tool it is the most misleading
    /// artifact there is. Name them, in the same spirit as the
    /// duplicate-signature note `generate_vc` already emits.
    fn note_unpinned_symbols(
        &mut self,
        requires: &[PureExpr],
        ensures: &[PureExpr],
        side_conditions: &[HoistedSideCondition],
        result_expr: Option<&PureExpr>,
    ) {
        let unconstrained = unconstrained_in_ensures(
            requires,
            ensures,
            side_conditions.iter().map(|c| &c.condition),
            result_expr,
        );
        if unconstrained.is_empty() {
            return;
        }
        self.output.push('\n');
        self.comment("WARNING: this query is weaker than the check that produced the verdict.");
        self.comment(&format!(
            "The postcondition mentions {}, which nothing here constrains,",
            join_names(&unconstrained)
        ));
        self.comment("so this file is satisfiable no matter what was actually proved.");
        self.comment("A `<param>_final` symbol means a `&mut` parameter's final value: this");
        self.comment("generator is a weakest-precondition rendering and does not model");
        self.comment("mutation, loop paths or the solver-context captures the real encoder");
        self.comment("uses. Read it as the shape of the obligation, never as the verdict.");
    }
}

/// Symbols the postcondition rests on that no other part of the query pins
/// down.
///
/// Such a symbol can take any value, so the negated postcondition is
/// satisfiable by construction and the query says nothing. Reported rather
/// than silently emitted — see the call site.
fn unconstrained_in_ensures<'a>(
    requires: &'a [PureExpr],
    ensures: &[PureExpr],
    side_conditions: impl Iterator<Item = &'a PureExpr>,
    result_expr: Option<&'a PureExpr>,
) -> Vec<String> {
    let mut constrained: HashSet<String> = HashSet::new();
    for expr in requires.iter().chain(side_conditions).chain(result_expr) {
        constrained.extend(collect_vars_with_sorts(expr).into_keys());
    }
    // `result` is pinned by the generator's own `(= result <body>)`, which is
    // not part of `result_expr` — the body is the right-hand side. Without
    // this, every function with a return value looked unconstrained.
    if result_expr.is_some() {
        constrained.insert("result".to_string());
    }
    let mut loose: Vec<String> = Vec::new();
    for expr in ensures {
        for (name, _) in collect_vars_with_sorts(expr) {
            if !constrained.contains(&name) && !loose.contains(&name) {
                loose.push(name);
            }
        }
    }
    // Deterministic: this text is diffed between runs.
    loose.sort();
    loose
}

/// `a`, `a and b`, `a, b and c` — for a sentence, not a list.
fn join_names(names: &[String]) -> String {
    match names {
        [] => String::new(),
        [only] => format!("`{only}`"),
        [rest @ .., last] => format!(
            "{} and `{last}`",
            rest.iter()
                .map(|n| format!("`{n}`"))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

impl Default for SmtGenerator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comment_produces_smt_comment() {
        let mut generator = SmtGenerator::new();
        generator.comment("hello world");
        assert_eq!(generator.output(), "; hello world\n");
    }

    #[test]
    fn set_logic_produces_set_logic_command() {
        let mut generator = SmtGenerator::new();
        generator.set_logic("QF_LIA");
        assert_eq!(generator.output(), "(set-logic QF_LIA)\n");
    }

    #[test]
    fn declare_int_produces_declare_const() {
        let mut generator = SmtGenerator::new();
        generator.declare_int("x");
        assert_eq!(generator.output(), "(declare-const x Int)\n");
    }

    #[test]
    fn declare_int_deduplicates() {
        let mut generator = SmtGenerator::new();
        generator.declare_int("x");
        generator.declare_int("x"); // duplicate
        assert_eq!(generator.output(), "(declare-const x Int)\n");
    }

    #[test]
    fn declare_bool_produces_declare_const() {
        let mut generator = SmtGenerator::new();
        generator.declare_bool("b");
        assert_eq!(generator.output(), "(declare-const b Bool)\n");
    }

    #[test]
    fn declare_var_dispatches_by_sort() {
        let mut generator = SmtGenerator::new();
        generator.declare_var("x", VarSort::Int);
        generator.declare_var("b", VarSort::Bool);
        generator.declare_var("s", VarSort::Seq);
        let out = generator.output();
        assert!(out.contains("(declare-const x Int)"));
        assert!(out.contains("(declare-const b Bool)"));
        assert!(out.contains("(declare-const s Seq)"));
    }

    #[test]
    fn assert_expr_wraps_in_assert() {
        let mut generator = SmtGenerator::new();
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        );
        generator.assert_expr(&expr);
        assert!(generator.output().starts_with("(assert "));
        assert!(generator.output().ends_with(")\n"));
        assert!(generator.output().contains("> x 0") || generator.output().contains("(> x 0)"));
    }

    #[test]
    fn assert_not_expr_wraps_in_assert_not() {
        let mut generator = SmtGenerator::new();
        let expr = PureExpr::Var("flag".to_string(), None);
        generator.assert_not_expr(&expr);
        assert_eq!(generator.output(), "(assert (not flag))\n");
    }

    #[test]
    fn check_sat_produces_command() {
        let mut generator = SmtGenerator::new();
        generator.check_sat();
        assert_eq!(generator.output(), "(check-sat)\n");
    }

    #[test]
    fn get_model_produces_command() {
        let mut generator = SmtGenerator::new();
        generator.get_model();
        assert_eq!(generator.output(), "(get-model)\n");
    }

    #[test]
    fn exit_produces_command() {
        let mut generator = SmtGenerator::new();
        generator.exit();
        assert_eq!(generator.output(), "(exit)\n");
    }

    #[test]
    fn into_output_consumes_generator() {
        let mut generator = SmtGenerator::new();
        generator.set_logic("ALL");
        generator.check_sat();
        let output = generator.into_output();
        assert!(output.contains("(set-logic ALL)"));
        assert!(output.contains("(check-sat)"));
    }
}
