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
    sort_inference::{collect_vars_with_sorts, infer_var_sorts, is_seq_var},
    sorts::VarSort,
    var_collect::collect_vars_formula,
};
use crate::formula::{BinOp, Formula, PureExpr};

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

        // Collect all expressions for sort inference
        let mut all_exprs: Vec<&PureExpr> = Vec::new();
        all_exprs.extend(requires.iter());
        all_exprs.extend(ensures.iter());
        if let Some(result) = result_expr {
            all_exprs.push(result);
        }

        if all_exprs
            .iter()
            .any(|expr| needs_bitwise_preamble_expr(expr))
        {
            self.comment("Bitwise UF declarations");
            self.output.push_str(&generate_bitwise_preamble());
            self.output.push('\n');
        }

        // Infer variable sorts from expression contexts
        let mut var_sorts: HashMap<String, VarSort> = HashMap::new();
        for expr in &all_exprs {
            let sorts = infer_var_sorts(expr);
            for (name, sort) in sorts {
                var_sorts.entry(name).or_insert(sort);
            }
        }
        // 'result' default depends on ensures - if ensures use it in Bool context, use Bool
        // Otherwise default to Int for arithmetic results
        var_sorts
            .entry("result".to_string())
            .or_insert(VarSort::Int);

        // Emit Seq preamble if any variable has Seq sort (#1539)
        if var_sorts.values().any(|s| *s == VarSort::Seq) {
            self.comment("Seq UF declarations (legacy encoding for --emit-smt)");
            self.output.push_str(&generate_seq_preamble());
            self.output.push('\n');
        }

        self.comment("Variable declarations");
        for (var, sort) in &var_sorts {
            self.declare_var(var, *sort);
        }
        self.output.push('\n');

        // Assert preconditions
        if !requires.is_empty() {
            self.comment("Preconditions");
            for req in requires {
                self.assert_expr(req);
            }
            self.output.push('\n');
        }

        // Assert result = body (if provided)
        if let Some(result) = result_expr {
            self.comment("Result assignment");
            let result_var = PureExpr::Var("result".to_string(), None);
            let eq = PureExpr::BinOp(Arc::new(result_var), BinOp::Eq, Arc::new(result.clone()));
            self.assert_expr(&eq);
            self.output.push('\n');
        }

        // Assert negation of postconditions (we want unsat)
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

        self.check_sat();
        self.comment("unsat = postcondition verified");
        self.comment("sat = potential counterexample (run get-model)");
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
