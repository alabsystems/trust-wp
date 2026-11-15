// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Arithmetic mode state: division obligations, total-int-arithmetic flag,
//! and bitwise proof mode. Extracted from AYEncoder (#2655).

use std::collections::HashMap;

use ay_dpll::api::{FuncDecl, Term};

/// Runtime arithmetic mode flags and accumulated division obligations.
///
/// - `division_obligations`: path-guarded arithmetic side-obligation terms
///   collected during encoding — `divisor != 0` for `/`/`%` (#1629) and
///   `0 <= amount < bits` for machine-int shifts (ledger int-shift-full).
///   The verification layer checks these as separate proof obligations.
/// - `total_int_arithmetic`: when true, suppresses division-by-zero obligations
///   for ghost functions on mathematical Int. (#1756)
/// - `bitwise_proof_mode`: when true, bitwise operations use ay native BV theory
///   via Int<->BV conversion instead of UF approximations. (#2666)
/// - `signed_window_hints`: variables whose asserted premises pin them into a
///   signed W-bit window (`-2^(W-1) <= v@ <= 2^(W-1)-1`); used by
///   `encode_int_binop_bv` to encode signed narrow bitwise ops exactly
///   (#route-100 rightmostbit latent false-reject).
#[derive(Debug, Clone)]
pub(crate) struct ArithmeticModeState {
    division_obligations: Vec<Term>,
    int_div_terms: Vec<(Term, Term, Term)>,
    int_div_func: Option<FuncDecl>,
    total_int_arithmetic: bool,
    bitwise_proof_mode: bool,
    signed_window_hints: HashMap<String, u32>,
    assumption_position_depth: u32,
}

impl ArithmeticModeState {
    pub(crate) fn new() -> Self {
        Self {
            division_obligations: Vec::new(),
            int_div_terms: Vec::new(),
            int_div_func: None,
            total_int_arithmetic: false,
            bitwise_proof_mode: true,
            signed_window_hints: HashMap::new(),
            assumption_position_depth: 0,
        }
    }

    /// True while the encoder is encoding an expression in ASSUMPTION
    /// position — a precondition, `LetAssume` assumption, or path-condition
    /// fact re-stating what an already-verified body execution established.
    ///
    /// Shift-amount range and divisor obligations are NOT collected in
    /// assumption position: the obligation for a body shift is collected
    /// (path-guarded) when the body VALUE expression is encoded, a body
    /// division is charged at its MIR assert, and re-collecting either from a
    /// fact re-encoding would conjoin it into a foreign goal WITHOUT its
    /// execution-path guard (e.g. the bitwalker `poke` proof_assert VC, where
    /// `(length < 64) ==> !(value >= 1 << length)` arrives as a requires
    /// fact and an unguarded `length < 64` obligation would spuriously fail
    /// at the legal `length == 64`). (ledger int-shift-full, D-114)
    pub(crate) fn assumption_position(&self) -> bool {
        self.assumption_position_depth > 0
    }

    pub(crate) fn enter_assumption_position(&mut self) {
        self.assumption_position_depth += 1;
    }

    pub(crate) fn exit_assumption_position(&mut self) {
        debug_assert!(self.assumption_position_depth > 0);
        self.assumption_position_depth = self.assumption_position_depth.saturating_sub(1);
    }

    pub(crate) fn take_division_obligations(&mut self) -> Vec<Term> {
        std::mem::take(&mut self.division_obligations)
    }

    pub(crate) fn push_division_obligation(&mut self, term: Term) {
        self.division_obligations.push(term);
    }

    pub(crate) fn int_div_terms(&self) -> &[(Term, Term, Term)] {
        &self.int_div_terms
    }

    pub(crate) fn push_int_div_term(&mut self, dividend: Term, divisor: Term, quotient: Term) {
        self.int_div_terms.push((dividend, divisor, quotient));
    }

    pub(crate) fn int_div_func(&self) -> Option<&FuncDecl> {
        self.int_div_func.as_ref()
    }

    pub(crate) fn set_int_div_func(&mut self, func: FuncDecl) {
        self.int_div_func = Some(func);
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn division_obligations(&self) -> &[Term] {
        &self.division_obligations
    }

    pub(crate) fn total_int_arithmetic(&self) -> bool {
        self.total_int_arithmetic
    }

    pub(crate) fn set_total_int_arithmetic(&mut self, total: bool) {
        self.total_int_arithmetic = total;
    }

    pub(crate) fn bitwise_proof_mode(&self) -> bool {
        self.bitwise_proof_mode
    }

    pub(crate) fn set_bitwise_proof_mode(&mut self, enabled: bool) {
        self.bitwise_proof_mode = enabled;
    }

    pub(crate) fn signed_window_hint(&self, var: &str) -> Option<u32> {
        self.signed_window_hints.get(var).copied()
    }

    pub(crate) fn insert_signed_window_hint(&mut self, var: String, width: u32) {
        self.signed_window_hints.insert(var, width);
    }
}
