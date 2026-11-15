// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::logic::{LogicFnDef, LogicMode};

use crate::{
    encoder::{view::is_direct_view_candidate, AYEncoder},
    error::EncodingError,
};

impl AYEncoder {
    /// Register multiple logic functions (test-only convenience wrapper).
    ///
    /// Production code uses `register_logic_fns_with_modes` which supports
    /// per-function mode overrides. This wrapper calls each function with
    /// its default mode.
    #[cfg(test)]
    pub(crate) fn register_logic_fns(
        &mut self,
        logic_fns: &[LogicFnDef],
    ) -> Result<(), EncodingError> {
        for logic_fn in logic_fns {
            if is_direct_view_candidate(logic_fn, logic_fn.mode()) {
                continue;
            }
            self.preseed_logic_fn_return_sort_hint(logic_fn);
        }
        for logic_fn in logic_fns {
            if is_direct_view_candidate(logic_fn, logic_fn.mode()) {
                continue;
            }
            self.declare_logic_fn_signature(logic_fn);
        }
        for logic_fn in logic_fns {
            self.register_logic_fn(logic_fn)?;
        }
        Ok(())
    }

    /// Prescan logic function bodies/requires/ensures for sort hints, then
    /// register the functions with optional mode overrides. Consolidates the
    /// duplicated prescan-then-register pattern used across loops/. (#2034)
    pub(crate) fn prescan_and_register_logic_fns(
        &mut self,
        logic_fns: &[LogicFnDef],
        mode_overrides: Option<&[LogicMode]>,
    ) -> Result<(), EncodingError> {
        for logic_fn in logic_fns {
            self.register_sort_hints(std::slice::from_ref(logic_fn.body()));
            if !logic_fn.requires().is_empty() {
                self.register_sort_hints(logic_fn.requires());
                self.register_formula_sort_hints(logic_fn.requires());
            }
            if !logic_fn.ensures().is_empty() {
                self.register_sort_hints(logic_fn.ensures());
                // Use _fn_ variant (not register_formula_sort_hints) to avoid
                // leaking per-function "result" Bool hints into the shared
                // encoder context. Each logic function's `result` is local to
                // that function — e.g., `pigeon`'s `#[ensures(result)]` (Bool)
                // must not set ExprSort::Bool for "result" globally, since
                // `find_ptr_in_seq`'s result is OptionInt. (#994)
                self.register_formula_fn_sort_hints(logic_fn.ensures());
            }
        }
        self.register_logic_fns_with_modes(logic_fns, mode_overrides)
    }

    /// Register logic functions with optional per-function mode overrides.
    ///
    /// When `mode_overrides` is `Some`, each logic function uses the
    /// corresponding mode from the overrides slice (which must be the same
    /// length as `logic_fns`). This avoids deep-cloning `LogicFnDef` structs
    /// just to change the `mode` field for module-level scoping. (#564)
    pub(crate) fn register_logic_fns_with_modes(
        &mut self,
        logic_fns: &[LogicFnDef],
        mode_overrides: Option<&[LogicMode]>,
    ) -> Result<(), EncodingError> {
        // Previously a debug_assert — but a length mismatch in release builds
        // would silently truncate via zip, potentially making opaque functions
        // visible (unsound) or visible functions opaque (incomplete).
        if let Some(modes) = mode_overrides {
            if modes.len() != logic_fns.len() {
                return Err(EncodingError::solver_error(format!(
                    "mode_overrides length ({}) != logic_fns length ({})",
                    modes.len(),
                    logic_fns.len()
                )));
            }
        }
        if std::env::var_os("TRUST_WP_LOGIC_IDENTITY_TRACE").is_some() {
            eprintln!(
                "trust-wp: logic-identity register [{}]",
                logic_fns
                    .iter()
                    .enumerate()
                    .map(|(i, lf)| format!(
                        "{}:{:?}:opaque={}:ens={}",
                        lf.full_path(),
                        mode_overrides
                            .and_then(|m| m.get(i).copied())
                            .unwrap_or(lf.mode()),
                        lf.is_opaque(),
                        lf.ensures().len()
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
        // One solver symbol per definition: two definitions with different
        // full paths must never share a symbol (the first axiom would answer
        // for both).
        {
            let mut owners: std::collections::HashMap<String, &str> =
                std::collections::HashMap::new();
            for logic_fn in logic_fns {
                let smt_name = trust_wp_core::logic::logic_fn_smt_name(logic_fn.name());
                if let Some(previous) = owners.insert(smt_name.clone(), logic_fn.full_path()) {
                    if previous != logic_fn.full_path() {
                        return Err(EncodingError::solver_error(format!(
                            "logic functions `{previous}` and `{}` share the solver symbol \
                             `{smt_name}`",
                            logic_fn.full_path()
                        )));
                    }
                }
            }
        }
        for (index, logic_fn) in logic_fns.iter().enumerate() {
            let mode = mode_overrides
                .and_then(|modes| modes.get(index).copied())
                .unwrap_or_else(|| logic_fn.mode());
            if is_direct_view_candidate(logic_fn, mode) {
                continue;
            }
            self.preseed_logic_fn_return_sort_hint(logic_fn);
        }
        for (index, logic_fn) in logic_fns.iter().enumerate() {
            let mode = mode_overrides
                .and_then(|modes| modes.get(index).copied())
                .unwrap_or_else(|| logic_fn.mode());
            if is_direct_view_candidate(logic_fn, mode) {
                continue;
            }
            self.declare_logic_fn_signature(logic_fn);
        }
        match mode_overrides {
            Some(modes) => {
                for (logic_fn, &mode) in logic_fns.iter().zip(modes) {
                    self.register_logic_fn_with_mode(logic_fn, mode)?;
                }
            }
            None => {
                for logic_fn in logic_fns {
                    self.register_logic_fn(logic_fn)?;
                }
            }
        }
        Ok(())
    }
}
