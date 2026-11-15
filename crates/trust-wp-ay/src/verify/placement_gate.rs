// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The encoder will not encode a constructor whose fields have not been placed.
//!
//! # What this closes
//!
//! The contract parser reads TEXT. `S { b: _bb, a: aa }` reaches the driver as
//! the constructor name `"S{b,a}"` and two sub-patterns IN THE ORDER WRITTEN —
//! the field names are an instruction to place them, not a representation the
//! encoder understands. The encoder binds sub-patterns POSITIONALLY against the
//! declared datatype, and `normalize_constructor_name` used to strip the
//! `{b,a}` right back off, so unplaced metadata arriving here bound `aa` to the
//! field DECLARED first. On `struct S { b, a }` that is the field `b`: a logic
//! function reads a different field than the one it names, and every contract
//! resting on it is discharged against the wrong value.
//!
//! # Why it is a gate and not a fix in the producers
//!
//! Front s82 fixed that misplacement three times — a candidate cap, a flat
//! name→index fallback, and a kernel with private fields that only rustc's own
//! `VariantDef` can feed. Each fix was sound where it sat, and each time a
//! FOURTH producer was found that never reached it: a `#[logic]` function
//! body, a type-invariant body. Patching producers one at a time is a strategy
//! that loses to the next producer.
//!
//! So this is the consumer, and it is the only door into the encoding
//! pipeline. [`Placed<T>`] has a private field and exactly one constructor,
//! [`Placed::check`], which refuses unplaced metadata; the three
//! `verify_*_inner` entry points take a `Placed<…>` and nothing else can make
//! one. A producer that forgets to place its fields therefore cannot reach the
//! encoder at all: it gets a counted, named `EncodingError` — exit 2, a
//! soundness-gap refusal — rather than a verdict computed from the wrong
//! field. Completeness is the producer's problem; soundness is not.
//!
//! Creusot cannot have this shape at all: it maps each THIR sub-pattern to a
//! rustc-resolved `FieldIdx`, so source order is structurally irrelevant to it.
//!
//! # The same door refuses a final read no logic parameter can carry
//!
//! A logic function reads its `&mut` parameters as one value, so one that
//! reads a final value is withdrawn where the driver defines it
//! (`trust_wp_core::logic::final_reads`, D-108). Every producer of a goal —
//! a clause, a callee's clause at a call, an inlined body, a closure spec, a
//! loop fact — reaches the encoder through here, so a goal that may name a
//! function reading a final value, or carries the marker an inliner
//! expanded, is refused here and nowhere else. Which functions read one is
//! decided here too, to a fixed point over the definitions the request
//! carries (`FinalReaders::reading_in`), withdrawn or not: the library
//! facade takes its definitions from its caller and withdraws nothing, and a
//! definition reading `^q` it handed the encoder verified `unchanged(p)` of
//! `*p = 5` (D-109). The definitions are scanned for placement only: they
//! are not goals.

use trust_wp_core::{
    formula::{first_unplaced_named_ctor, PureExpr},
    logic::{final_reads::FinalReaders, LogicFnDef, TypeInvariantDef},
};

use super::{
    types::VerificationBase, ClosureCaptureInfo, LoopVerificationContext, MutBorrowRequest,
    VerificationRequest,
};
use crate::error::EncodingError;

/// A verification input whose named-field constructors are all PLACED.
///
/// The field is private and [`Self::check`] is the only constructor, so a
/// value of this type is a proof that [`scan_base`] (or its loop twin) ran and
/// found nothing. That is the same shape the driver's
/// `contract_rewrite::placement::FieldPlacement` uses one layer up: privacy,
/// not a doc comment, is what stops the next edit from routing around it.
pub(crate) struct Placed<T>(T);

impl<T> Placed<T> {
    /// The checked value. Available only to code that already holds a
    /// `Placed`, i.e. code downstream of the check.
    pub(crate) fn into_inner(self) -> T {
        self.0
    }
}

impl<'a, 'ctx> Placed<&'a LoopVerificationContext<'ctx>> {
    /// Borrow the checked context without consuming the witness.
    pub(crate) fn get(&self) -> &'a LoopVerificationContext<'ctx> {
        self.0
    }
}

/// The one door. `Placed`'s field is private to this module, so every
/// implementation of this trait has to be written here, next to the scan it
/// must run — an implementation somewhere else cannot produce the value the
/// trait demands.
pub(crate) trait CheckPlacement: Sized {
    /// Refuse if any named-field constructor in this input is still carrying
    /// the parser's field-name metadata.
    fn into_placed(self) -> Result<Placed<Self>, EncodingError>;
}

impl<'a> CheckPlacement for VerificationRequest<'a> {
    fn into_placed(self) -> Result<Placed<Self>, EncodingError> {
        if let Some(name) = scan_base(&self.base, &placement, true) {
            return Err(unplaced_error(&name));
        }
        let readers = final_readers(&self.base);
        if let Some(name) = scan_base(&self.base, &|expr| readers.first_named_in(expr), false) {
            return Err(final_reader_error(&name));
        }
        Ok(Placed(self))
    }
}

impl<'a> CheckPlacement for MutBorrowRequest<'a> {
    fn into_placed(self) -> Result<Placed<Self>, EncodingError> {
        let mut_borrow_exprs = |check: &dyn Fn(&PureExpr) -> Option<String>| {
            self.final_values.values().find_map(check).or_else(|| {
                self.projected_final_pins
                    .as_ref()
                    .and_then(|pins| pins.iter().find_map(|pin| check(&pin.value)))
            })
        };
        if let Some(name) =
            scan_base(&self.base, &placement, true).or_else(|| mut_borrow_exprs(&placement))
        {
            return Err(unplaced_error(&name));
        }
        let readers = final_readers(&self.base);
        let final_read = |expr: &PureExpr| readers.first_named_in(expr);
        if let Some(name) =
            scan_base(&self.base, &final_read, false).or_else(|| mut_borrow_exprs(&final_read))
        {
            return Err(final_reader_error(&name));
        }
        Ok(Placed(self))
    }
}

impl<'a, 'ctx> CheckPlacement for &'a LoopVerificationContext<'ctx> {
    fn into_placed(self) -> Result<Placed<Self>, EncodingError> {
        if let Some(name) = scan_loop_ctx(self, &placement, true) {
            return Err(unplaced_error(&name));
        }
        let readers = FinalReaders::reading_in(self.config.logic_fns.unwrap_or_default());
        if let Some(name) = scan_loop_ctx(self, &|expr| readers.first_named_in(expr), false) {
            return Err(final_reader_error(&name));
        }
        Ok(Placed(self))
    }
}

fn placement(expr: &PureExpr) -> Option<String> {
    first_unplaced_named_ctor(expr).map(str::to_owned)
}

fn unplaced_error(name: &str) -> EncodingError {
    EncodingError::Unsupported {
        message: format!(
            "named-field constructor `{name}` reached the encoder with its field names still \
             attached, which means no declaration was ever consulted for it. Binding its \
             sub-terms in the order they were written would place one field where another is \
             declared, so this function is refused instead. (s82)"
        ),
        span: None,
        contract_text: None,
    }
}

/// The logic functions a request carries that read a final value, withdrawn
/// or not (`trust_wp_core::logic::final_reads`, D-108, D-109).
fn final_readers(base: &VerificationBase<'_>) -> FinalReaders {
    FinalReaders::reading_in(
        base.logic_fns
            .unwrap_or_default()
            .iter()
            .chain(base.local_unfolding_logic_fns.unwrap_or_default()),
    )
}

/// A goal that may name a logic function reading a final value. Its `&mut`
/// parameters are one value there, so the final read is the current one:
/// `^q == *q` of every `q`. Every lane reaches the encoder through this door,
/// so none of them reads it (D-108).
fn final_reader_error(name: &str) -> EncodingError {
    EncodingError::Unsupported {
        message: format!(
            "`{name}` may name a logic function that reads a final value (`^`); a logic \
             parameter is one value, so that read would be the current one, and the goal is \
             refused (D-108)"
        ),
        span: None,
        contract_text: None,
    }
}

type Check<'c> = &'c dyn Fn(&PureExpr) -> Option<String>;

/// Every expression a [`VerificationBase`] carries into the encoder; the
/// logic functions' own definitions only when `defs`.
fn scan_base(base: &VerificationBase<'_>, check: Check<'_>, defs: bool) -> Option<String> {
    scan_exprs(base.requires, check)
        .or_else(|| scan_exprs(base.ensures, check))
        .or_else(|| {
            base.ghost_context
                .and_then(|exprs| scan_exprs(exprs, check))
        })
        .or_else(|| base.return_expr.and_then(check))
        .or_else(|| {
            defs.then(|| {
                base.logic_fns
                    .and_then(|fns| scan_logic_fns(fns, check))
                    .or_else(|| {
                        base.local_unfolding_logic_fns
                            .and_then(|fns| scan_logic_fns(fns, check))
                    })
            })
            .flatten()
        })
        .or_else(|| {
            base.type_invariants
                .and_then(|invs| scan_type_invariants(invs, check))
        })
        .or_else(|| {
            base.type_constants
                .and_then(|map| map.values().find_map(check))
        })
        .or_else(|| {
            base.closure_captures
                .and_then(|captures| scan_closure_captures(captures, check))
        })
}

/// A closure's inlined body and its own requires/ensures are specification
/// text too: `closure_inline` substitutes them straight into the obligation,
/// so a pattern they carry is bound by the encoder like any clause's.
fn scan_closure_captures(captures: &[ClosureCaptureInfo], check: Check<'_>) -> Option<String> {
    captures.iter().find_map(|info| {
        info.body_expr()
            .and_then(check)
            .or_else(|| {
                info.ensures_exprs()
                    .and_then(|exprs| scan_exprs(exprs, check))
            })
            .or_else(|| {
                info.requires_exprs()
                    .and_then(|exprs| scan_exprs(exprs, check))
            })
    })
}

fn scan_loop_ctx(
    ctx: &LoopVerificationContext<'_>,
    check: Check<'_>,
    defs: bool,
) -> Option<String> {
    scan_exprs(ctx.requires, check)
        .or_else(|| scan_exprs(ctx.ensures, check))
        .or_else(|| scan_exprs(ctx.invariants, check))
        .or_else(|| ctx.loop_condition.and_then(check))
        .or_else(|| ctx.variant.and_then(check))
        .or_else(|| ctx.return_expr.and_then(check))
        .or_else(|| scan_exprs(ctx.init_extra_facts, check))
        .or_else(|| scan_exprs(ctx.post_extra_facts, check))
        .or_else(|| ctx.body_effect.values().find_map(check))
        .or_else(|| ctx.deref_body_effect.values().find_map(check))
        .or_else(|| ctx.double_deref_body_effect.values().find_map(check))
        .or_else(|| {
            ctx.pre_loop_assignments
                .values()
                .find_map(|binding| check(&binding.value))
        })
        .or_else(|| scan_exprs(&ctx.config.transition_facts, check))
        .or_else(|| scan_exprs(&ctx.config.bridge_facts, check))
        .or_else(|| {
            defs.then(|| {
                ctx.config
                    .logic_fns
                    .and_then(|fns| scan_logic_fns(fns, check))
            })
            .flatten()
        })
        .or_else(|| {
            ctx.config
                .type_invariants
                .and_then(|invs| scan_type_invariants(invs, check))
        })
        .or_else(|| {
            ctx.config
                .type_constants
                .and_then(|map| map.values().find_map(check))
        })
}

fn scan_exprs(exprs: &[PureExpr], check: Check<'_>) -> Option<String> {
    exprs.iter().find_map(check)
}

fn scan_logic_fns(logic_fns: &[LogicFnDef], check: Check<'_>) -> Option<String> {
    logic_fns.iter().find_map(|lf| {
        check(lf.body())
            .or_else(|| scan_exprs(lf.requires(), check))
            .or_else(|| scan_exprs(lf.ensures(), check))
            .or_else(|| scan_exprs(lf.variants(), check))
    })
}

fn scan_type_invariants(defs: &[TypeInvariantDef], check: Check<'_>) -> Option<String> {
    defs.iter().find_map(|def| check(def.body()))
}

#[cfg(test)]
#[path = "placement_gate_tests.rs"]
mod tests;
