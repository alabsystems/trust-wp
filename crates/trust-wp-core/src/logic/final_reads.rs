// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What denotes a final value, decided once (D-108, D-109).
//!
//! A clause states the value a borrow is left with by `^e` (`final_value(e)`
//! parses to the same node), by a call that states it whatever defines it
//! (`resolve(e)` is `*e == ^e`; `structural_resolve`, Creusot's `Fin::fin`,
//! an iterator's `completed`), and by a call of a logic function whose body
//! or clauses denote one, to a fixed point over their bodies
//! ([`FinalReaders::reading_in`]). [`FinalReaders::final_operands`] is the
//! one predicate every refusal of a final value reads: the state
//! elaboration's (a final another holder decides, a final read in the entry
//! state, a final read through a value holding a parameter) and the
//! encoder's door. Each refusal once read the spelling `^` alone, and
//! `resolve(x)` of a `&mut` over interior-mutable memory, `old(resolve(x))`
//! and `exists<q> q == x && ^q == *q` each verified a false claim.
//!
//! A logic function's parameters are values: a `&mut T` parameter is one
//! value, and a clause passes the current value of the borrow it names. A
//! final read inside the function therefore collapses onto the current read,
//! and `#[logic(open, prophetic)] fn unchanged(q: &mut i32) -> bool { ^q ==
//! *q }` holds of every `q`: `#[ensures(unchanged(p))]` verified of `*p = 5`,
//! of a borrow stored in another parameter, of a cell set through it, and a
//! caller holding it beside a true clause was vacuous. Left uninterpreted it
//! is no sounder: a function of the current value alone equates two borrows
//! that agree now and differ in the end.
//!
//! So such a function is withdrawn where it is defined
//! ([`withdraw_final_readers`]): its body becomes a call of
//! [`WITHDRAWN_FINAL_READER`] over its parameters and its clauses are
//! dropped, so an inliner that expands it carries the marker into the goal,
//! and the one door into the encoding pipeline refuses every goal that names
//! the marker or may name a function reading a final value
//! ([`FinalReaders::first_named_in`]), withdrawn or not: a producer that hands
//! the encoder definitions nothing withdrew (the library facade) meets the
//! same door.

use std::collections::HashSet;

use super::{identity::logic_fn_unique_id, LogicFnDef, LogicMode};
use crate::formula::PureExpr;

/// The body a withdrawn logic function is given: a call of this name over
/// its parameters. Nothing defines it, and no goal naming it is encoded.
pub const WITHDRAWN_FINAL_READER: &str = "__trust_wp_withdrawn_final_reader";

/// Calls that denote a final value of their operands whatever defines them:
/// `resolve` (`*e == ^e`), `structural_resolve` (a conjunction of those),
/// `resolve_coherence`, `fin` (Creusot's `^`) and `completed` (an iterator's
/// final state).
const FINAL_READING_CALLS: &[&str] = &[
    "resolve",
    "structural_resolve",
    "resolve_coherence",
    "completed",
    "fin",
];

/// The last `::` segment of a call name (`Self::unchanged`, `m::unchanged`).
fn leaf(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// Every spelling a call of `def` may carry: the full path, the unique id,
/// the crate-relative path, the short name, and the name it was renamed to.
fn spellings(def: &LogicFnDef) -> Vec<String> {
    let full_path = def.full_path();
    let mut out = vec![
        full_path.to_string(),
        logic_fn_unique_id(full_path),
        leaf(full_path).to_string(),
        def.name().to_string(),
        def.short_name().to_string(),
    ];
    if let Some((_, relative)) = full_path.split_once("::") {
        out.push(relative.to_string());
    }
    out
}

/// The logic functions that read a final value, by every spelling a call of
/// one may carry, matched over-approximately: a call may name one when its
/// name, or its last path segment, is a spelling. A spurious match refuses a
/// goal; a missed one reads a final value as the current one.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FinalReaders {
    spellings: HashSet<String>,
}

impl FinalReaders {
    /// The functions among `defs` that read a final value, to a fixed point
    /// over their bodies: a definition whose body or a clause denotes one
    /// ([`Self::reads_a_final`], over the functions found so far), whose body
    /// is the [`WITHDRAWN_FINAL_READER`] marker, or that is prophetic with a
    /// body nobody reads.
    #[must_use]
    pub fn reading_in<'d>(defs: impl IntoIterator<Item = &'d LogicFnDef>) -> Self {
        let defs: Vec<&LogicFnDef> = defs.into_iter().collect();
        Self::fixed_point(&defs).0
    }

    /// [`Self::reading_in`], with the positions in `defs` it found.
    fn fixed_point(defs: &[&LogicFnDef]) -> (Self, Vec<usize>) {
        let mut readers = Self::default();
        let mut found: Vec<usize> = Vec::new();
        loop {
            let before = found.len();
            for (at, def) in defs.iter().enumerate() {
                if !found.contains(&at) && readers.def_reads_a_final(def) {
                    found.push(at);
                    readers.spellings.extend(spellings(def));
                }
            }
            if found.len() == before {
                found.sort_unstable();
                return (readers, found);
            }
        }
    }

    /// Whether a call spelled `name` may denote one of these functions, or is
    /// the marker a withdrawn one's body is. A goal naming one is refused at
    /// the encoder's door: its `&mut` parameters are one value there.
    #[must_use]
    pub fn may_name(&self, name: &str) -> bool {
        name == WITHDRAWN_FINAL_READER
            || self.spellings.contains(name)
            || self.spellings.contains(leaf(name))
    }

    /// Whether a call spelled `name` denotes a final value of its operands:
    /// one of [`FINAL_READING_CALLS`], whatever path spells it, or a function
    /// [`Self::may_name`].
    fn call_denotes_a_final(&self, name: &str) -> bool {
        FINAL_READING_CALLS.contains(&leaf(name)) || self.may_name(name)
    }

    /// THE predicate: the operands whose final value `node` itself denotes
    /// (not its subterms'), however it is spelled: the operand of `^e`, and
    /// every argument (a method's receiver included) of a call that denotes
    /// one. `None` when `node` denotes no final value.
    #[must_use]
    pub fn final_operands<'e>(&self, node: &'e PureExpr) -> Option<Vec<&'e PureExpr>> {
        match node {
            PureExpr::Final(operand) => Some(vec![operand.as_ref()]),
            PureExpr::LogicFnCall { name, args } if self.call_denotes_a_final(name) => {
                Some(args.iter().collect())
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if self.call_denotes_a_final(method) => Some(
                std::iter::once(receiver.as_ref())
                    .chain(args.iter())
                    .collect(),
            ),
            _ => None,
        }
    }

    /// Whether `expr` denotes a final value anywhere ([`Self::final_operands`]).
    #[must_use]
    pub fn reads_a_final(&self, expr: &PureExpr) -> bool {
        expr.any_recursive(|node| self.final_operands(node).is_some())
    }

    /// Whether `def`, as defined, reads a final value: its body or a clause
    /// denotes one, or it is prophetic and its body is not read (opaque,
    /// trusted, a trait declaration).
    fn def_reads_a_final(&self, def: &LogicFnDef) -> bool {
        (def.mode() == LogicMode::Prophetic && def.is_opaque())
            || std::iter::once(def.body())
                .chain(def.requires())
                .chain(def.ensures())
                .chain(def.variants())
                .any(|expr| self.reads_a_final(expr))
    }

    /// The first call in `expr` that may denote one of these functions (or
    /// the marker itself), as spelled.
    #[must_use]
    pub fn first_named_in(&self, expr: &PureExpr) -> Option<String> {
        let mut found = None;
        expr.any_recursive(|node| {
            let name = match node {
                PureExpr::LogicFnCall { name, .. } => name,
                PureExpr::MethodCall { method, .. } => method,
                _ => return false,
            };
            if self.may_name(name) {
                found = Some(name.clone());
                true
            } else {
                false
            }
        });
        found
    }
}

/// Withdraw every definition that reads a final value, and every one that
/// calls such a one, to a fixed point ([`FinalReaders::reading_in`]): its
/// body becomes a call of [`WITHDRAWN_FINAL_READER`] over its parameters,
/// and its requires, ensures and variants are dropped, so no axiom or
/// unfolding of it reaches any goal. Returns the full paths withdrawn.
pub fn withdraw_final_readers(defs: &mut [LogicFnDef]) -> Vec<String> {
    let (_, withdrawn) = FinalReaders::fixed_point(&defs.iter().collect::<Vec<_>>());
    withdrawn
        .into_iter()
        .map(|at| {
            let def = &mut defs[at];
            let args = def
                .params()
                .iter()
                .map(|param| PureExpr::Var(param.clone(), None))
                .collect();
            def.set_body(PureExpr::LogicFnCall {
                name: WITHDRAWN_FINAL_READER.to_string(),
                args,
            });
            def.set_requires(Vec::new());
            def.set_ensures(Vec::new());
            def.variants_mut().clear();
            def.full_path().to_string()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::contract_parser::parse_contract;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn call(name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    fn def(path: &str, param: &str, body: PureExpr) -> LogicFnDef {
        let name = path.rsplit("::").next().unwrap().to_string();
        LogicFnDef::new(name, path.to_string(), vec![param.to_string()], body)
            .with_mode(LogicMode::Open)
    }

    fn unchanged_body() -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(var("q")))),
            crate::formula::BinOp::Eq,
            Arc::new(PureExpr::Deref(Arc::new(var("q")))),
        )
    }

    /// `unchanged` reads `^q`; `wrapper` calls it by its bare name; `plain`
    /// reads only `*q`. The first two are withdrawn, the third kept.
    #[test]
    fn a_final_read_withdraws_its_function_and_every_caller() {
        let mut defs = vec![
            def("c::wrapper", "q", call("unchanged", vec![var("q")])),
            def("c::unchanged", "q", unchanged_body()),
            def("c::plain", "q", PureExpr::Deref(Arc::new(var("q")))),
        ];
        let withdrawn = withdraw_final_readers(&mut defs);
        assert_eq!(withdrawn, vec!["c::wrapper", "c::unchanged"]);
        assert_eq!(
            defs[1].body(),
            &call(WITHDRAWN_FINAL_READER, vec![var("q")])
        );
        assert_eq!(defs[2].body(), &PureExpr::Deref(Arc::new(var("q"))));

        let readers = FinalReaders::reading_in(&defs);
        let goal = PureExpr::MethodCall {
            receiver: Arc::new(var("p")),
            method: "unchanged".to_string(),
            args: vec![],
        };
        assert_eq!(readers.first_named_in(&goal), Some("unchanged".to_string()));
        assert_eq!(
            readers.first_named_in(&call("Self::wrapper", vec![var("p")])),
            Some("Self::wrapper".to_string())
        );
        assert_eq!(readers.first_named_in(&call("plain", vec![var("p")])), None);
    }

    /// A definition nothing withdrew (the library facade takes its
    /// definitions from its caller) is found where the door looks, to the
    /// same fixed point.
    #[test]
    fn an_unwithdrawn_final_reader_is_found_where_the_door_looks() {
        let defs = vec![
            def("c::wrapper", "q", call("unchanged", vec![var("q")])),
            def("c::unchanged", "q", unchanged_body()),
            def("c::plain", "q", PureExpr::Deref(Arc::new(var("q")))),
        ];
        let readers = FinalReaders::reading_in(&defs);
        assert!(readers.may_name("unchanged") && readers.may_name("wrapper"));
        assert!(!readers.may_name("plain"));
    }

    /// A resolve in the body reads a final value as `^` does; an opaque
    /// prophetic function may, unseen.
    #[test]
    fn a_resolve_or_an_unread_prophetic_body_withdraws_its_function() {
        let mut defs = vec![
            def("c::r", "q", call("resolve", vec![var("q")])),
            def("c::hidden", "q", PureExpr::Bool(true))
                .with_mode(LogicMode::Prophetic)
                .with_opaque(true),
            def("c::seen", "q", PureExpr::Bool(true)).with_mode(LogicMode::Prophetic),
        ];
        assert_eq!(withdraw_final_readers(&mut defs), vec!["c::r", "c::hidden"]);
    }

    /// Every spelling of a final value denotes it: `^e`, `final_value(e)`,
    /// `resolve` by any path or as a method, `structural_resolve`, `fin`, and
    /// a logic function reading one; the builtins are not what the door
    /// refuses.
    #[test]
    fn every_spelling_of_a_final_value_denotes_its_operands() {
        let defs = vec![def("c::unchanged", "q", unchanged_body())];
        let readers = FinalReaders::reading_in(&defs);
        let operands = |text: &str| {
            let clause = parse_contract(text).expect("parses");
            let mut out = Vec::new();
            clause.for_each_recursive(|node| {
                if let Some(operands) = readers.final_operands(node) {
                    out.extend(operands.iter().map(ToString::to_string));
                }
            });
            out
        };
        for text in [
            "^x == *x",
            "final_value(x) == *x",
            "resolve(x)",
            "x.resolve()",
            "Resolve::resolve(x)",
            "trust_wp::resolve::resolve(x)",
            "structural_resolve(x)",
            "x.fin() == *x",
            "unchanged(x)",
            "c::unchanged(x)",
        ] {
            assert_eq!(operands(text), vec!["x".to_string()], "{text}");
        }
        assert_eq!(operands("*x == 0 && plain(x)"), Vec::<String>::new());
        assert_eq!(
            readers.first_named_in(&call("resolve", vec![var("x")])),
            None
        );
        assert_eq!(
            readers.first_named_in(&call("unchanged", vec![var("x")])),
            Some("unchanged".to_string())
        );
    }
}
