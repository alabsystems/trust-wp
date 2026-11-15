// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The state each read of a parameter denotes, decided once for every lane
//! that reads a contract.
//!
//! A function's own lane proves its postcondition under one reading of each
//! `*p`, `^p`, `p@` and `old(..)`, and every call of the function is credited
//! with the same clause. The two once read it apart: the callee proved
//! swap's `*a == old(*b)` with `*a` the value `a` is left with, and the call
//! read `*a` as the value at the call, crediting its caller with the entry
//! values being equal; the call read the callee's `old(e)` as the CALLER's
//! entry state, so after `*x = 5; get(x)` the caller learned `result == *x`
//! of its own entry `*x`. Both lanes now read a clause through the functions
//! here, over the same [`Signature`]:
//!
//! 1. [`place_parameter_reads`]: a binder of a parameter is the parameter
//!    (`old(..)` included, since a parameter is one value in every state),
//!    and a read the state rule cannot place, or a dereference of a
//!    parameter the signature makes no reference, is refused;
//! 2. [`postcondition_states`]: the pre-Creusot dialect (a clause naming a
//!    `&mut` parameter inside `old(..)` reads a bare `*p` and `p@` as the
//!    value `p` is left with) is rewritten to Creusot's: `^p` for the final
//!    value, `*p` for the entry one;
//! 3. at a call, [`postcondition_at_a_call`]: the callee's entry state is the
//!    call's pre-state, so `old(e)` over the callee's parameters is `e`, read
//!    where the arguments are.
//!
//! Whether a `&mut` parameter may be lent into the returned value is a fact
//! of the signature too ([`Signature::set_result_may_carry_a_borrow`]): a
//! pre-Creusot clause's bare `*p` of such a parameter is the value `p` is
//! left with, which whoever holds the result decides, so it has no reading in
//! either lane and is refused in both. So is whether it may be stored where
//! another parameter's holder reads it after the call
//! ([`Signature::lend_into_a_parameter`]), or lent into a result whose
//! holder writes through it by interior mutability
//! ([`Signature::set_result_writes_by_interior_mutability`]), or whether its
//! referent holds interior-mutable memory
//! ([`Signature::over_interior_mutable_memory`]); then its final value has no
//! reading either, in either dialect. What denotes a final value is decided
//! by one predicate, [`FinalReaders::final_operands`] over the signature's
//! [`Signature::read_finals_through`]: `^p`, `final_value(p)`, `resolve(p)`
//! by any path, and a call of a logic function whose body reads one, so each
//! refusal applies to the value denoted, not to a spelling (D-109). A clause
//! whose reading at a call depends on a parameter type the call cannot read
//! is refused there.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use super::{
    first_dereference_of_a_non_reference, first_final_held_through_a_reference_parameter,
    first_unplaced_mut_ref_read, places::is_field_projection, resolve_aliases_with, ParamReference,
};
use crate::{formula::PureExpr, logic::final_reads::FinalReaders};

/// A contract's parameters, as its signature types them.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Signature {
    /// Every parameter (and binding of a destructuring parameter): each is
    /// one value in every state the clause reads, so a binder of it is it
    /// under `old(..)` too.
    names: std::collections::BTreeSet<String>,
    /// What `*`, `^` and `@` of each parameter (or binding of a
    /// destructuring parameter) read; a name missing here is one the
    /// signature does not classify (a type with a `Deref` of its own).
    references: BTreeMap<String, ParamReference>,
    /// The parameters whose type is, or holds, a `&mut`: a clause naming
    /// one inside `old(..)` is in the pre-Creusot dialect.
    mut_ref_params: HashSet<String>,
    /// Parameters whose type the signature could not be read for.
    untyped: HashSet<String>,
    /// Whether the return type could carry the borrow of a `&mut`
    /// parameter: then every one of them may be lent into the result.
    result_may_carry_a_borrow: bool,
    /// The `&mut` parameters whose borrow may be stored where another
    /// parameter's holder reads it after the call (`*slot = Some(p)`).
    lent_into_a_parameter: HashSet<String>,
    /// Whether the returned value may carry a borrow its holder writes
    /// through by interior mutability (`&Cell<T>`, `&Box<Cell<T>>`): a write
    /// no prophecy of the result records.
    result_writes_by_interior_mutability: bool,
    /// The `&mut` parameters whose referent holds memory a shared reference
    /// writes (`&mut Cell<i32>`, `&mut S` with `S { c: &Cell<i32> }`).
    over_interior_mutable_memory: HashSet<String>,
    /// The logic functions whose call denotes a final value of its
    /// arguments, beside the calls that denote one whatever defines them.
    final_readers: Arc<FinalReaders>,
}

impl Signature {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record the parameter `name`: what its type makes of `*`, `^` and `@`
    /// (`None` when the type has a reading of its own), and whether the type
    /// is or holds a `&mut`.
    pub fn insert(
        &mut self,
        name: impl Into<String>,
        reference: Option<ParamReference>,
        holds_mut_ref: bool,
    ) {
        let name = name.into();
        self.names.insert(name.clone());
        if let Some(reference) = reference {
            self.references.insert(name.clone(), reference);
        }
        if holds_mut_ref {
            self.mut_ref_params.insert(name);
        }
    }

    /// Record a parameter whose type is not known: every reading that
    /// depends on it is refused.
    pub fn insert_untyped(&mut self, name: impl Into<String>) {
        let name = name.into();
        self.names.insert(name.clone());
        self.untyped.insert(name);
    }

    #[must_use]
    pub fn reference(&self, name: &str) -> Option<ParamReference> {
        self.references.get(name).copied()
    }

    /// The parameters whose type is, or holds, a `&mut`.
    #[must_use]
    pub fn mut_ref_params(&self) -> &HashSet<String> {
        &self.mut_ref_params
    }

    /// Record whether the function's return type could carry the borrow of
    /// a `&mut` parameter (a reference, a raw pointer, a type whose fields
    /// reach one, a type the signature cannot see into).
    pub fn set_result_may_carry_a_borrow(&mut self, may: bool) {
        self.result_may_carry_a_borrow = may;
    }

    /// Record that the borrow of the `&mut` parameter `name` may be stored
    /// where another parameter's holder reads it after the call: the value
    /// it is left with is that holder's to decide.
    pub fn lend_into_a_parameter(&mut self, name: impl Into<String>) {
        self.lent_into_a_parameter.insert(name.into());
    }

    /// Record whether the returned value may carry a borrow its holder writes
    /// through by interior mutability.
    pub fn set_result_writes_by_interior_mutability(&mut self, writes: bool) {
        self.result_writes_by_interior_mutability = writes;
    }

    /// Record that the referent of the `&mut` parameter `name` holds memory a
    /// shared reference writes (interior mutability): whoever holds such a
    /// reference writes it by a route no prophecy records (a copy of the
    /// reference, a loop, a callee), so the value `name` is left with is not
    /// the function's to state.
    pub fn over_interior_mutable_memory(&mut self, name: impl Into<String>) {
        self.over_interior_mutable_memory.insert(name.into());
    }

    /// Read a call of any of `readers` as a final read of its arguments
    /// ([`FinalReaders::final_operands`]): the logic functions of the crate
    /// that read a final value, to a fixed point over their bodies.
    pub fn read_finals_through(&mut self, readers: Arc<FinalReaders>) {
        self.final_readers = readers;
    }

    /// What denotes a final value in a clause over this signature.
    #[must_use]
    pub fn final_readers(&self) -> &FinalReaders {
        &self.final_readers
    }

    /// The `&mut` parameters whose final value some other holder decides by a
    /// write no prophecy of the function records: lent into another
    /// parameter, or into a result written through by interior mutability,
    /// or over interior-mutable memory. A `&mut` lent into a result it is
    /// read through (`&mut T`) is not one: its final value is the result's
    /// (`^p == ^result`).
    fn finals_decided_elsewhere(&self) -> HashSet<String> {
        let mut decided = self.lent_into_a_parameter.clone();
        decided.extend(self.over_interior_mutable_memory.iter().cloned());
        if self.result_writes_by_interior_mutability {
            decided.extend(self.mut_ref_params.iter().cloned());
        }
        decided
    }

    /// The `&mut` parameters that may be lent: into the returned value, or
    /// into another parameter.
    #[must_use]
    pub fn may_lend(&self) -> HashSet<String> {
        let mut lent = self.lent_into_a_parameter.clone();
        if self.result_may_carry_a_borrow {
            lent.extend(self.mut_ref_params.iter().cloned());
        }
        lent
    }

    /// Whether `name` is a parameter (or a binding of a destructuring one).
    #[must_use]
    pub fn has(&self, name: &str) -> bool {
        self.names.contains(name)
    }
}

/// Which clause of a contract is read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClauseKind {
    Precondition,
    Postcondition,
}

/// `clause` with every binder of a parameter read as the parameter, `old(..)`
/// included (a `&mut` parameter is a reference, one value in every state, and
/// any other parameter cannot change), refused where a read has no reading:
/// a dereference of a parameter its type makes no reference (`*x` of an `x:
/// i32`, `^r` of an `r: &i32`), and, in a postcondition, a read of a `&mut`
/// parameter's referent the state rule cannot place (`*t.0` of `let t = (p,
/// 0)`, any read of a `&mut` a parameter holds without being it), a final
/// value read in the entry state ([`first_final_in_the_entry_state`]), a
/// pre-Creusot read of the value a parameter the result may borrow is left
/// with ([`first_read_of_a_lent_final`]), or, in either dialect, a final
/// value another holder decides ([`first_final_decided_elsewhere`]). Each
/// final value is found by what denotes it ([`FinalReaders::final_operands`]),
/// not by its spelling.
///
/// # Errors
///
/// The refusal, described.
pub fn place_parameter_reads(
    clause: &PureExpr,
    signature: &Signature,
    kind: ClauseKind,
) -> Result<PureExpr, String> {
    let clause = resolve_aliases_with(clause, &|name| signature.has(name));
    // A field of a `&mut` parameter is read where `*p` is: at entry in
    // Creusot's reading (which the `*p`-keyed rewrite already gives a bare
    // `p`), and as the value `p` is left with in the pre-Creusot dialect,
    // which only an explicit `(*p).f` tells the rewrite.
    let clause = if in_the_old_dialect(&clause, signature.mut_ref_params()) {
        with_field_reads_dereferenced(&clause, signature)
    } else {
        clause
    };
    let reference = |name: &str| signature.reference(name);
    if let Some(refusal) = first_dereference_of_a_non_reference(&clause, &reference) {
        return Err(refusal);
    }
    // `^x.m`, `^*x`, `^x[0]` of a reference parameter `x` reads the final
    // value of a borrow `x`'s referent holds, whatever clause it sits in: a
    // precondition reads the same prophecy a postcondition does, and the
    // encoder would read either as the field the outer borrow is left with
    // (`#[requires(^x.m == k)]` of a body writing `*x.m = 5` proved `k == 5`).
    // Decided by the parameter's type, once for every lane (D-183).
    if let Some(refusal) = first_final_held_through_a_reference_parameter(
        &clause,
        &reference,
        signature.final_readers(),
    ) {
        return Err(refusal);
    }
    if kind == ClauseKind::Postcondition {
        let readers = signature.final_readers();
        if let Some(refusal) = first_unplaced_mut_ref_read(&clause, &reference, readers) {
            return Err(refusal);
        }
        if let Some(refusal) = first_final_in_the_entry_state(&clause, readers) {
            return Err(refusal);
        }
        if let Some(refusal) = first_read_of_a_lent_final(&clause, signature) {
            return Err(refusal);
        }
        if let Some(refusal) = first_final_decided_elsewhere(&clause, signature) {
            return Err(refusal);
        }
    }
    Ok(clause)
}

/// The refusal of a postcondition that reads a final value inside `old(..)`,
/// however denoted: `old(^p)`, `old(resolve(p))`, `old(unchanged(p))`. The
/// entry state has no final value to read; the function's lane read
/// `old(resolve(x))` of `*x = 5` under `*x != 5` as true, and a call read
/// such a clause at its pre-state. Refused alike in both.
fn first_final_in_the_entry_state(clause: &PureExpr, readers: &FinalReaders) -> Option<String> {
    let mut refusal = None;
    clause.for_each_recursive(|node| {
        if refusal.is_none() {
            if let PureExpr::Old(inner) = node {
                if readers.reads_a_final(inner) {
                    refusal = Some(format!(
                        "`{node}` reads a final value in the entry state, which has no reading"
                    ));
                }
            }
        }
    });
    refusal
}

/// The refusal of a postcondition that reads the final value of a `&mut`
/// parameter another holder decides by a write no prophecy of the function
/// records ([`Signature::finals_decided_elsewhere`]), in either dialect.
///
/// After `*slot = Some(p)` (or `v.push(p)`), `p`'s final value is whatever
/// the holder of `slot` leaves it, after the call; after `&*p` is returned
/// as a `&Cell<i32>`, whatever the result's holder sets the cell to. The
/// function cannot state it, and no lane gives the reading a prophecy of its
/// own. A `&mut` result is different: its final value is the result's
/// (`^p == ^result`). Every caller was credited with `stash`'s `^p == *p`
/// while writing 5 through the slot, and with `give`'s while setting the
/// cell. A referent holding interior-mutable memory is written by whoever
/// holds a shared reference into it: `x.set(5)` inside an annotated loop and
/// `let c = x.c; c.set(5)` each proved `^x == *x` (D-108). Decided from the
/// signature, so the function's lane and every call refuse the same clauses.
///
/// The final value is found by what denotes it ([`FinalReaders::final_operands`]):
/// `resolve(x)` is `*x == ^x`, and a logic function reading `^q` of its
/// argument reads the argument's. A final read of a name the clause binds
/// (`exists<q> q == x && ^q == *q`, a `match` or `let` binding no alias
/// resolves) may denote any value the clause names, so in a clause naming a
/// parameter whose final value is decided elsewhere it reads that one too:
/// each spelling once verified a false claim of a `&mut` over a copied
/// `&Cell` (D-109).
fn first_final_decided_elsewhere(clause: &PureExpr, signature: &Signature) -> Option<String> {
    let decided = signature.finals_decided_elsewhere();
    if decided.is_empty() {
        return None;
    }
    // `|r| ..` binds the returned value, not a quantified one.
    let clause = applied_to_the_result(clause).unwrap_or_else(|_| clause.clone());
    let bound = names_bound_in(&clause);
    let named_parameters: HashSet<String> = clause
        .free_vars()
        .into_iter()
        .filter(|name| decided.contains(name))
        .collect();
    let readers = signature.final_readers();
    let mut read = HashSet::new();
    clause.for_each_recursive(|node| {
        for operand in readers.final_operands(node).unwrap_or_default() {
            let names = operand.free_vars();
            read.extend(names.iter().filter(|name| decided.contains(*name)).cloned());
            if names.iter().any(|name| bound.contains(name)) {
                read.extend(named_parameters.iter().cloned());
            }
        }
    });
    (!read.is_empty()).then(|| {
        format!(
            "the final value of {} is not the function's to state: another parameter or the \
             returned value may hold its borrow after the call, or its referent holds memory a \
             shared reference writes, and whoever holds it decides that value by a write no \
             prophecy records",
            sorted(&read)
        )
    })
}

/// The refusal of a pre-Creusot postcondition that reads a bare `*p` (or
/// `p@`, or a field of `p`) of a `&mut` parameter the function may lend
/// ([`Signature::may_lend`]) or whose referent holds interior-mutable memory
/// ([`Signature::over_interior_mutable_memory`]).
///
/// In that dialect the read is the value `p` is left with, and when `p` is
/// lent into the returned value (or another parameter) that is whatever the
/// holder of its borrow leaves it: the function cannot state it, and a call cannot read it as the value
/// after the call. The lane once read it as the ENTRY value instead, so `*p
/// == old(*p)` held of `*p = 5; p as *mut i32` and every caller was credited
/// with its argument unchanged. Decided from the signature alone, so a
/// function's own lane and each of its calls refuse the same clauses.
fn first_read_of_a_lent_final(clause: &PureExpr, signature: &Signature) -> Option<String> {
    let mut lent = signature.may_lend();
    lent.extend(signature.over_interior_mutable_memory.iter().cloned());
    if lent.is_empty() {
        return None;
    }
    let clause = applied_to_the_result(clause).unwrap_or_else(|_| clause.clone());
    let mut_ref_params = signature.mut_ref_params();
    if !in_the_old_dialect(&clause, mut_ref_params) {
        return None;
    }
    let read = clause.transform_postcondition_for_mut_refs(mut_ref_params);
    let lent_kept =
        clause.transform_postcondition_for_mut_refs_keeping_current(mut_ref_params, &lent);
    let lender = if signature.result_may_carry_a_borrow {
        "the returned value may borrow it"
    } else if signature.lent_into_a_parameter.is_empty() {
        "its referent holds memory a shared reference writes"
    } else {
        "another parameter may hold its borrow after the call"
    };
    (read != lent_kept).then(|| {
        format!(
            "in the pre-Creusot dialect (the clause names a `&mut` parameter inside `old(..)`) a \
             bare read of {} is the value it is left with, and {lender}, so that value is its \
             holder's to decide: write the claim over `result`, or in Creusot's reading (`^p`)",
            sorted(&lent)
        )
    })
}

/// `clause` with a field of a `&mut` parameter (`p.f`, `p.0`) read as the
/// field of its referent, `(*p).f`: Rust's auto-deref, written out so the
/// state rule places the read where it places `*p` (the pre-Creusot dialect's
/// `self.v == x` is the field `self` is left with). Left on the reference, a
/// field read was the entry value at a call and the final one in the
/// callee's own lane.
fn with_field_reads_dereferenced(clause: &PureExpr, signature: &Signature) -> PureExpr {
    let is_mutable = |name: &str| signature.reference(name) == Some(ParamReference::Mutable);
    if !clause.any_recursive(|node| {
        matches!(node, PureExpr::LogicFnCall { name, args }
            if is_field_projection(name)
                && matches!(args.as_slice(), [PureExpr::Var(param, _)] if is_mutable(param)))
    }) {
        return clause.clone();
    }
    clause
        .rename_binders_apart(is_mutable)
        .rewrite_bottom_up(|node| match node {
            PureExpr::LogicFnCall { name, args }
                if is_field_projection(&name)
                    && matches!(args.as_slice(), [PureExpr::Var(param, _)] if is_mutable(param)) =>
            {
                PureExpr::LogicFnCall {
                    name,
                    args: args
                        .into_iter()
                        .map(|arg| PureExpr::Deref(std::sync::Arc::new(arg)))
                        .collect(),
                }
            }
            node => node,
        })
}

/// A closure-style postcondition, `|r| body` (Creusot's shorthand for a
/// clause over the returned value), as the clause `body[r := result]`. A
/// destructuring parameter is one parameter the parser binds by its pattern,
/// so a closure postcondition has exactly one parameter.
///
/// # Errors
///
/// A closure postcondition of another arity, which has no reading.
pub fn applied_to_the_result(clause: &PureExpr) -> Result<PureExpr, String> {
    match clause {
        PureExpr::Closure { params, body } => {
            let [(param, _)] = params.as_slice() else {
                return Err(format!(
                    "a closure postcondition takes the returned value as its one parameter, and \
                     this one takes {}",
                    params.len()
                ));
            };
            let mut substitutions = HashMap::new();
            substitutions.insert(param.clone(), PureExpr::Var("result".to_string(), None));
            Ok(body.substitute(&substitutions))
        }
        _ => Ok(clause.clone()),
    }
}

/// Whether `clause` is written in the pre-Creusot dialect: it names one of
/// `mut_ref_params` inside `old(..)`.
///
/// Creusot has no `old(..)` on a function-level `&mut` parameter, so a clause
/// naming one there marks the entry value with `old(..)`, and in that clause
/// every bare `*p` (and `p@`) is the post-state: `#[ensures(*a == old(*b))]`
/// on `swap` relates `a`'s post-state to `b`'s entry value, exactly as `*x ==
/// old(*x) + 1` does for `x`. The dialect is a property of the CLAUSE, not of
/// each parameter: reading `*a` there as the entry value turns swap's contract
/// into `entry(a) == entry(b)`, a claim nobody wrote. A clause with no such
/// `old(..)` keeps Creusot's reading, so `#[ensures(result@ == (*r)@)]` over
/// `*r = 5; 5` still states, and fails, `result == entry(*r)`.
#[must_use]
pub fn in_the_old_dialect(clause: &PureExpr, mut_ref_params: &HashSet<String>) -> bool {
    clause.any_recursive(|node| {
        matches!(node, PureExpr::Old(inner)
            if inner.free_vars().iter().any(|var| mut_ref_params.contains(var)))
    })
}

/// `clause` with each read of a `&mut` parameter at the state it denotes:
/// `^p` the value `p` is left with, `*p` (and `old(*p)`) the entry value. A
/// clause in the pre-Creusot dialect ([`in_the_old_dialect`]) reads its bare
/// `*p` and `p@` as `^p` and `(^p)@`, unless it writes `^p` too. Whether `p`
/// is lent into the returned value does not change the reading: a clause
/// whose bare `*p` of a parameter the result may borrow would need it is
/// refused before it gets here ([`place_parameter_reads`]).
#[must_use]
pub fn postcondition_states(clause: &PureExpr, mut_ref_params: &HashSet<String>) -> PureExpr {
    if mut_ref_params.is_empty() {
        return clause.clone();
    }
    if in_the_old_dialect(clause, mut_ref_params) {
        clause.transform_postcondition_for_mut_refs(mut_ref_params)
    } else {
        clause.transform_postcondition_for_mut_refs_keeping_current(mut_ref_params, mut_ref_params)
    }
}

/// A callee's postcondition as a call reads it: the clause the callee's own
/// lane proves ([`applied_to_the_result`], [`place_parameter_reads`],
/// [`postcondition_states`] over the callee's [`Signature`]), with the
/// callee's entry state named by the call's pre-state: `old(e)` over the
/// callee's parameters is `e`, and the arguments substituted for the
/// parameters are their values at the call.
///
/// A clause whose reading differs with the type of a parameter the signature
/// could not read has no one reading here.
///
/// # Errors
///
/// The refusal, described: the clause is then no fact at the call.
pub fn postcondition_at_a_call(
    clause: &PureExpr,
    signature: &Signature,
) -> Result<PureExpr, String> {
    let clause = applied_to_the_result(clause)?;
    let clause = place_parameter_reads(&clause, signature, ClauseKind::Postcondition)?;
    let mut_ref_params = signature.mut_ref_params();
    let read = read_at_the_call(&clause, mut_ref_params);
    if !signature.untyped.is_empty() {
        let widened: HashSet<String> = mut_ref_params.union(&signature.untyped).cloned().collect();
        if read_at_the_call(&clause, &widened) != read {
            return Err(format!(
                "its reading depends on the type of {}, which the call cannot read",
                sorted(&signature.untyped)
            ));
        }
    }
    in_the_pre_state(&read, &|name| signature.has(name))
}

/// `clause` with each `old(e)` over a parameter that is no `&mut` read as
/// the parameter: such a parameter is one value in every state (the body may
/// rebind its own copy, which nothing the clause reads sees), so a subterm of
/// `e` that reads nothing but such parameters (`unchanging`) and names the
/// clause binds around the `old` is its own entry value and is taken out of
/// the `old`, which is split along the operators that hold it. The rest of
/// `e`, and an `old(e)` that reads no such parameter, is left as written.
///
/// The function's lane reads an `old(..)` in the entry state, where a value
/// parameter has no symbol of its own: `old(v@) + 1`, `old(v@ + 1)` and
/// `old(v@ + i)` read a fresh `old_v` unrelated to `v`, and a true
/// `result@ == old(v@) + 1` of `v + 1` was refuted with it.
#[must_use]
pub fn entry_reads_of_unchanging_params(
    clause: &PureExpr,
    unchanging: &dyn Fn(&str) -> bool,
) -> PureExpr {
    let clause_free = clause.free_vars();
    // A name free in the `old` and not in the clause is bound around it.
    let value_only = |name: &String| unchanging(name) || !clause_free.contains(name);
    let reads_a_value_param =
        |node: &PureExpr| node.free_vars().iter().any(|name| unchanging(name));
    let stateless = |node: &PureExpr| {
        !node.any_recursive(|read| {
            matches!(
                read,
                PureExpr::Deref(_) | PureExpr::Final(_) | PureExpr::Old(_)
            )
        }) && node.free_vars().iter().all(value_only)
    };
    clause.rewrite_bottom_up_prune(
        |node| !matches!(node, PureExpr::Old(_)),
        |node| match node {
            PureExpr::Old(inner) if reads_a_value_param(&inner) => {
                out_of_old(&inner, &stateless, &reads_a_value_param)
            }
            node => node,
        },
    )
}

/// `old(node)` with the subterms `stateless` holds of taken out of it: see
/// [`entry_reads_of_unchanging_params`].
fn out_of_old(
    node: &PureExpr,
    stateless: &dyn Fn(&PureExpr) -> bool,
    reads_a_value_param: &dyn Fn(&PureExpr) -> bool,
) -> PureExpr {
    use std::sync::Arc;
    if stateless(node) {
        return node.clone();
    }
    if !reads_a_value_param(node) {
        return PureExpr::Old(Arc::new(node.clone()));
    }
    let split = |child: &PureExpr| out_of_old(child, stateless, reads_a_value_param);
    match node {
        PureExpr::BinOp(left, op, right) => {
            PureExpr::BinOp(Arc::new(split(left)), *op, Arc::new(split(right)))
        }
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, Arc::new(split(inner))),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(split(cond)),
            Arc::new(split(then_expr)),
            Arc::new(split(else_expr)),
        ),
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args.iter().map(split).collect(),
        },
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(split(receiver)),
            method: method.clone(),
            args: args.iter().map(split).collect(),
        },
        node => PureExpr::Old(Arc::new(node.clone())),
    }
}

/// [`postcondition_states`] for a clause in the pre-Creusot dialect. A
/// clause in Creusot's reading already says which state each read is at
/// (`*p` the entry value, `^p` the final one, `p@` the entry view), so the
/// call reads it as written: the rewrite would only respell `p@` as `(*p)@`,
/// which the call's receiver-state lanes match by its written form.
fn read_at_the_call(clause: &PureExpr, mut_ref_params: &HashSet<String>) -> PureExpr {
    if in_the_old_dialect(clause, mut_ref_params) {
        postcondition_states(clause, mut_ref_params)
    } else {
        clause.clone()
    }
}

/// `clause`, read at a call: `old(e)` over the callee's parameters is `e`,
/// since the callee's entry state is the call's pre-state, where the
/// arguments substituted for them are read. A name the call binds to no
/// argument (a closure's capture, whose value before and after the call
/// differ) keeps its `old`, which the lanes reading a capture's states read.
/// An `old(..)` mixing both is split along its operands; one whose state read
/// (`*`, `^`, `@`) itself mixes them has no reading. A final value read in
/// the entry state was refused before ([`first_final_in_the_entry_state`]).
fn in_the_pre_state(
    clause: &PureExpr,
    is_param: &dyn Fn(&str) -> bool,
) -> Result<PureExpr, String> {
    let mut refusal = None;
    clause.for_each_recursive(|node| {
        if refusal.is_some() {
            return;
        }
        if let PureExpr::Old(inner) = node {
            if inner.any_free_var(|name, _| name == "result") {
                refusal = Some(format!(
                    "`{node}` reads the returned value in the entry state, which has no reading"
                ));
            }
        }
    });
    if let Some(refusal) = refusal {
        return Err(refusal);
    }
    let mut refusal = None;
    let read = clause.rewrite_bottom_up_prune(
        |node| !matches!(node, PureExpr::Old(_)),
        |node| match node {
            PureExpr::Old(inner) => match split_old(&inner, is_param) {
                Ok(read) => read,
                Err(reason) => {
                    refusal.get_or_insert(reason);
                    PureExpr::Old(inner)
                }
            },
            node => node,
        },
    );
    match refusal {
        Some(reason) => Err(reason),
        None => Ok(read),
    }
}

/// `old(inner)` with its reads of parameters taken at the call: see
/// [`in_the_pre_state`].
fn split_old(inner: &PureExpr, is_param: &dyn Fn(&str) -> bool) -> Result<PureExpr, String> {
    // Names `inner` binds are neither parameters nor state.
    let mut bound: HashSet<String> = HashSet::new();
    inner.for_each_recursive(|node| match node {
        PureExpr::Let { var, .. } | PureExpr::Forall { var, .. } | PureExpr::Exists { var, .. } => {
            bound.insert(var.clone());
        }
        PureExpr::Closure { params, .. } => {
            bound.extend(params.iter().map(|(name, _)| name.clone()));
        }
        PureExpr::Match { arms, .. } => {
            for arm in arms {
                bound.extend(arm.pattern.bound_names().into_iter().map(str::to_string));
            }
        }
        _ => {}
    });
    let reads = |node: &PureExpr| {
        let names = node.free_vars();
        let params = names.iter().any(|name| is_param(name));
        let others = names
            .iter()
            .any(|name| !is_param(name) && !bound.contains(name));
        (params, others)
    };
    if bound.iter().any(|name| is_param(name)) && reads(inner) == (true, true) {
        return Err(format!(
            "`old({inner})` binds a parameter's name and reads other state, which has no reading \
             at the call"
        ));
    }
    let mut refusal = None;
    let read = inner.rewrite_bottom_up_prune(
        |node| reads(node) == (true, true),
        |node| match reads(&node) {
            (true, true) => {
                if matches!(
                    node,
                    PureExpr::Deref(_) | PureExpr::Final(_) | PureExpr::View(_) | PureExpr::Old(_)
                ) {
                    refusal.get_or_insert_with(|| {
                        format!(
                            "`old({node})` reads a parameter and other state through one \
                             dereference, which has no reading at the call"
                        )
                    });
                }
                node
            }
            (false, true) => PureExpr::Old(std::sync::Arc::new(node)),
            (_, false) => node,
        },
    );
    match refusal {
        Some(reason) => Err(reason),
        None => Ok(read),
    }
}

/// Every name `clause` binds: a quantifier's, a closure's parameters, a
/// `let`'s and a `match` arm's.
fn names_bound_in(clause: &PureExpr) -> HashSet<String> {
    let mut bound = HashSet::new();
    clause.for_each_recursive(|node| match node {
        PureExpr::Let { var, .. } | PureExpr::Forall { var, .. } | PureExpr::Exists { var, .. } => {
            bound.insert(var.clone());
        }
        PureExpr::Closure { params, .. } => {
            bound.extend(params.iter().map(|(name, _)| name.clone()));
        }
        PureExpr::Match { arms, .. } => {
            for arm in arms {
                bound.extend(arm.pattern.bound_names().into_iter().map(str::to_string));
            }
        }
        _ => {}
    });
    bound
}

fn sorted(names: &HashSet<String>) -> String {
    let mut names: Vec<&str> = names.iter().map(String::as_str).collect();
    names.sort_unstable();
    names
        .iter()
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// A signature with every name in `mutable` a `&mut` parameter and every name
/// in `values` an integer, for tests.
#[cfg(test)]
fn signature(mutable: &[&str], values: &[&str]) -> Signature {
    let mut signature = Signature::new();
    for name in mutable {
        signature.insert(*name, Some(ParamReference::Mutable), true);
    }
    for name in values {
        signature.insert(*name, Some(ParamReference::Value), false);
    }
    signature
}

#[cfg(test)]
mod tests {
    use super::{
        applied_to_the_result, place_parameter_reads, postcondition_at_a_call,
        postcondition_states, signature, ClauseKind, ParamReference, Signature,
    };
    use crate::contract_parser::parse_contract;

    fn at_a_call(text: &str, signature: &Signature) -> Result<String, String> {
        let clause = parse_contract(text).expect("parses");
        postcondition_at_a_call(&clause, signature).map(|read| read.to_string())
    }

    /// The clause as the function's own lane reads it: placed as parsed
    /// (`parsing/extraction.rs`), then applied and rewritten
    /// (`contract_transform.rs`).
    fn in_its_lane(text: &str, signature: &Signature) -> Result<String, String> {
        let clause = parse_contract(text).expect("parses");
        let clause = place_parameter_reads(&clause, signature, ClauseKind::Postcondition)?;
        let clause = applied_to_the_result(&clause)?;
        Ok(postcondition_states(&clause, signature.mut_ref_params()).to_string())
    }

    #[test]
    fn a_call_reads_the_old_dialect_as_the_callee_proves_it() {
        let swap = signature(&["a", "b"], &[]);
        assert_eq!(
            at_a_call("*a == old(*b) && *b == old(*a)", &swap).as_deref(),
            Ok("((^a == *b) && (^b == *a))")
        );
        // Creusot's reading is read as written.
        assert_eq!(
            at_a_call("^a == *b && ^b == *a", &swap).as_deref(),
            Ok("((^a == *b) && (^b == *a))")
        );
        assert_eq!(
            at_a_call("(^a)@ == a@", &swap).as_deref(),
            Ok("(^a@ == a@)")
        );
        let replace = signature(&["p"], &["v"]);
        assert_eq!(
            at_a_call("*p == v && result == old(*p)", &replace).as_deref(),
            Ok("((^p == v) && (result == *p))")
        );
        // A binder of the parameter is the parameter.
        assert_eq!(
            at_a_call("match p { q => *q == old(*q) + 1 }", &replace).as_deref(),
            Ok("(^p == (*p + 1))")
        );
        let method = signature(&["self"], &["x"]);
        // A field of the `&mut` parameter is a field of its referent.
        assert_eq!(
            at_a_call("self.v == x && result == old(self.v)", &method).as_deref(),
            Ok("((__trust_wp_field_v(^self) == x) && (result == __trust_wp_field_v(*self)))")
        );
        assert_eq!(
            at_a_call("self.v == x", &method).as_deref(),
            Ok("(__trust_wp_field_v(self) == x)")
        );
    }

    #[test]
    fn a_call_reads_old_in_its_own_pre_state() {
        let get = signature(&["p"], &["v"]);
        assert_eq!(
            at_a_call("result == old(*p)", &get).as_deref(),
            Ok("(result == *p)")
        );
        assert_eq!(
            at_a_call("result == old(v) + 1", &get).as_deref(),
            Ok("(result == (v + 1))")
        );
        assert!(at_a_call("old(^p) == 0", &get).is_err());
        // A name the call binds to no argument (a closure's capture) keeps
        // its `old`: its value before the call is not its value after.
        assert_eq!(
            at_a_call("c == old(c) + 1", &get).as_deref(),
            Ok("(c == (old(c) + 1))")
        );
        assert_eq!(
            at_a_call("result == old(c + v)", &get).as_deref(),
            Ok("(result == (old(c) + v))")
        );
        assert!(at_a_call("old(result) == 0", &get).is_err());
    }

    #[test]
    fn a_closure_postcondition_is_read_of_the_result() {
        let none = Signature::new();
        assert_eq!(
            at_a_call("|r| r == 5", &none).as_deref(),
            Ok("(result == 5)")
        );
    }

    #[test]
    fn a_pre_creusot_read_of_a_lent_final_has_no_reading_in_either_lane() {
        let mut lends = signature(&["p"], &["v"]);
        lends.set_result_may_carry_a_borrow(true);
        // The value `p` is left with is the result's holder's to decide: the
        // function's lane once read `*p` here at entry, which made `*p ==
        // old(*p)` true of `*p = 5; p as *mut i32`, and a call read it as
        // the value after the call.
        for clause in ["*p == old(*p)", "p@ == old(p@)", "|r| *p == old(*p) + r"] {
            assert!(in_its_lane(clause, &lends).is_err(), "{clause}");
            assert!(at_a_call(clause, &lends).is_err(), "{clause}");
        }
        // A clause that says which state it reads is read, alike in both.
        for (clause, read) in [
            ("^p == old(*p) + 1", "(^p == (*p + 1))"),
            ("result == old(*p)", "(result == *p)"),
            ("*p == v", "(*p == v)"),
        ] {
            assert_eq!(at_a_call(clause, &lends).as_deref(), Ok(read), "{clause}");
            assert!(in_its_lane(clause, &lends).is_ok(), "{clause}");
        }
        // A result that cannot borrow lends nothing: the same clause is the
        // value `p` is left with, in both lanes.
        let keeps = signature(&["p"], &[]);
        assert_eq!(
            in_its_lane("*p == old(*p)", &keeps).as_deref(),
            Ok("(^p == old(*p))")
        );
        assert_eq!(
            at_a_call("*p == old(*p)", &keeps).as_deref(),
            Ok("(^p == *p)")
        );
    }

    #[test]
    fn a_final_of_a_parameter_lent_into_another_has_no_reading_in_either_lane() {
        let mut stash = signature(&["p", "slot"], &[]);
        stash.lend_into_a_parameter("p");
        // `stash(p, slot) { *slot = Some(p) }`: whoever holds `slot` after
        // the call decides what `p` is left with, in either dialect.
        for clause in [
            "^p == *p",
            "(^p)@ == 0",
            "*p == old(*p)",
            "^slot == *slot && ^p == *p",
        ] {
            assert!(in_its_lane(clause, &stash).is_err(), "{clause}");
            assert!(at_a_call(clause, &stash).is_err(), "{clause}");
        }
        // Clauses that read no final value of `p` keep their reading.
        for (clause, read) in [
            ("^slot == *slot", "(^slot == *slot)"),
            ("*p == 3", "(*p == 3)"),
        ] {
            assert_eq!(at_a_call(clause, &stash).as_deref(), Ok(read), "{clause}");
            assert!(in_its_lane(clause, &stash).is_ok(), "{clause}");
        }
    }

    #[test]
    fn a_final_written_through_an_interior_mutable_result_has_no_reading() {
        let mut give = signature(&["p"], &[]);
        give.set_result_may_carry_a_borrow(true);
        give.set_result_writes_by_interior_mutability(true);
        // `give(p: &mut Cell<i32>) -> &Cell<i32>`: the result's holder sets
        // the cell, a write no `^result` records.
        for clause in ["^p == *p", "*p == old(*p)"] {
            assert!(in_its_lane(clause, &give).is_err(), "{clause}");
            assert!(at_a_call(clause, &give).is_err(), "{clause}");
        }
        // A `&mut` result is read through its prophecy: `^p` keeps its reading.
        let mut reborrow = signature(&["p"], &[]);
        reborrow.set_result_may_carry_a_borrow(true);
        assert_eq!(
            at_a_call("^p == ^result", &reborrow).as_deref(),
            Ok("(^p == ^result)")
        );
    }

    #[test]
    fn a_final_over_interior_mutable_memory_has_no_reading_in_either_lane() {
        let mut set = signature(&["x", "n"], &[]);
        set.over_interior_mutable_memory("x");
        // `x: &mut Cell<i32>` (or `&mut S` with `S { c: &Cell<i32> }`): a
        // shared reference into the referent writes it, in a loop, through a
        // copy of the reference or in a callee, and no prophecy records it.
        for clause in ["^x == *x", "*x == old(*x)", "^n == *n && ^x == *x"] {
            assert!(in_its_lane(clause, &set).is_err(), "{clause}");
            assert!(at_a_call(clause, &set).is_err(), "{clause}");
        }
        assert_eq!(
            at_a_call("^n == *n + 1", &set).as_deref(),
            Ok("(^n == (*n + 1))")
        );
    }

    /// `unchanged(q) = ^q == *q` and `wrapper(q) = unchanged(q)`, read as the
    /// crate's final readers.
    fn reading_unchanged(signature: &mut Signature) {
        use std::sync::Arc;

        use crate::logic::{final_reads::FinalReaders, LogicFnDef};
        let body = |text: &str| parse_contract(text).expect("parses");
        let defs = [
            LogicFnDef::new(
                "unchanged".to_string(),
                "c::unchanged".to_string(),
                vec!["q".to_string()],
                body("^q == *q"),
            ),
            LogicFnDef::new(
                "wrapper".to_string(),
                "c::wrapper".to_string(),
                vec!["q".to_string()],
                body("unchanged(q)"),
            ),
        ];
        signature.read_finals_through(Arc::new(FinalReaders::reading_in(&defs)));
    }

    /// The final value of `x` (over interior-mutable memory) is refused
    /// however the clause denotes it, not only where it spells `^x`: each of
    /// the `resolve` and binder spellings verified a false claim of a `&mut`
    /// over a copied `&Cell` (D-109).
    #[test]
    fn a_final_decided_elsewhere_has_no_reading_however_denoted() {
        let mut set = signature(&["x", "n"], &[]);
        set.over_interior_mutable_memory("x");
        reading_unchanged(&mut set);
        for clause in [
            "final_value(x) == *x",
            "resolve(x)",
            "structural_resolve(x)",
            "x.resolve()",
            "x.fin() == *x",
            "Resolve::resolve(x)",
            "trust_wp::resolve::resolve(x)",
            "resolve(x) && ^n == *n",
            "resolve((x, 0))",
            "resolve(*x)",
            "!!resolve(x)",
            "if resolve(x) { true } else { false }",
            "{ let t = x; resolve(t) }",
            "match (x, 0) { (q, _) => resolve(q) }",
            "match Some(x) { Some(q) => resolve(q), None => true }",
            "exists<q: &mut Int> q == x && ^q == *q",
            "forall<q: &mut Int> q == x ==> resolve(q)",
            "unchanged(x)",
            "c::wrapper(x)",
            "|r| resolve(x) && r == 0",
        ] {
            assert!(in_its_lane(clause, &set).is_err(), "{clause}");
            assert!(at_a_call(clause, &set).is_err(), "{clause}");
        }
        // A final value of another parameter keeps its reading, and so does a
        // quantified borrow in a clause that names no such parameter.
        for clause in [
            "resolve(n)",
            "^n == *n + 1",
            "unchanged(n)",
            "exists<q: &mut Int> q == n && ^q == *q",
            "*x == 3",
        ] {
            assert!(in_its_lane(clause, &set).is_ok(), "{clause}");
        }
        let mut stash = signature(&["p", "slot"], &[]);
        stash.lend_into_a_parameter("p");
        reading_unchanged(&mut stash);
        for clause in ["resolve(p)", "unchanged(p)", "p.resolve()"] {
            assert!(in_its_lane(clause, &stash).is_err(), "{clause}");
            assert!(at_a_call(clause, &stash).is_err(), "{clause}");
        }
    }

    /// The entry state has no final value: `old(resolve(x))` of `*x = 5`
    /// under `*x != 5` verified in the function's own lane (D-109).
    #[test]
    fn a_final_in_the_entry_state_has_no_reading_in_either_lane() {
        let mut plain = signature(&["x"], &["v"]);
        reading_unchanged(&mut plain);
        for clause in [
            "old(resolve(x))",
            "old(^x == *x)",
            "old(^x) == 5",
            "old(resolve(x) && true)",
            "old(structural_resolve(x))",
            "old(x.resolve())",
            "old(unchanged(x))",
        ] {
            assert!(in_its_lane(clause, &plain).is_err(), "{clause}");
            assert!(at_a_call(clause, &plain).is_err(), "{clause}");
        }
        // A final value read outside `old` keeps its reading.
        assert_eq!(
            at_a_call("resolve(x) && old(*x) == v", &plain).as_deref(),
            Ok("(resolve(*x) && (*x == v))")
        );
    }

    #[test]
    fn a_value_parameter_is_its_own_entry_value() {
        let unchanging = |name: &str| name == "v";
        let read = |text: &str| {
            let clause = parse_contract(text).expect("parses");
            super::entry_reads_of_unchanging_params(&clause, &unchanging).to_string()
        };
        assert_eq!(read("result@ == old(v@) + 1"), "(result@ == (v@ + 1))");
        assert_eq!(read("result@ == old(v@ + 1)"), "(result@ == (v@ + 1))");
        assert_eq!(
            read("forall<i: Int> i == 1 ==> result@ == old(v@ + i)"),
            "forall<i: Int> ((i == 1) ==> (result@ == (v@ + i)))"
        );
        // A read of state stays in the entry state, split from the rest.
        assert_eq!(read("^p == old(*p + v)"), "(^p == (old(*p) + v))");
        // An `old` that reads no value parameter is left as written, and so
        // is a name the clause does not bind (a closure's capture).
        assert_eq!(read("^p == old(*p) + 1"), "(^p == (old(*p) + 1))");
        assert_eq!(read("c == old(c + v)"), "(c == (old(c) + v))");
    }

    #[test]
    fn a_reading_the_call_cannot_decide_is_refused() {
        let mut untyped = Signature::new();
        untyped.insert_untyped("p");
        assert!(at_a_call("*p == old(*p) + 1", &untyped).is_err());
        assert!(at_a_call("result == old(*p)", &untyped).is_ok());
        // A dereference of a value parameter and an unplaced read are refused
        // at the call as in the callee's own lane.
        let value = signature(&[], &["x"]);
        assert!(at_a_call("*x == result", &value).is_err());
        let mut held = Signature::new();
        held.insert("h", Some(ParamReference::HeldMutable), true);
        assert!(at_a_call("*h == old(*h)", &held).is_err());
    }
}
