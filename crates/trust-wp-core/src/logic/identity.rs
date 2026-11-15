// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic-function identity: one solver symbol per Rust definition.
//!
//! Logic functions used to be keyed by their bare short name end to end, so
//! `a::k` and `b::k` (or `<A as Tr>::m` and `<B as Tr>::m`) shared one solver
//! symbol and the first-registered definition's axiom answered for all of
//! them. The driver now gives every member of a short-name collision a unique
//! id (derived from its crate-qualified def path) and installs the collision
//! families here, so the encoder can
//!
//! - resolve a receiver-style call (`x.m()`) to exactly one member, or to the
//!   trait declaration when the receiver's concrete impl is not certain, and
//! - refuse (encoding error) any use of a colliding short name it cannot
//!   resolve, instead of silently binding it to whichever member came first.

use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, RwLock},
};

use crate::formula::ExprSort;

/// Prefix of every unique logic-function id minted for a collision member.
pub const LOGIC_FN_ID_PREFIX: &str = "__lfid__";

/// Prefix of the opaque declaration symbol that stands for a method of an
/// EXTERNAL trait (no local declaration) at a receiver whose impl is not
/// certain. It never carries an axiom.
pub const LOGIC_FN_EXTERN_DECL_PREFIX: &str = "__lfid__extern__";

/// Where a logic function is defined.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicFnOwnerKind {
    /// Free function in a module.
    Free,
    /// Associated function of an inherent impl.
    Inherent,
    /// Item of a trait declaration (with or without a default body).
    TraitDecl,
    /// Item of a trait impl.
    TraitImpl,
}

/// One definition sharing its short name with at least one other definition.
// Each Boolean records an independent compiler-observed dispatch or default-body
// fact; keeping those facts separate preserves the identity record's public API.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogicFnFamilyMember {
    /// The unique id: the `LogicFnDef::name` of this definition.
    pub id: String,
    /// Crate-qualified def path (display).
    pub full_path: String,
    /// The shared short name.
    pub short_name: String,
    pub kind: LogicFnOwnerKind,
    /// Crate-qualified path of the trait (`TraitDecl` / `TraitImpl`).
    pub trait_path: Option<String>,
    /// For impls: the sort of the impl self type when it is NOMINAL, i.e. a
    /// local ADT whose solver sort can only come from that ADT. `None` for
    /// primitives, tuples, references, type parameters and anything else.
    pub nominal_self_sort: Option<ExprSort>,
    /// The first parameter has type `Self` (receiver-style dispatch).
    pub receiver_is_self: bool,
    /// `TraitDecl` only: the declaration carries a visible default body.
    pub decl_has_visible_body: bool,
    /// For impls: Rust's method lookup of this name at the impl's self type
    /// can select no method but this one, so a receiver of that nominal sort
    /// may be dispatched to it. `false` where an inherent program method, a
    /// trait default, or another trait's method of the name could apply
    /// (method_call_untyped_receiver_*_granted.rs).
    pub receiver_dispatch: bool,
    /// `TraitDecl` only: the declaration has a default body and some impl of
    /// its trait does not define the method, so at that impl's self type the
    /// callee is the default, which no impl member of the family stands for.
    pub decl_default_runs: bool,
    /// Number of parameters (a call with a different argument count cannot
    /// denote this definition).
    pub arity: usize,
}

/// All collision families of the crate under verification.
#[derive(Debug, Default)]
pub struct LogicFnIdentityRegistry {
    families: HashMap<String, Vec<LogicFnFamilyMember>>,
    ids: HashSet<String>,
    by_full_path: HashMap<String, String>,
}

impl LogicFnIdentityRegistry {
    /// Build a registry from collision members (grouped by short name).
    #[must_use]
    pub fn new(members: Vec<LogicFnFamilyMember>) -> Self {
        let mut registry = Self::default();
        for member in members {
            registry.ids.insert(member.id.clone());
            registry
                .by_full_path
                .insert(member.full_path.clone(), member.id.clone());
            registry
                .families
                .entry(member.short_name.clone())
                .or_default()
                .push(member);
        }
        registry
    }

    /// The family sharing `short_name`, if that name collides.
    #[must_use]
    pub fn family(&self, short_name: &str) -> Option<&[LogicFnFamilyMember]> {
        self.families.get(short_name).map(Vec::as_slice)
    }

    /// Whether `name` is a minted unique id.
    #[must_use]
    pub fn is_id(&self, name: &str) -> bool {
        self.ids.contains(name)
    }

    /// The unique id of the collision member with this crate-qualified path.
    #[must_use]
    pub fn id_for_full_path(&self, full_path: &str) -> Option<&str> {
        self.by_full_path.get(full_path).map(String::as_str)
    }

    /// The member with this id.
    #[must_use]
    pub fn member(&self, id: &str) -> Option<&LogicFnFamilyMember> {
        if !self.ids.contains(id) {
            return None;
        }
        self.families
            .values()
            .flatten()
            .find(|member| member.id == id)
    }

    /// The colliding family a call NAME refers to when it is not itself a
    /// resolved id: `m`, `Self::m`, `T::m`, `a::b::m`, `<A as Tr>::m`.
    #[must_use]
    pub fn unresolved_family_for_call(&self, name: &str) -> Option<&[LogicFnFamilyMember]> {
        if name.starts_with(LOGIC_FN_ID_PREFIX)
            || is_refused_logic_fn_marker(name)
            || self.ids.contains(name)
        {
            return None;
        }
        self.family(logic_fn_short_name(name))
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.families.is_empty()
    }
}

static REGISTRY: RwLock<Option<Arc<LogicFnIdentityRegistry>>> = RwLock::new(None);

/// Install the collision families of the crate under verification.
pub fn install_logic_fn_identity_registry(registry: LogicFnIdentityRegistry) {
    let mut guard = REGISTRY
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    *guard = Some(Arc::new(registry));
}

/// Remove the installed registry (tests).
pub fn clear_logic_fn_identity_registry() {
    let mut guard = REGISTRY
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    *guard = None;
}

/// The installed registry, if any.
#[must_use]
pub fn logic_fn_identity_registry() -> Option<Arc<LogicFnIdentityRegistry>> {
    REGISTRY
        .read()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone()
}

/// Last `::` segment of a (possibly qualified) logic-function call name.
#[must_use]
pub fn logic_fn_short_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

fn encode_identity_component(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len() + 8);
    for ch in raw.chars() {
        match ch {
            '_' => out.push_str("__"),
            ch if ch.is_ascii_alphanumeric() => out.push(ch),
            ':' => out.push_str("_P_"),
            '<' => out.push_str("_LT_"),
            '>' => out.push_str("_GT_"),
            ',' => out.push_str("_C_"),
            ' ' => out.push_str("_S_"),
            '&' => out.push_str("_R_"),
            '(' => out.push_str("_LP_"),
            ')' => out.push_str("_RP_"),
            '[' => out.push_str("_LB_"),
            ']' => out.push_str("_RB_"),
            other => {
                use std::fmt::Write;
                let _ = write!(out, "_x{:02X}_", other as u32);
            }
        }
    }
    out
}

/// The unique id of a logic function defined at `full_path`
/// (crate-qualified def path). Injective in `full_path`.
#[must_use]
pub fn logic_fn_unique_id(full_path: &str) -> String {
    format!(
        "{LOGIC_FN_ID_PREFIX}{}",
        encode_identity_component(full_path)
    )
}

/// The opaque declaration symbol of `short_name` in the EXTERNAL trait at
/// `trait_path`.
#[must_use]
pub fn logic_fn_extern_decl_id(trait_path: &str, short_name: &str) -> String {
    format!(
        "{LOGIC_FN_EXTERN_DECL_PREFIX}{}",
        encode_identity_component(&format!("{trait_path}::{short_name}"))
    )
}

/// Prefix of a call name the driver could not resolve to one definition. The
/// encoder refuses every call spelled with it (never an unconstrained UF).
pub const LOGIC_FN_UNRESOLVED_PREFIX: &str = "__lfidU__";

/// Prefix of a call name standing for a trait logic method at a GENERIC
/// receiver of a callee contract; call sites re-resolve it against the call's
/// generic arguments. Reaching the encoder unresolved is refused.
pub const LOGIC_FN_GENERIC_PREFIX: &str = "__lfidG__";

/// The refusal marker for a call to the colliding short name `short`.
#[must_use]
pub fn logic_fn_unresolved_marker(short: &str) -> String {
    format!(
        "{LOGIC_FN_UNRESOLVED_PREFIX}{}",
        encode_identity_component(short)
    )
}

/// Whether `name` is a marker the encoder must refuse.
#[must_use]
pub fn is_refused_logic_fn_marker(name: &str) -> bool {
    name.starts_with(LOGIC_FN_UNRESOLVED_PREFIX) || name.starts_with(LOGIC_FN_GENERIC_PREFIX)
}

/// Whether a call of `family` with `arity` arguments is one the encoder reads
/// by its first argument's sort ([`resolve_family_by_receiver`]): every
/// definition of that arity is a method. The driver asks exactly this before
/// it leaves a call under its written name, so a bare call the scopes bind to
/// no logic definition is never handed to the dispatch
/// (bare_call_mixed_arity_family_*_granted.rs, where a free definition of
/// ANOTHER arity made the driver read the call as a free one).
#[must_use]
pub fn dispatches_on_receiver(family: &[LogicFnFamilyMember], arity: usize) -> bool {
    let mut same_arity = family
        .iter()
        .filter(|member| member.arity == arity)
        .peekable();
    same_arity.peek().is_some() && same_arity.all(|member| member.receiver_is_self)
}

/// Resolve a receiver-style call to one member of a collision family from the
/// SOLVER SORT of the receiver alone.
///
/// `receiver_has_sort(sort)` must answer whether the ENCODED receiver has
/// exactly the solver sort of `sort`.
///
/// The only rule: when every impl member has a nominal self sort (a local ADT
/// whose solver sort nothing else shares) and exactly one of them has the
/// receiver's sort, that impl is the callee. Anything else is refused. In
/// particular the trait-declaration symbol is NEVER chosen here: it denotes
/// the method at an abstract `Self`, and using it for a receiver whose type is
/// merely unknown to the encoder conflates impls whose receivers share a
/// solver sort (`u32`/`u64`, newtypes erased to `Int`, instantiations of a
/// generic callee contract). The driver resolves generic receivers.
///
/// # Errors
/// A message naming the family when the rule does not apply.
pub fn resolve_family_by_receiver(
    family: &[LogicFnFamilyMember],
    arity: usize,
    receiver_has_sort: impl Fn(&ExprSort) -> bool,
) -> Result<String, String> {
    // A definition with a different parameter count is never the callee.
    let same_arity: Vec<&LogicFnFamilyMember> = family
        .iter()
        .filter(|member| member.arity == arity)
        .collect();
    let short = family
        .first()
        .map_or("<empty>", |member| member.short_name.as_str());
    let paths = || {
        family
            .iter()
            .map(|member| member.full_path.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    };
    if !dispatches_on_receiver(family, arity) {
        return Err(format!(
            "call to logic function `{short}` is ambiguous between {} and was not resolved to one definition",
            paths()
        ));
    }
    // A trait default that runs at some impl is the callee at that impl's self
    // type, and no impl member carries its sort: matching the receiver's sort
    // against the impl members alone would bind another trait's method where
    // Rust runs the default.
    if same_arity.iter().any(|member| member.decl_default_runs) {
        return Err(format!(
            "receiver-style call to logic function `{short}` may be a trait's default body \
             beside {} (the receiver's type is not known here)",
            paths()
        ));
    }
    let impls: Vec<&&LogicFnFamilyMember> = same_arity
        .iter()
        .filter(|member| {
            matches!(
                member.kind,
                LogicFnOwnerKind::TraitImpl | LogicFnOwnerKind::Inherent
            )
        })
        .collect();
    if !impls.is_empty()
        && impls
            .iter()
            .all(|member| member.nominal_self_sort.is_some())
    {
        let matches: Vec<&&&LogicFnFamilyMember> = impls
            .iter()
            .filter(|member| {
                member
                    .nominal_self_sort
                    .as_ref()
                    .is_some_and(&receiver_has_sort)
            })
            .collect();
        match matches.as_slice() {
            [only] if only.receiver_dispatch => return Ok(only.id.clone()),
            [only] => {
                return Err(format!(
                    "receiver-style call to logic function `{short}` would select `{}`, but \
                     Rust's method lookup on that receiver may select another method named \
                     `{short}`",
                    only.full_path
                ))
            }
            [] => {}
            _ => {
                return Err(format!(
                    "receiver-style call to logic function `{short}` matches several impls ({})",
                    paths()
                ))
            }
        }
    }
    Err(format!(
        "receiver-style call to logic function `{short}` was not resolved to one of {} \
         (the receiver's type is not known here)",
        paths()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::intern_sort_name;

    fn member(
        path: &str,
        kind: LogicFnOwnerKind,
        trait_path: Option<&str>,
        nominal: Option<&str>,
    ) -> LogicFnFamilyMember {
        LogicFnFamilyMember {
            id: logic_fn_unique_id(path),
            full_path: path.to_string(),
            short_name: logic_fn_short_name(path).to_string(),
            kind,
            trait_path: trait_path.map(str::to_string),
            nominal_self_sort: nominal.map(|n| ExprSort::Datatype(intern_sort_name(n))),
            receiver_is_self: true,
            decl_has_visible_body: false,
            receiver_dispatch: true,
            decl_default_runs: false,
            arity: 1,
        }
    }

    fn trait_family() -> Vec<LogicFnFamilyMember> {
        vec![
            member("c::Tr::m", LogicFnOwnerKind::TraitDecl, Some("c::Tr"), None),
            member(
                "c::<A as Tr>::m",
                LogicFnOwnerKind::TraitImpl,
                Some("c::Tr"),
                Some("A"),
            ),
            member(
                "c::<B as Tr>::m",
                LogicFnOwnerKind::TraitImpl,
                Some("c::Tr"),
                Some("B"),
            ),
        ]
    }

    fn is(name: &'static str) -> impl Fn(&ExprSort) -> bool {
        move |sort| matches!(sort, ExprSort::Datatype(id) if *id == intern_sort_name(name))
    }

    #[test]
    fn unique_ids_are_injective_and_distinct() {
        assert_ne!(logic_fn_unique_id("c::a::k"), logic_fn_unique_id("c::b::k"));
        assert_ne!(
            logic_fn_unique_id("c::a_b::k"),
            logic_fn_unique_id("c::a::b::k")
        );
        assert!(logic_fn_unique_id("c::a::k").starts_with(LOGIC_FN_ID_PREFIX));
    }

    #[test]
    fn nominal_receiver_selects_its_impl() {
        let family = trait_family();
        assert_eq!(
            resolve_family_by_receiver(&family, 1, is("B")),
            Ok(logic_fn_unique_id("c::<B as Tr>::m"))
        );
        assert_eq!(
            resolve_family_by_receiver(&family, 1, is("A")),
            Ok(logic_fn_unique_id("c::<A as Tr>::m"))
        );
    }

    #[test]
    fn unknown_receiver_is_refused() {
        let family = trait_family();
        assert!(resolve_family_by_receiver(&family, 1, |_| false).is_err());
    }

    #[test]
    fn visible_default_body_is_never_used_for_an_uncertain_receiver() {
        let mut family = trait_family();
        family[0].decl_has_visible_body = true;
        assert!(resolve_family_by_receiver(&family, 1, |_| false).is_err());
        // A certain impl is still fine.
        assert!(resolve_family_by_receiver(&family, 1, is("A")).is_ok());
    }

    /// Where some impl of the trait does not define the method, the default is
    /// the callee at that impl's self type, and no impl member has its sort:
    /// the receiver's sort matching one impl is no answer then.
    #[test]
    fn a_default_that_runs_at_some_impl_blocks_sort_selection() {
        let mut family = trait_family();
        family[0].decl_default_runs = true;
        assert!(resolve_family_by_receiver(&family, 1, is("A")).is_err());
        assert!(resolve_family_by_receiver(&family, 1, is("B")).is_err());
    }

    #[test]
    fn non_nominal_impl_blocks_sort_selection() {
        let mut family = trait_family();
        family.push(member(
            "c::<Box<T> as Tr>::m",
            LogicFnOwnerKind::TraitImpl,
            Some("c::Tr"),
            None,
        ));
        assert!(resolve_family_by_receiver(&family, 1, is("A")).is_err());
    }

    #[test]
    fn same_sort_impls_are_ambiguous() {
        let family = vec![
            member("c::Tr::m", LogicFnOwnerKind::TraitDecl, Some("c::Tr"), None),
            member(
                "c::<A<u8> as Tr>::m",
                LogicFnOwnerKind::TraitImpl,
                Some("c::Tr"),
                Some("A"),
            ),
            member(
                "c::<A<i8> as Tr>::m",
                LogicFnOwnerKind::TraitImpl,
                Some("c::Tr"),
                Some("A"),
            ),
        ];
        assert!(resolve_family_by_receiver(&family, 1, is("A")).is_err());
        assert!(resolve_family_by_receiver(&family, 1, is("Z")).is_err());
    }

    #[test]
    fn external_trait_without_declaration_is_refused_at_unknown_receiver() {
        let family = vec![
            member(
                "c::<A as View>::view",
                LogicFnOwnerKind::TraitImpl,
                Some("s::View"),
                Some("A"),
            ),
            member(
                "c::<B as View>::view",
                LogicFnOwnerKind::TraitImpl,
                Some("s::View"),
                Some("B"),
            ),
        ];
        assert!(resolve_family_by_receiver(&family, 1, |_| false).is_err());
        assert_eq!(
            resolve_family_by_receiver(&family, 1, is("B")),
            Ok(logic_fn_unique_id("c::<B as View>::view"))
        );
    }

    #[test]
    fn arity_separates_families_of_different_traits() {
        let mut family = vec![
            member(
                "c::T1::inv",
                LogicFnOwnerKind::TraitDecl,
                Some("c::T1"),
                None,
            ),
            member(
                "c::<A as T1>::inv",
                LogicFnOwnerKind::TraitImpl,
                Some("c::T1"),
                Some("A"),
            ),
            member(
                "c::T2::inv",
                LogicFnOwnerKind::TraitDecl,
                Some("c::T2"),
                None,
            ),
            member(
                "c::<B as T2>::inv",
                LogicFnOwnerKind::TraitImpl,
                Some("c::T2"),
                Some("B"),
            ),
        ];
        family[2].arity = 2;
        family[3].arity = 2;
        assert_eq!(
            resolve_family_by_receiver(&family, 1, is("A")),
            Ok(logic_fn_unique_id("c::<A as T1>::inv"))
        );
        assert_eq!(
            resolve_family_by_receiver(&family, 2, is("B")),
            Ok(logic_fn_unique_id("c::<B as T2>::inv"))
        );
        // `B` has no arity-1 impl.
        assert!(resolve_family_by_receiver(&family, 1, is("B")).is_err());
        assert!(resolve_family_by_receiver(&family, 3, |_| true).is_err());
    }

    /// The driver leaves a call under its written name only where this says
    /// the encoder refuses it: a free definition of ANOTHER arity does not
    /// make a call of methods' arity a free call
    /// (bare_call_mixed_arity_family_*_granted.rs).
    #[test]
    fn dispatch_asks_only_the_definitions_of_the_call_s_arity() {
        let mut family = vec![
            member("c::S::m", LogicFnOwnerKind::Inherent, None, Some("S")),
            member("c::other::m", LogicFnOwnerKind::Free, None, None),
        ];
        family[1].receiver_is_self = false;
        family[1].arity = 2;
        assert!(dispatches_on_receiver(&family, 1));
        assert!(!dispatches_on_receiver(&family, 2));
        assert!(!dispatches_on_receiver(&family, 3));
        family[1].arity = 1;
        assert!(!dispatches_on_receiver(&family, 1));
        assert!(resolve_family_by_receiver(&family, 1, is("S")).is_err());
    }

    #[test]
    fn markers_are_refused_and_distinct_from_ids() {
        assert!(is_refused_logic_fn_marker(&logic_fn_unresolved_marker("m")));
        assert!(!is_refused_logic_fn_marker(&logic_fn_unique_id("c::a::m")));
    }

    #[test]
    fn free_and_mixed_families_are_refused() {
        let mut free = vec![
            member("c::a::k", LogicFnOwnerKind::Free, None, None),
            member("c::b::k", LogicFnOwnerKind::Free, None, None),
        ];
        assert!(resolve_family_by_receiver(&free, 1, |_| true).is_err());
        free[0].receiver_is_self = false;
        assert!(resolve_family_by_receiver(&free, 1, |_| true).is_err());
        let two_traits = vec![
            member(
                "c::<A as T1>::m",
                LogicFnOwnerKind::TraitImpl,
                Some("c::T1"),
                None,
            ),
            member(
                "c::<A as T2>::m",
                LogicFnOwnerKind::TraitImpl,
                Some("c::T2"),
                None,
            ),
        ];
        assert!(resolve_family_by_receiver(&two_traits, 1, |_| true).is_err());
    }
}
