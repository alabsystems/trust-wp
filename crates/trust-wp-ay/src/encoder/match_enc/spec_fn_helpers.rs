// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort-aware spec function declaration helpers.
//!
//! Provides name-mangling and lookup/declaration for uninterpreted spec functions,
//! constructor testers, and accessor (destructor) functions with sort-polymorphic
//! naming to avoid SMT declaration collisions.

use ay_dpll::api::{FuncDecl, SolverError, Sort};

use super::AYEncoder;

impl AYEncoder {
    fn encode_spec_fn_tag(raw: &str) -> String {
        let mut encoded = String::new();
        for byte in raw.as_bytes() {
            let _ = std::fmt::Write::write_fmt(&mut encoded, format_args!("{byte:02x}"));
        }
        encoded
    }

    fn spec_fn_sort_tag(sort: &Sort) -> String {
        Self::encode_spec_fn_tag(&sort.as_term_sort().to_string())
    }

    fn sort_aware_spec_fn_name(base: &str, domain: &Sort, range: &Sort) -> String {
        let domain = domain.as_term_sort();
        let range = range.as_term_sort();
        format!(
            "{base}__dom_{}__ret_{}",
            Self::spec_fn_sort_tag(&domain),
            Self::spec_fn_sort_tag(&range)
        )
    }

    fn sort_aware_nary_spec_fn_name(base: &str, domains: &[Sort], range: &Sort) -> String {
        let domains = domains.iter().map(Sort::as_term_sort).collect::<Vec<_>>();
        let range = range.as_term_sort();
        let domain_tags = if domains.is_empty() {
            "nullary".to_string()
        } else {
            domains
                .iter()
                .map(Self::spec_fn_sort_tag)
                .collect::<Vec<_>>()
                .join("_")
        };
        format!(
            "{base}__args_{domain_tags}__ret_{}",
            Self::spec_fn_sort_tag(&range)
        )
    }

    /// Get or declare a constructor tester function.
    ///
    /// Constructor testers are uninterpreted functions `T -> Bool` that
    /// determine whether a value was constructed with a particular constructor.
    /// The legacy bare name is preserved for the historical `Int -> Bool` path.
    pub(in crate::encoder) fn get_or_declare_constructor_tester_for_sort(
        &mut self,
        name: &str,
        domain_sort: &Sort,
    ) -> FuncDecl {
        let domain_sort = domain_sort.as_term_sort();
        let decl_name = if domain_sort == Sort::Int {
            name.to_string()
        } else {
            Self::sort_aware_spec_fn_name(name, &domain_sort, &Sort::Bool)
        };
        self.get_or_declare_spec_fn(&decl_name, std::slice::from_ref(&domain_sort), Sort::Bool)
    }

    /// Get or declare a constructor accessor (destructor) function.
    ///
    /// Accessors extract the field value from a datatype constructor.
    /// For example, `option_some_value: Int -> Int` extracts the inner value
    /// from `Some(v)`. The legacy bare name is preserved for the historical
    /// `Int -> Int` path.
    pub(in crate::encoder) fn get_or_declare_accessor_for_sorts(
        &mut self,
        name: &str,
        domain_sort: &Sort,
        range_sort: &Sort,
    ) -> FuncDecl {
        let domain_sort = domain_sort.as_term_sort();
        let range_sort = range_sort.as_term_sort();
        // A native datatype selector occupies its field name globally in ay's
        // function namespace.  An erased receiver can still need an Int-lane
        // UF after that datatype has been declared (for example, `unwrap()`
        // followed by `unwrap_err()` on the same unresolved value).  Preserve
        // the historical bare Int -> Int name only when no native selector has
        // reserved it; otherwise use the deterministic sort-aware spelling.
        let native_selector_uses_name = self.datatypes_iter().any(|datatype| {
            datatype
                .constructors
                .iter()
                .flat_map(|constructor| &constructor.fields)
                .any(|field| field.name == name)
        });
        let reserved_legacy_alias =
            domain_sort == Sort::Int && range_sort == Sort::Int && native_selector_uses_name;
        let decl_name =
            if domain_sort == Sort::Int && range_sort == Sort::Int && !reserved_legacy_alias {
                name.to_string()
            } else {
                Self::sort_aware_spec_fn_name(name, &domain_sort, &range_sort)
            };
        let decl = self.get_or_declare_spec_func(
            &decl_name,
            std::slice::from_ref(&domain_sort),
            range_sort,
        );
        if reserved_legacy_alias {
            // Standard Option/Result axiom discovery uses the historical base
            // registry key. Keep that semantic alias even though the solver
            // symbol itself must be mangled around the native selector.
            self.register_spec_func(name.to_string(), decl.clone());
        }
        decl
    }

    /// Helper: get or declare an uninterpreted spec function.
    #[allow(clippy::needless_pass_by_value)]
    pub(crate) fn get_or_declare_spec_fn(
        &mut self,
        name: &str,
        arg_sorts: &[Sort],
        ret_sort: Sort,
    ) -> FuncDecl {
        let arg_sorts = arg_sorts.iter().map(Sort::as_term_sort).collect::<Vec<_>>();
        let ret_sort = ret_sort.as_term_sort();
        if let Some(existing) = self.spec_func_decl_cloned(name) {
            if existing.domain() == arg_sorts && existing.range() == &ret_sort {
                return existing;
            }
            let collision_name = Self::sort_aware_nary_spec_fn_name(name, &arg_sorts, &ret_sort);
            return self.get_or_declare_spec_func(&collision_name, &arg_sorts, ret_sort);
        }
        let collision_name = Self::sort_aware_nary_spec_fn_name(name, &arg_sorts, &ret_sort);
        if let Some(existing_collision) = self.spec_func_decl_cloned(&collision_name) {
            return existing_collision;
        }
        match self
            .solver
            .try_declare_fun(name, &arg_sorts, ret_sort.clone())
        {
            Ok(decl) => {
                self.register_spec_func(name.to_string(), decl.clone());
                decl
            }
            Err(SolverError::InvalidArgument {
                operation: "declare_fun",
                ref message,
            }) if message.contains("already in use") => {
                // Native datatype members share AY's function namespace.  A
                // built-in selector such as `result_err_error : ResultIntInt
                // -> Int` can therefore already own the legacy bare name when
                // the fallback lane needs an unrelated `Int -> Int` UF.  AY
                // deliberately rejects that overload because a name is the
                // native declaration identity.  Preserve the surface registry
                // key while giving the fallback declaration a signature-bound
                // native identity.
                let collision_name =
                    Self::sort_aware_nary_spec_fn_name(name, &arg_sorts, &ret_sort);
                let decl = self.get_or_declare_spec_func(&collision_name, &arg_sorts, ret_sort);
                self.register_spec_func(name.to_string(), decl.clone());
                decl
            }
            Err(error) => panic!("failed to declare internal spec function `{name}`: {error}"),
        }
    }
}
