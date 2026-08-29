// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Iterator-related std-spec entries.

use trust_wp_std::std::{iter, ops};

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    // RangeInclusive::new — constructor used by `start..=end` desugaring.
    (
        &[
            "core::ops::range::RangeInclusive::new",
            "core::ops::RangeInclusive::new",
            "std::ops::range::RangeInclusive::new",
            "std::ops::RangeInclusive::new",
        ],
        ops::specs::RANGE_INCLUSIVE_NEW,
    ),
    (
        &[
            "core::iter::traits::iterator::Iterator::next",
            "std::iter::traits::iterator::Iterator::next",
            // UFCS paths for concrete iterator type impls (#2238).
            // Post-borrowck MIR may resolve to the concrete impl rather
            // than the trait default method.
            "<core::slice::iter::IterMut as core::iter::Iterator>::next",
            "<core::slice::iter::IterMut as std::iter::Iterator>::next",
            "<core::slice::IterMut as core::iter::Iterator>::next",
            "<core::slice::IterMut as std::iter::Iterator>::next",
            "<std::slice::IterMut as core::iter::Iterator>::next",
            "<std::slice::IterMut as std::iter::Iterator>::next",
            "<core::slice::iter::Iter as core::iter::Iterator>::next",
            "<core::slice::iter::Iter as std::iter::Iterator>::next",
            "<core::slice::Iter as core::iter::Iterator>::next",
            "<core::slice::Iter as std::iter::Iterator>::next",
            "<std::slice::Iter as core::iter::Iterator>::next",
            "<std::slice::Iter as std::iter::Iterator>::next",
            "<alloc::vec::into_iter::IntoIter as core::iter::Iterator>::next",
            "<alloc::vec::into_iter::IntoIter as std::iter::Iterator>::next",
            "<std::vec::IntoIter as core::iter::Iterator>::next",
            "<std::vec::IntoIter as std::iter::Iterator>::next",
            // UFCS paths for iterator adapter types (#2688).
            // Post-borrowck MIR resolves `next()` on adapter types to the
            // concrete adapter impl rather than the trait method. Without
            // these entries, adapter `next()` calls fall through to the
            // opaque-call path, losing the produces/completed spec.
            "<core::iter::adapters::map::Map as core::iter::Iterator>::next",
            "<core::iter::adapters::map::Map as std::iter::Iterator>::next",
            "<std::iter::Map as core::iter::Iterator>::next",
            "<std::iter::Map as std::iter::Iterator>::next",
            "<core::iter::adapters::filter::Filter as core::iter::Iterator>::next",
            "<core::iter::adapters::filter::Filter as std::iter::Iterator>::next",
            "<std::iter::Filter as core::iter::Iterator>::next",
            "<std::iter::Filter as std::iter::Iterator>::next",
            "<core::iter::adapters::filter_map::FilterMap as core::iter::Iterator>::next",
            "<core::iter::adapters::filter_map::FilterMap as std::iter::Iterator>::next",
            "<std::iter::FilterMap as core::iter::Iterator>::next",
            "<std::iter::FilterMap as std::iter::Iterator>::next",
            "<core::iter::adapters::enumerate::Enumerate as core::iter::Iterator>::next",
            "<core::iter::adapters::enumerate::Enumerate as std::iter::Iterator>::next",
            "<std::iter::Enumerate as core::iter::Iterator>::next",
            "<std::iter::Enumerate as std::iter::Iterator>::next",
            "<core::iter::adapters::skip::Skip as core::iter::Iterator>::next",
            "<core::iter::adapters::skip::Skip as std::iter::Iterator>::next",
            "<std::iter::Skip as core::iter::Iterator>::next",
            "<std::iter::Skip as std::iter::Iterator>::next",
            "<core::iter::adapters::take::Take as core::iter::Iterator>::next",
            "<core::iter::adapters::take::Take as std::iter::Iterator>::next",
            "<std::iter::Take as core::iter::Iterator>::next",
            "<std::iter::Take as std::iter::Iterator>::next",
            "<core::iter::adapters::zip::Zip as core::iter::Iterator>::next",
            "<core::iter::adapters::zip::Zip as std::iter::Iterator>::next",
            "<std::iter::Zip as core::iter::Iterator>::next",
            "<std::iter::Zip as std::iter::Iterator>::next",
            "<core::iter::adapters::chain::Chain as core::iter::Iterator>::next",
            "<core::iter::adapters::chain::Chain as std::iter::Iterator>::next",
            "<std::iter::Chain as core::iter::Iterator>::next",
            "<std::iter::Chain as std::iter::Iterator>::next",
            "<core::iter::adapters::fuse::Fuse as core::iter::Iterator>::next",
            "<core::iter::adapters::fuse::Fuse as std::iter::Iterator>::next",
            "<std::iter::Fuse as core::iter::Iterator>::next",
            "<std::iter::Fuse as std::iter::Iterator>::next",
            "<core::iter::adapters::cloned::Cloned as core::iter::Iterator>::next",
            "<core::iter::adapters::cloned::Cloned as std::iter::Iterator>::next",
            "<std::iter::Cloned as core::iter::Iterator>::next",
            "<std::iter::Cloned as std::iter::Iterator>::next",
            "<core::iter::adapters::copied::Copied as core::iter::Iterator>::next",
            "<core::iter::adapters::copied::Copied as std::iter::Iterator>::next",
            "<std::iter::Copied as core::iter::Iterator>::next",
            "<std::iter::Copied as std::iter::Iterator>::next",
            "<core::iter::adapters::rev::Rev as core::iter::Iterator>::next",
            "<core::iter::adapters::rev::Rev as std::iter::Iterator>::next",
            "<std::iter::Rev as core::iter::Iterator>::next",
            "<std::iter::Rev as std::iter::Iterator>::next",
            "<core::iter::adapters::peekable::Peekable as core::iter::Iterator>::next",
            "<core::iter::adapters::peekable::Peekable as std::iter::Iterator>::next",
            "<std::iter::Peekable as core::iter::Iterator>::next",
            "<std::iter::Peekable as std::iter::Iterator>::next",
            // MapInv adapter (trust-wp-specific) (#2688)
            "<trust_wp_std::std::iter::map_inv::MapInv as core::iter::Iterator>::next",
            "<trust_wp_std::std::iter::MapInv as core::iter::Iterator>::next",
            "<creusot_std::std::iter::MapInv as core::iter::Iterator>::next",
            "<creusot_std::MapInv as core::iter::Iterator>::next",
            // Normalized form: creusot_std::MapInv → trust_wp_std::MapInv (#2689)
            "<trust_wp_std::MapInv as core::iter::Iterator>::next",
            // Range iterator (#2688)
            "<core::ops::range::Range as core::iter::Iterator>::next",
            // `std::ops::Range` normalizes to `core::ops::Range` (missing `range::`)
            "<core::ops::Range as core::iter::Iterator>::next",
            "<std::ops::Range as core::iter::Iterator>::next",
            "<core::ops::Range as std::iter::Iterator>::next",
            "<std::ops::Range as std::iter::Iterator>::next",
            // ── Additional iterator adapter UFCS paths (#2689) ────────────
            // FlatMap adapter
            "<core::iter::adapters::flatten::FlatMap as core::iter::Iterator>::next",
            "<core::iter::adapters::flatten::FlatMap as std::iter::Iterator>::next",
            "<std::iter::FlatMap as core::iter::Iterator>::next",
            "<std::iter::FlatMap as std::iter::Iterator>::next",
            // Inspect adapter
            "<core::iter::adapters::inspect::Inspect as core::iter::Iterator>::next",
            "<core::iter::adapters::inspect::Inspect as std::iter::Iterator>::next",
            "<std::iter::Inspect as core::iter::Iterator>::next",
            "<std::iter::Inspect as std::iter::Iterator>::next",
            // StepBy adapter
            "<core::iter::adapters::step_by::StepBy as core::iter::Iterator>::next",
            "<core::iter::adapters::step_by::StepBy as std::iter::Iterator>::next",
            "<std::iter::StepBy as core::iter::Iterator>::next",
            "<std::iter::StepBy as std::iter::Iterator>::next",
            // TakeWhile adapter
            "<core::iter::adapters::take_while::TakeWhile as core::iter::Iterator>::next",
            "<core::iter::adapters::take_while::TakeWhile as std::iter::Iterator>::next",
            "<std::iter::TakeWhile as core::iter::Iterator>::next",
            "<std::iter::TakeWhile as std::iter::Iterator>::next",
            // SkipWhile adapter
            "<core::iter::adapters::skip_while::SkipWhile as core::iter::Iterator>::next",
            "<core::iter::adapters::skip_while::SkipWhile as std::iter::Iterator>::next",
            "<std::iter::SkipWhile as core::iter::Iterator>::next",
            "<std::iter::SkipWhile as std::iter::Iterator>::next",
            // MapWhile adapter
            "<core::iter::adapters::map_while::MapWhile as core::iter::Iterator>::next",
            "<core::iter::adapters::map_while::MapWhile as std::iter::Iterator>::next",
            "<std::iter::MapWhile as core::iter::Iterator>::next",
            "<std::iter::MapWhile as std::iter::Iterator>::next",
            // Scan adapter
            "<core::iter::adapters::scan::Scan as core::iter::Iterator>::next",
            "<core::iter::adapters::scan::Scan as std::iter::Iterator>::next",
            "<std::iter::Scan as core::iter::Iterator>::next",
            "<std::iter::Scan as std::iter::Iterator>::next",
            // Flatten adapter
            "<core::iter::adapters::flatten::Flatten as core::iter::Iterator>::next",
            "<core::iter::adapters::flatten::Flatten as std::iter::Iterator>::next",
            "<std::iter::Flatten as core::iter::Iterator>::next",
            "<std::iter::Flatten as std::iter::Iterator>::next",
            // RangeInclusive iterator (#2689)
            "<core::ops::range::RangeInclusive as core::iter::Iterator>::next",
            "<core::ops::RangeInclusive as core::iter::Iterator>::next",
            "<std::ops::RangeInclusive as core::iter::Iterator>::next",
            "<core::ops::RangeInclusive as std::iter::Iterator>::next",
            "<std::ops::RangeInclusive as std::iter::Iterator>::next",
        ],
        iter::specs::ITERATOR_NEXT,
    ),
    (
        &[
            "alloc::vec::Vec::iter",
            "std::vec::Vec::iter",
            "core::slice::iter",
            "std::slice::iter",
            "core::slice::<impl [T]>::iter",
            // &Vec / &[T] IntoIterator — `for x in &vec {}` desugars to this.
            "<&alloc::vec::Vec as core::iter::IntoIterator>::into_iter",
            "<&std::vec::Vec as core::iter::IntoIterator>::into_iter",
            "<&alloc::vec::Vec as std::iter::IntoIterator>::into_iter",
            "<&std::vec::Vec as std::iter::IntoIterator>::into_iter",
            "<&[T] as core::iter::IntoIterator>::into_iter",
            "<&[T] as std::iter::IntoIterator>::into_iter",
        ],
        iter::specs::VEC_ITER,
    ),
    (
        &[
            "alloc::vec::Vec::iter_mut",
            "std::vec::Vec::iter_mut",
            "core::slice::iter_mut",
            "std::slice::iter_mut",
            "core::slice::<impl [T]>::iter_mut",
            // &mut Vec / &mut [T] IntoIterator — `for x in &mut vec {}` desugars
            // to `<&mut Vec as IntoIterator>::into_iter`, producing IterMut. (#2238)
            "<&mut alloc::vec::Vec as core::iter::IntoIterator>::into_iter",
            "<&mut std::vec::Vec as core::iter::IntoIterator>::into_iter",
            "<&mut alloc::vec::Vec as std::iter::IntoIterator>::into_iter",
            "<&mut std::vec::Vec as std::iter::IntoIterator>::into_iter",
            "<&mut [T] as core::iter::IntoIterator>::into_iter",
            "<&mut [T] as std::iter::IntoIterator>::into_iter",
        ],
        iter::specs::VEC_ITER_MUT,
    ),
    (
        &[
            "alloc::vec::Vec::into_iter",
            "std::vec::Vec::into_iter",
            "<alloc::vec::Vec as core::iter::IntoIterator>::into_iter",
            "<std::vec::Vec as core::iter::IntoIterator>::into_iter",
            "<alloc::vec::Vec as std::iter::IntoIterator>::into_iter",
            "<std::vec::Vec as std::iter::IntoIterator>::into_iter",
        ],
        iter::specs::VEC_INTO_ITER,
    ),
    // Range<T> into_iter — seeds start_log/end_log from range bounds
    (
        &[
            "<core::ops::range::Range as core::iter::IntoIterator>::into_iter",
            // `std::ops::Range` normalizes to `core::ops::Range` (missing `range::`)
            "<core::ops::Range as core::iter::IntoIterator>::into_iter",
            "<std::ops::Range as core::iter::IntoIterator>::into_iter",
            "<core::ops::Range as std::iter::IntoIterator>::into_iter",
            "<std::ops::Range as std::iter::IntoIterator>::into_iter",
        ],
        iter::specs::RANGE_INTO_ITER,
    ),
    // core::iter::empty — always completed
    (
        &[
            "core::iter::sources::empty::empty",
            "core::iter::empty",
            "std::iter::empty",
        ],
        iter::specs::ITER_EMPTY,
    ),
    // core::iter::once — produces exactly one element
    (
        &[
            "core::iter::sources::once::once",
            "core::iter::once",
            "std::iter::once",
        ],
        iter::specs::ITER_ONCE,
    ),
    // core::iter::repeat — infinite production of the same value
    (
        &[
            "core::iter::sources::repeat::repeat",
            "core::iter::repeat",
            "std::iter::repeat",
        ],
        iter::specs::ITER_REPEAT,
    ),
    (
        &[
            "core::iter::traits::iterator::Iterator::fuse",
            "std::iter::traits::iterator::Iterator::fuse",
        ],
        iter::specs::ITER_FUSE,
    ),
    (
        &[
            "core::iter::traits::iterator::Iterator::cloned",
            "std::iter::traits::iterator::Iterator::cloned",
        ],
        iter::specs::ITER_CLONED,
    ),
    (
        &[
            "core::iter::traits::iterator::Iterator::copied",
            "std::iter::traits::iterator::Iterator::copied",
            "core::iter::Iterator::copied",
            "std::iter::Iterator::copied",
        ],
        iter::specs::ITER_COPIED,
    ),
    (
        &[
            "core::iter::traits::iterator::Iterator::skip",
            "std::iter::traits::iterator::Iterator::skip",
        ],
        iter::specs::ITER_SKIP,
    ),
    (
        &[
            "core::iter::traits::iterator::Iterator::take",
            "std::iter::traits::iterator::Iterator::take",
        ],
        iter::specs::ITER_TAKE,
    ),
    (
        &[
            "core::iter::traits::iterator::Iterator::enumerate",
            "std::iter::traits::iterator::Iterator::enumerate",
        ],
        iter::specs::ITER_ENUMERATE,
    ),
    (
        &[
            "core::iter::traits::iterator::Iterator::zip",
            "std::iter::traits::iterator::Iterator::zip",
        ],
        iter::specs::ITER_ZIP,
    ),
    // Iterator::map — wraps iterator + closure, seeds accessor equalities (#2170).
    (
        &[
            "core::iter::traits::iterator::Iterator::map",
            "std::iter::traits::iterator::Iterator::map",
        ],
        iter::specs::ITER_MAP,
    ),
    // Iterator::filter — wraps iterator + predicate, seeds accessor equalities (#2170).
    (
        &[
            "core::iter::traits::iterator::Iterator::filter",
            "std::iter::traits::iterator::Iterator::filter",
            "core::iter::Iterator::filter",
            "std::iter::Iterator::filter",
        ],
        iter::specs::ITER_FILTER,
    ),
    // Iterator::filter_map — wraps iterator + closure, seeds accessor equalities (#2170).
    (
        &[
            "core::iter::traits::iterator::Iterator::filter_map",
            "std::iter::traits::iterator::Iterator::filter_map",
            "core::iter::Iterator::filter_map",
            "std::iter::Iterator::filter_map",
        ],
        iter::specs::ITER_FILTER_MAP,
    ),
    // Iterator::collect — close the into_iter/collect roundtrip gap (#2116).
    // Post-borrowck MIR does NOT inline collect() to FromIterator::from_iter,
    // so this is the path that actually appears at call sites.
    (
        &[
            "core::iter::traits::iterator::Iterator::collect",
            "std::iter::traits::iterator::Iterator::collect",
            "std::iter::Iterator::collect",
            "core::iter::Iterator::collect",
        ],
        iter::specs::ITERATOR_COLLECT,
    ),
    // <Vec<T> as FromIterator<T>>::from_iter — collect via FromIteratorSpec (#2217).
    // Direct from_iter calls (rare; collect() is the common path) get the
    // richer from_iter_post constraint instead of the simple roundtrip spec.
    (
        &[
            "<alloc::vec::Vec as core::iter::FromIterator>::from_iter",
            "<std::vec::Vec as core::iter::FromIterator>::from_iter",
            "<alloc::vec::Vec as std::iter::FromIterator>::from_iter",
            "<std::vec::Vec as std::iter::FromIterator>::from_iter",
            "<alloc::vec::Vec as core::iter::traits::collect::FromIterator>::from_iter",
            "<std::vec::Vec as core::iter::traits::collect::FromIterator>::from_iter",
        ],
        iter::specs::VEC_FROM_ITER,
    ),
    // Iterator::rev — wraps in Rev adapter, preserves inner state (#2217).
    (
        &[
            "core::iter::traits::iterator::Iterator::rev",
            "std::iter::traits::iterator::Iterator::rev",
            "std::iter::Iterator::rev",
            "core::iter::Iterator::rev",
        ],
        iter::specs::ITERATOR_REV,
    ),
    // DoubleEndedIterator::next_back — reverse analogue of Iterator::next (#2217).
    (
        &[
            "core::iter::traits::double_ended::DoubleEndedIterator::next_back",
            "std::iter::traits::double_ended::DoubleEndedIterator::next_back",
            "std::iter::DoubleEndedIterator::next_back",
            "core::iter::DoubleEndedIterator::next_back",
            // UFCS paths for adapter types that implement DoubleEndedIterator (#2688).
            "<core::iter::adapters::rev::Rev as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::rev::Rev as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Rev as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Rev as std::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::chain::Chain as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::chain::Chain as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Chain as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Chain as std::iter::DoubleEndedIterator>::next_back",
            // Concrete iterator types
            "<alloc::vec::into_iter::IntoIter as core::iter::DoubleEndedIterator>::next_back",
            "<alloc::vec::into_iter::IntoIter as std::iter::DoubleEndedIterator>::next_back",
            "<std::vec::IntoIter as core::iter::DoubleEndedIterator>::next_back",
            "<std::vec::IntoIter as std::iter::DoubleEndedIterator>::next_back",
            "<core::slice::iter::Iter as core::iter::DoubleEndedIterator>::next_back",
            "<core::slice::iter::Iter as std::iter::DoubleEndedIterator>::next_back",
            "<core::slice::Iter as core::iter::DoubleEndedIterator>::next_back",
            "<core::slice::Iter as std::iter::DoubleEndedIterator>::next_back",
            "<std::slice::Iter as core::iter::DoubleEndedIterator>::next_back",
            "<std::slice::Iter as std::iter::DoubleEndedIterator>::next_back",
            // ── Additional DoubleEndedIterator adapter UFCS paths (#2689) ──
            // IterMut
            "<core::slice::iter::IterMut as core::iter::DoubleEndedIterator>::next_back",
            "<core::slice::iter::IterMut as std::iter::DoubleEndedIterator>::next_back",
            "<core::slice::IterMut as core::iter::DoubleEndedIterator>::next_back",
            "<core::slice::IterMut as std::iter::DoubleEndedIterator>::next_back",
            "<std::slice::IterMut as core::iter::DoubleEndedIterator>::next_back",
            "<std::slice::IterMut as std::iter::DoubleEndedIterator>::next_back",
            // Map adapter
            "<core::iter::adapters::map::Map as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::map::Map as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Map as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Map as std::iter::DoubleEndedIterator>::next_back",
            // Filter adapter
            "<core::iter::adapters::filter::Filter as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::filter::Filter as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Filter as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Filter as std::iter::DoubleEndedIterator>::next_back",
            // Enumerate adapter
            "<core::iter::adapters::enumerate::Enumerate as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::enumerate::Enumerate as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Enumerate as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Enumerate as std::iter::DoubleEndedIterator>::next_back",
            // Fuse adapter
            "<core::iter::adapters::fuse::Fuse as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::fuse::Fuse as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Fuse as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Fuse as std::iter::DoubleEndedIterator>::next_back",
            // Cloned adapter
            "<core::iter::adapters::cloned::Cloned as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::cloned::Cloned as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Cloned as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Cloned as std::iter::DoubleEndedIterator>::next_back",
            // Copied adapter
            "<core::iter::adapters::copied::Copied as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::copied::Copied as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Copied as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Copied as std::iter::DoubleEndedIterator>::next_back",
            // Peekable adapter
            "<core::iter::adapters::peekable::Peekable as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::peekable::Peekable as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Peekable as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Peekable as std::iter::DoubleEndedIterator>::next_back",
            // FlatMap adapter
            "<core::iter::adapters::flatten::FlatMap as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::flatten::FlatMap as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::FlatMap as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::FlatMap as std::iter::DoubleEndedIterator>::next_back",
            // Flatten adapter
            "<core::iter::adapters::flatten::Flatten as core::iter::DoubleEndedIterator>::next_back",
            "<core::iter::adapters::flatten::Flatten as std::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Flatten as core::iter::DoubleEndedIterator>::next_back",
            "<std::iter::Flatten as std::iter::DoubleEndedIterator>::next_back",
        ],
        iter::specs::DOUBLE_ENDED_NEXT_BACK,
    ),
    // Iterator::sum — consumes iterator, produces sum of elements.
    (
        &[
            "core::iter::traits::iterator::Iterator::sum",
            "std::iter::traits::iterator::Iterator::sum",
            "std::iter::Iterator::sum",
            "core::iter::Iterator::sum",
        ],
        iter::specs::ITERATOR_SUM,
    ),
    // Iterator::count — consumes iterator, returns number of elements.
    (
        &[
            "core::iter::traits::iterator::Iterator::count",
            "std::iter::traits::iterator::Iterator::count",
            "std::iter::Iterator::count",
            "core::iter::Iterator::count",
        ],
        iter::specs::ITERATOR_COUNT,
    ),
    // Iterator::for_each — consumes iterator, calls closure on each element.
    (
        &[
            "core::iter::traits::iterator::Iterator::for_each",
            "std::iter::traits::iterator::Iterator::for_each",
        ],
        iter::specs::ITERATOR_FOR_EACH,
    ),
    // Iterator::fold — consumes iterator with accumulator.
    (
        &[
            "core::iter::traits::iterator::Iterator::fold",
            "std::iter::traits::iterator::Iterator::fold",
        ],
        iter::specs::ITERATOR_FOLD,
    ),
    // Iterator::any — tests if any element satisfies predicate.
    (
        &[
            "core::iter::traits::iterator::Iterator::any",
            "std::iter::traits::iterator::Iterator::any",
        ],
        iter::specs::ITERATOR_ANY,
    ),
    // Iterator::all — tests if all elements satisfy predicate.
    (
        &[
            "core::iter::traits::iterator::Iterator::all",
            "std::iter::traits::iterator::Iterator::all",
        ],
        iter::specs::ITERATOR_ALL,
    ),
    // Iterator::find — returns first element satisfying predicate.
    (
        &[
            "core::iter::traits::iterator::Iterator::find",
            "std::iter::traits::iterator::Iterator::find",
        ],
        iter::specs::ITERATOR_FIND,
    ),
    // Iterator::position — returns index of first matching element.
    (
        &[
            "core::iter::traits::iterator::Iterator::position",
            "std::iter::traits::iterator::Iterator::position",
        ],
        iter::specs::ITERATOR_POSITION,
    ),
    // Iterator::chain — chains two iterators.
    (
        &[
            "core::iter::traits::iterator::Iterator::chain",
            "std::iter::traits::iterator::Iterator::chain",
        ],
        iter::specs::ITERATOR_CHAIN,
    ),
    // Iterator::peekable — wraps in Peekable adapter.
    (
        &[
            "core::iter::traits::iterator::Iterator::peekable",
            "std::iter::traits::iterator::Iterator::peekable",
        ],
        iter::specs::ITERATOR_PEEKABLE,
    ),
    // Iterator::flat_map — wraps iterator + closure.
    (
        &[
            "core::iter::traits::iterator::Iterator::flat_map",
            "std::iter::traits::iterator::Iterator::flat_map",
        ],
        iter::specs::ITER_FLAT_MAP,
    ),
    // Iterator::inspect — wraps iterator, does not change elements.
    (
        &[
            "core::iter::traits::iterator::Iterator::inspect",
            "std::iter::traits::iterator::Iterator::inspect",
        ],
        iter::specs::ITER_INSPECT,
    ),
    // Iterator::step_by — steps through iterator.
    (
        &[
            "core::iter::traits::iterator::Iterator::step_by",
            "std::iter::traits::iterator::Iterator::step_by",
        ],
        iter::specs::ITER_STEP_BY,
    ),
    // Iterator::take_while — yields elements based on predicate.
    (
        &[
            "core::iter::traits::iterator::Iterator::take_while",
            "std::iter::traits::iterator::Iterator::take_while",
        ],
        iter::specs::ITER_TAKE_WHILE,
    ),
    // Iterator::skip_while — skips elements based on predicate.
    (
        &[
            "core::iter::traits::iterator::Iterator::skip_while",
            "std::iter::traits::iterator::Iterator::skip_while",
        ],
        iter::specs::ITER_SKIP_WHILE,
    ),
    // Iterator::min — returns minimum element.
    (
        &[
            "core::iter::traits::iterator::Iterator::min",
            "std::iter::traits::iterator::Iterator::min",
        ],
        iter::specs::ITERATOR_MIN,
    ),
    // Iterator::max — returns maximum element.
    (
        &[
            "core::iter::traits::iterator::Iterator::max",
            "std::iter::traits::iterator::Iterator::max",
        ],
        iter::specs::ITERATOR_MAX,
    ),
    // Iterator::last — consumes, returns last element.
    (
        &[
            "core::iter::traits::iterator::Iterator::last",
            "std::iter::traits::iterator::Iterator::last",
        ],
        iter::specs::ITERATOR_LAST,
    ),
    // Iterator::nth — returns nth element.
    (
        &[
            "core::iter::traits::iterator::Iterator::nth",
            "std::iter::traits::iterator::Iterator::nth",
        ],
        iter::specs::ITERATOR_NTH,
    ),
    // Iterator::flatten — flattens nested structure.
    (
        &[
            "core::iter::traits::iterator::Iterator::flatten",
            "std::iter::traits::iterator::Iterator::flatten",
        ],
        iter::specs::ITER_FLATTEN,
    ),
    // Iterator::unzip — converts iterator of pairs into pair of containers.
    (
        &[
            "core::iter::traits::iterator::Iterator::unzip",
            "std::iter::traits::iterator::Iterator::unzip",
        ],
        iter::specs::ITERATOR_UNZIP,
    ),
    // Iterator::min_by — returns element that gives minimum via compare.
    (
        &[
            "core::iter::traits::iterator::Iterator::min_by",
            "std::iter::traits::iterator::Iterator::min_by",
        ],
        iter::specs::ITERATOR_MIN_BY,
    ),
    // Iterator::max_by — returns element that gives maximum via compare.
    (
        &[
            "core::iter::traits::iterator::Iterator::max_by",
            "std::iter::traits::iterator::Iterator::max_by",
        ],
        iter::specs::ITERATOR_MAX_BY,
    ),
    // Iterator::min_by_key — returns element that gives minimum key.
    (
        &[
            "core::iter::traits::iterator::Iterator::min_by_key",
            "std::iter::traits::iterator::Iterator::min_by_key",
        ],
        iter::specs::ITERATOR_MIN_BY_KEY,
    ),
    // Iterator::max_by_key — returns element that gives maximum key.
    (
        &[
            "core::iter::traits::iterator::Iterator::max_by_key",
            "std::iter::traits::iterator::Iterator::max_by_key",
        ],
        iter::specs::ITERATOR_MAX_BY_KEY,
    ),
    // Iterator::product — multiplies all elements.
    (
        &[
            "core::iter::traits::iterator::Iterator::product",
            "std::iter::traits::iterator::Iterator::product",
        ],
        iter::specs::ITERATOR_PRODUCT,
    ),
    // Iterator::find_map — applies function and returns first non-None result.
    (
        &[
            "core::iter::traits::iterator::Iterator::find_map",
            "std::iter::traits::iterator::Iterator::find_map",
        ],
        iter::specs::ITERATOR_FIND_MAP,
    ),
    // Iterator::reduce — reduces to a single element.
    (
        &[
            "core::iter::traits::iterator::Iterator::reduce",
            "std::iter::traits::iterator::Iterator::reduce",
        ],
        iter::specs::ITERATOR_REDUCE,
    ),
    // ExactSizeIterator::len — exact remaining length.
    (
        &[
            "core::iter::traits::exact_size::ExactSizeIterator::len",
            "std::iter::traits::exact_size::ExactSizeIterator::len",
            "core::iter::ExactSizeIterator::len",
            "std::iter::ExactSizeIterator::len",
        ],
        iter::specs::EXACT_SIZE_ITER_LEN,
    ),
    // Iterator::map_while — predicate-driven mapping that stops on None.
    (
        &[
            "core::iter::traits::iterator::Iterator::map_while",
            "std::iter::traits::iterator::Iterator::map_while",
        ],
        iter::specs::ITER_MAP_WHILE,
    ),
    // Iterator::scan — stateful transformation adapter.
    (
        &[
            "core::iter::traits::iterator::Iterator::scan",
            "std::iter::traits::iterator::Iterator::scan",
        ],
        iter::specs::ITER_SCAN,
    ),
    // Iterator::try_fold — foldable that can fail early.
    (
        &[
            "core::iter::traits::iterator::Iterator::try_fold",
            "std::iter::traits::iterator::Iterator::try_fold",
        ],
        iter::specs::ITERATOR_TRY_FOLD,
    ),
    // Iterator::try_for_each — applies fallible function, stops on first error.
    (
        &[
            "core::iter::traits::iterator::Iterator::try_for_each",
            "std::iter::traits::iterator::Iterator::try_for_each",
        ],
        iter::specs::ITERATOR_TRY_FOR_EACH,
    ),
    // Iterator::is_sorted — returns true if elements are sorted.
    (
        &[
            "core::iter::traits::iterator::Iterator::is_sorted",
            "std::iter::traits::iterator::Iterator::is_sorted",
        ],
        iter::specs::ITERATOR_IS_SORTED,
    ),
    // Iterator::partition — splits into two collections based on predicate.
    (
        &[
            "core::iter::traits::iterator::Iterator::partition",
            "std::iter::traits::iterator::Iterator::partition",
        ],
        iter::specs::ITERATOR_PARTITION,
    ),
    // Iterator::eq — tests element-wise equality of two iterators.
    (
        &[
            "core::iter::traits::iterator::Iterator::eq",
            "std::iter::traits::iterator::Iterator::eq",
        ],
        iter::specs::ITERATOR_EQ,
    ),
    // Iterator::size_hint — returns remaining length bounds. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::size_hint",
            "std::iter::traits::iterator::Iterator::size_hint",
        ],
        iter::specs::ITERATOR_SIZE_HINT,
    ),
    // Iterator::by_ref — borrows the iterator. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::by_ref",
            "std::iter::traits::iterator::Iterator::by_ref",
        ],
        iter::specs::ITERATOR_BY_REF,
    ),
    // Iterator::cmp — lexicographic comparison. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::cmp",
            "std::iter::traits::iterator::Iterator::cmp",
        ],
        iter::specs::ITERATOR_CMP,
    ),
    // Iterator::partial_cmp — lexicographic partial comparison. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::partial_cmp",
            "std::iter::traits::iterator::Iterator::partial_cmp",
        ],
        iter::specs::ITERATOR_PARTIAL_CMP,
    ),
    // Iterator::ne — element-wise inequality. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::ne",
            "std::iter::traits::iterator::Iterator::ne",
        ],
        iter::specs::ITERATOR_NE,
    ),
    // Iterator::lt — lexicographic less-than. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::lt",
            "std::iter::traits::iterator::Iterator::lt",
        ],
        iter::specs::ITERATOR_LT,
    ),
    // Iterator::le — lexicographic less-than-or-equal. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::le",
            "std::iter::traits::iterator::Iterator::le",
        ],
        iter::specs::ITERATOR_LE,
    ),
    // Iterator::gt — lexicographic greater-than. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::gt",
            "std::iter::traits::iterator::Iterator::gt",
        ],
        iter::specs::ITERATOR_GT,
    ),
    // Iterator::ge — lexicographic greater-than-or-equal. (#2689)
    (
        &[
            "core::iter::traits::iterator::Iterator::ge",
            "std::iter::traits::iterator::Iterator::ge",
        ],
        iter::specs::ITERATOR_GE,
    ),
    // RangeInclusive IntoIterator — inclusive range `for x in 0..=5` (#2689)
    (
        &[
            "<core::ops::range::RangeInclusive as core::iter::IntoIterator>::into_iter",
            // `std::ops::RangeInclusive` normalizes to `core::ops::RangeInclusive` (missing `range::`)
            "<core::ops::RangeInclusive as core::iter::IntoIterator>::into_iter",
            "<std::ops::RangeInclusive as core::iter::IntoIterator>::into_iter",
            "<core::ops::RangeInclusive as std::iter::IntoIterator>::into_iter",
            "<std::ops::RangeInclusive as std::iter::IntoIterator>::into_iter",
        ],
        iter::specs::RANGE_INTO_ITER,
    ),
];
