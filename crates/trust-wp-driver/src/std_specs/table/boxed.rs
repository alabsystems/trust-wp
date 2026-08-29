// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Box<T> specs — new, deref, deref_mut, into_inner, as_ref, as_mut.

use trust_wp_std::std::boxed;

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    // Box::new — logically transparent wrapping
    (
        &["alloc::boxed::Box::new", "std::boxed::Box::new"],
        boxed::specs::NEW,
    ),
    // Box::into_inner (unstable intrinsic, but encountered as *box)
    (
        &[
            "alloc::boxed::Box::into_inner",
            "std::boxed::Box::into_inner",
        ],
        boxed::specs::INTO_INNER,
    ),
    // Box<T> Deref::deref — identity on inner value
    (
        &[
            "<alloc::boxed::Box as core::ops::Deref>::deref",
            "<alloc::boxed::Box as std::ops::Deref>::deref",
            "<std::boxed::Box as core::ops::Deref>::deref",
            "<std::boxed::Box as std::ops::Deref>::deref",
            "alloc::boxed::Box::deref",
            "std::boxed::Box::deref",
        ],
        boxed::specs::DEREF,
    ),
    // Box<T> DerefMut::deref_mut — mutable identity on inner value
    (
        &[
            "<alloc::boxed::Box as core::ops::DerefMut>::deref_mut",
            "<alloc::boxed::Box as std::ops::DerefMut>::deref_mut",
            "<std::boxed::Box as core::ops::DerefMut>::deref_mut",
            "<std::boxed::Box as std::ops::DerefMut>::deref_mut",
            "alloc::boxed::Box::deref_mut",
            "std::boxed::Box::deref_mut",
        ],
        boxed::specs::DEREF_MUT,
    ),
    // Box<T> as_ref
    (
        &[
            "alloc::boxed::Box::as_ref",
            "std::boxed::Box::as_ref",
            "<alloc::boxed::Box as core::convert::AsRef>::as_ref",
            "<alloc::boxed::Box as std::convert::AsRef>::as_ref",
            "<std::boxed::Box as core::convert::AsRef>::as_ref",
            "<std::boxed::Box as std::convert::AsRef>::as_ref",
        ],
        boxed::specs::AS_REF,
    ),
    // Box<T> as_mut
    (
        &[
            "alloc::boxed::Box::as_mut",
            "std::boxed::Box::as_mut",
            "<alloc::boxed::Box as core::convert::AsMut>::as_mut",
            "<alloc::boxed::Box as std::convert::AsMut>::as_mut",
            "<std::boxed::Box as core::convert::AsMut>::as_mut",
            "<std::boxed::Box as std::convert::AsMut>::as_mut",
        ],
        boxed::specs::AS_MUT,
    ),
];
