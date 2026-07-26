#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Stable import hub for the Creusot compatibility classifier policy."""

from __future__ import annotations

try:
    from tests.creusot_compat.harness_classify_fail import (
        BACKEND_PASS_PREFIX,
        STRICT_PASS_PREFIX,
        _KNOWN_BACKEND_SUPERSEDED_TESTS,
        _KNOWN_STRICT_REJECTION_TESTS,
        _check_backend_superseded,
        _is_should_fail_test,
        classify_error_category,
        classify_should_fail_result,
        classify_unknown_category,
        count_backend_superseded,
        count_known_false_accepts,
        get_false_accept_summary,
        get_residual_summary,
    )
    from tests.creusot_compat.harness_classify_signals import (
        _dropped_obligation_warning_count,
        _has_cargo_lock_contention,
        _has_caught_panic_marker,
        _has_panic_exit_status,
        _has_rustc_panic,
        _has_timeout_caused_errors,
        _has_verified_contracts,
        _has_verification_failures,
        _last_contract_count,
        _last_proof_assert_summary_counts,
        _last_verification_summary_counts,
        _verification_run_succeeded,
        _wire_line_shows_pa_only_failure,
    )
    from tests.creusot_compat.harness_classify_succeed import (
        NO_REPLAY_PASS_PREFIX,
        NO_REPLAY_STRICT_ERROR_MESSAGE,
        _all_contracts_axiomatized,
        _is_no_replay_source,
        _source_has_user_contracts,
        classify_failure,
        classify_no_replay_result,
    )
except ModuleNotFoundError:
    from harness_classify_fail import (
        BACKEND_PASS_PREFIX,
        STRICT_PASS_PREFIX,
        _KNOWN_BACKEND_SUPERSEDED_TESTS,
        _KNOWN_STRICT_REJECTION_TESTS,
        _check_backend_superseded,
        _is_should_fail_test,
        classify_error_category,
        classify_should_fail_result,
        classify_unknown_category,
        count_backend_superseded,
        count_known_false_accepts,
        get_false_accept_summary,
        get_residual_summary,
    )
    from harness_classify_signals import (
        _dropped_obligation_warning_count,
        _has_cargo_lock_contention,
        _has_caught_panic_marker,
        _has_panic_exit_status,
        _has_rustc_panic,
        _has_timeout_caused_errors,
        _has_verified_contracts,
        _has_verification_failures,
        _last_contract_count,
        _last_proof_assert_summary_counts,
        _last_verification_summary_counts,
        _verification_run_succeeded,
        _wire_line_shows_pa_only_failure,
    )
    from harness_classify_succeed import (
        NO_REPLAY_PASS_PREFIX,
        NO_REPLAY_STRICT_ERROR_MESSAGE,
        _all_contracts_axiomatized,
        _is_no_replay_source,
        _source_has_user_contracts,
        classify_failure,
        classify_no_replay_result,
    )


def _module_exports() -> list[str]:
    return [
        "BACKEND_PASS_PREFIX",
        "NO_REPLAY_PASS_PREFIX",
        "NO_REPLAY_STRICT_ERROR_MESSAGE",
        "STRICT_PASS_PREFIX",
        "_KNOWN_BACKEND_SUPERSEDED_TESTS",
        "_KNOWN_STRICT_REJECTION_TESTS",
        "_all_contracts_axiomatized",
        "_check_backend_superseded",
        "_dropped_obligation_warning_count",
        "_has_cargo_lock_contention",
        "_has_caught_panic_marker",
        "_has_panic_exit_status",
        "_has_rustc_panic",
        "_has_timeout_caused_errors",
        "_has_verified_contracts",
        "_has_verification_failures",
        "_is_no_replay_source",
        "_is_should_fail_test",
        "_source_has_user_contracts",
        "_last_contract_count",
        "_last_proof_assert_summary_counts",
        "_last_verification_summary_counts",
        "_verification_run_succeeded",
        "_wire_line_shows_pa_only_failure",
        "classify_error_category",
        "classify_failure",
        "classify_no_replay_result",
        "classify_should_fail_result",
        "classify_unknown_category",
        "count_backend_superseded",
        "count_known_false_accepts",
        "get_false_accept_summary",
        "get_residual_summary",
    ]


__all__ = _module_exports()
