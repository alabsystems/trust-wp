// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structured verification result protocol for `trust-wp-rustc` → `cargo-trust-wp`
//! communication.
//!
//! Replaces brittle stderr text parsing with a fixed ASCII wire format.
//! The wire line is emitted by `trust-wp-rustc` when `TRUST_WP_RESULT_PROTOCOL=1`
//! is set, and parsed by `cargo-trust-wp` to derive exit codes.
//!
//! Wire format:
//! ```text
//! TRUST_WP_RESULT:v1 base_exit_code=1 verified=2 failed=1 errors=0 ...
//! ```
//!
//! Design: `designs/2026-03-12-1690-structured-result-protocol.md`

/// Wire line prefix. Reject lines with unknown schema versions.
pub const WIRE_PREFIX: &str = "TRUST_WP_RESULT:v1";

/// Machine-readable per-obligation diagnostic line prefix.
///
/// `cargo-trust-wp` treats this as ordinary stderr today, so adding this side
/// channel does not change `TRUST_WP_RESULT:v1` parsing or exit-code behavior.
pub const DIAGNOSTIC_WIRE_PREFIX: &str = "TRUST_WP_DIAGNOSTIC:v1";

/// Environment variable that `cargo-trust-wp` sets to request structured output.
pub const RESULT_PROTOCOL_ENV: &str = "TRUST_WP_RESULT_PROTOCOL";

/// Diagnostic field value meaning "this does not apply / was not produced".
pub const NONE_SENTINEL: &str = "none";

/// Diagnostic field value meaning "the engine had no evidence either way".
pub const UNKNOWN_SENTINEL: &str = "unknown";

/// Whether a `TRUST_WP_RESULT:v1` field must be present for a line to parse.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WireFieldPresence {
    /// The decoder rejects a line that omits the field.
    Required,
    /// The decoder defaults the field to zero when the key is absent. Fields
    /// added after v1 first shipped are optional: an older producer omits them.
    Optional,
}

/// Canonical `TRUST_WP_RESULT:v1` field manifest, in wire-emission order.
///
/// This is THE single declaration of the v1 field set:
/// [`StructuredVerificationResult::to_wire_line`] renders exactly these keys in
/// this order, [`StructuredVerificationResult::from_wire_line`] derives its
/// known-key set and required-field mask from it, and the checked-in
/// conformance fixture `tests/creusot_compat/wire_fields.v1.txt` is generated
/// from it by [`wire_fields_v1_manifest`]. The two Python decoders
/// (`tests/creusot_compat/harness_model.py`, `scripts/compare_baselines.py`)
/// are pinned to that fixture by pytest, so a field added here without
/// teaching the mirrors fails their suites instead of silently rejecting every
/// fresh wire line (the drift class behind the 24-test misclassification day).
/// Whether a rendered Alethe proof can be replayed by an independent checker.
///
/// ay renders a step whose rule the pinned calculus does not implement as
/// `hole` — see `UNPROVED_STEP_RULE`. That is an honest rendering rather than a
/// defect: a bit-blasting theory lemma really has no Alethe spelling, so a
/// proof that leans on one cannot be handed to carcara whatever its native
/// standing.
///
/// This is NOT the same question as whether the proof has unproved steps. A
/// `hole` in the proof *IR* means an inference was never established, and such
/// a proof is refused outright (`hole_count == 0` is required for authority). A
/// `hole` in the rendered *text* can sit under an inference ay validated fully.
/// The first is a soundness failure; the second is a limit on who else can
/// check the work.
///
/// `None` text means the proof was not rendered, which is not evidence either
/// way — callers should treat that as unknown rather than as a failure.
#[must_use]
pub fn alethe_proof_is_externally_checkable(alethe_text: &str) -> bool {
    !alethe_text
        .split(":rule")
        .skip(1)
        .any(|tail| tail.trim_start().starts_with("hole"))
}

pub const WIRE_FIELDS_V1: &[(&str, WireFieldPresence)] = &[
    ("base_exit_code", WireFieldPresence::Required),
    ("verified", WireFieldPresence::Required),
    ("failed", WireFieldPresence::Required),
    ("errors", WireFieldPresence::Required),
    ("warnings", WireFieldPresence::Required),
    ("assumed", WireFieldPresence::Required),
    ("trusted", WireFieldPresence::Required),
    ("skipped", WireFieldPresence::Required),
    ("verified_with_axiom_deps", WireFieldPresence::Required),
    ("unverified_axioms", WireFieldPresence::Required),
    ("vacuous", WireFieldPresence::Required),
    ("evidence_gaps", WireFieldPresence::Required),
    // Optional: absent from records emitted before this field existed.
    ("proof_assert_verified", WireFieldPresence::Optional),
    // Optional for the same reason: contractless proof_asserts the solver could
    // not decide. Counted as a soundness gap (#143) -- previously incremented a
    // field that reached no outcome column, so a test could report a clean pass
    // while carrying an undecided obligation.
    ("proof_assert_inconclusive", WireFieldPresence::Optional),
    // Optional for the same reason: absent from records emitted before it
    // existed, and absent from producers that cannot determine it.
    ("verified_native_only", WireFieldPresence::Optional),
    ("proof_assert_failed", WireFieldPresence::Required),
    ("proof_assert_errors", WireFieldPresence::Required),
    ("panics", WireFieldPresence::Required),
    ("demoted", WireFieldPresence::Required),
    ("parse_errors", WireFieldPresence::Required),
    ("termination_errors", WireFieldPresence::Required),
    ("logic_recursion_errors", WireFieldPresence::Required),
    ("erasure_errors", WireFieldPresence::Required),
];

// The decoder tracks seen fields in a u32 bitmask indexed by manifest position.
const _: () = assert!(WIRE_FIELDS_V1.len() <= u32::BITS as usize);

/// Bitmask (by [`WIRE_FIELDS_V1`] index) of the fields a v1 line must carry.
const fn wire_required_mask() -> u32 {
    let mut mask = 0u32;
    let mut index = 0;
    while index < WIRE_FIELDS_V1.len() {
        if matches!(WIRE_FIELDS_V1[index].1, WireFieldPresence::Required) {
            mask |= 1 << index;
        }
        index += 1;
    }
    mask
}

/// Render [`WIRE_FIELDS_V1`] as the conformance-fixture text checked in at
/// `tests/creusot_compat/wire_fields.v1.txt`.
///
/// Plain text: `#` comment lines, then one field name per line under
/// `[required]` / `[optional]` section markers, each section in wire-emission
/// order. A Rust unit test asserts the checked-in file equals this string; the
/// Python decoder tests parse the same file — all field-set declarations meet
/// at one artifact.
#[must_use]
pub fn wire_fields_v1_manifest() -> String {
    let mut out = String::from(
        "# TRUST_WP_RESULT:v1 wire-field manifest — generated, do not hand-edit.\n\
         # Source of truth: trust_wp_core::result_protocol::WIRE_FIELDS_V1 (the same\n\
         # slice drives the Rust emitter and decoder). Regenerate and commit together\n\
         # with any manifest change:\n\
         #   TRUST_WP_BLESS_WIRE_FIXTURE=1 cargo test -p trust-wp-core --lib wire_manifest\n\
         # Pinned consumers: tests/creusot_compat/harness_model.py and\n\
         # scripts/compare_baselines.py, via tests/creusot_compat/test_harness.py.\n",
    );
    for (header, want) in [
        ("[required]", WireFieldPresence::Required),
        ("[optional]", WireFieldPresence::Optional),
    ] {
        out.push_str(header);
        out.push('\n');
        for (name, presence) in WIRE_FIELDS_V1 {
            if *presence == want {
                out.push_str(name);
                out.push('\n');
            }
        }
    }
    out
}

/// Structured verification result record.
///
/// All fields are integer counters. The wire format is a space-separated
/// sequence of `key=value` pairs after the `TRUST_WP_RESULT:v1` prefix.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StructuredVerificationResult {
    /// Base exit code from the driver's `VerificationSummary::exit_code()`.
    pub base_exit_code: i32,
    /// Functions whose contracts were proven correct.
    pub verified: u64,
    /// Functions whose contracts were disproven.
    pub failed: u64,
    /// Functions with encoding/solver errors.
    pub errors: u64,
    /// Dropped obligation warnings.
    pub warnings: u64,
    /// Functions whose contracts were assumed correct.
    pub assumed: u64,
    /// `#[trusted]`-annotated functions skipped by design.
    pub trusted: u64,
    /// Functions skipped (no MIR body).
    pub skipped: u64,
    /// Functions verified but depending on unproven axioms.
    pub verified_with_axiom_deps: u64,
    /// Logic function postconditions that could not be verified.
    pub unverified_axioms: u64,
    /// Functions where verification was vacuous.
    pub vacuous: u64,
    /// Verified-shaped results that lacked accepted proof evidence.
    pub evidence_gaps: u64,
    /// Contractless proof_asserts the solver could not decide (#143).
    pub proof_assert_inconclusive: u64,
    /// `proof_assert` statements that were proved.
    ///
    /// Carried so a consumer can tell "examined nothing" apart from "examined
    /// only `proof_assert!`s, and proved them all" — the two are otherwise
    /// indistinguishable in an all-zero record. It does not participate in the
    /// exit code, and it is an OPTIONAL wire field: a producer that predates it
    /// omits the key and a reader defaults it to 0.
    pub proof_assert_verified: u64,
    /// Obligations that verified on proof authority no INDEPENDENT checker can
    /// re-check.
    ///
    /// These are counted in `verified` too — the distinction is *which kind* of
    /// authority backs them, not whether they were proved. ay validated every
    /// inference itself (a genuinely unproved step is a `hole` in the proof IR
    /// and is refused outright), but the proof does not render into the pinned
    /// Alethe calculus, so carcara cannot replay it. A symbolic QF_BV
    /// refutation is the standard case: it is anchored on a bit-blasting theory
    /// lemma for which the calculus has no rule, so it renders as `hole` on the
    /// wire however sound it is natively.
    ///
    /// Reported because the two claims are genuinely different and a consumer
    /// cannot otherwise tell them apart: "we checked this ourselves" is weaker
    /// than "anyone can check this", and a tool that trades on being honest
    /// about its own limits should not silently merge them. Zero means every
    /// verified obligation carries an externally replayable proof.
    pub verified_native_only: u64,
    /// `proof_assert` statements that failed.
    pub proof_assert_failed: u64,
    /// `proof_assert` statements with errors.
    pub proof_assert_errors: u64,
    /// Functions where driver-level processing panicked.
    pub panics: u64,
    /// Functions demoted from Verified to Unknown.
    pub demoted: u64,
    /// Contract/logic parse errors (Slice 2: currently zero in Slice 1).
    pub parse_errors: u64,
    /// Termination check errors (Slice 2: currently zero in Slice 1).
    pub termination_errors: u64,
    /// Logic recursion errors (Slice 2: currently zero in Slice 1).
    pub logic_recursion_errors: u64,
    /// `#[erasure(target)]` validation errors (Phase 5c THIR-equivalence scaffold).
    ///
    /// Counts every `(lhs, rhs)` erasure pair where the driver-side check failed.
    /// The current driver implementation performs a STUB check (target resolvable,
    /// rhs has a non-empty body). Full Creusot-grade THIR-equivalence after
    /// ghost-stripping + A-normal form is deferred. See
    /// `crates/trust-wp-driver/src/callbacks/discovery/erasure.rs`.
    pub erasure_errors: u64,
}

impl StructuredVerificationResult {
    /// Serialize to the wire line format.
    ///
    /// Produces a single line suitable for stderr emission. Renders exactly
    /// the [`WIRE_FIELDS_V1`] manifest, in manifest order.
    #[must_use]
    pub fn to_wire_line(&self) -> String {
        use std::fmt::Write as _;

        let mut line = String::from(WIRE_PREFIX);
        for (name, _) in WIRE_FIELDS_V1 {
            let _ = write!(line, " {name}={}", self.wire_field_value(name));
        }
        line
    }

    /// Emitter-side value of a [`WIRE_FIELDS_V1`] field.
    ///
    /// Panics on a manifest name with no struct mapping — the manifest
    /// round-trip unit test catches that at `cargo test` time, so a manifest
    /// entry cannot ship without its accessor arm.
    fn wire_field_value(&self, name: &str) -> String {
        match name {
            "base_exit_code" => self.base_exit_code.to_string(),
            "verified" => self.verified.to_string(),
            "failed" => self.failed.to_string(),
            "errors" => self.errors.to_string(),
            "warnings" => self.warnings.to_string(),
            "assumed" => self.assumed.to_string(),
            "trusted" => self.trusted.to_string(),
            "skipped" => self.skipped.to_string(),
            "verified_with_axiom_deps" => self.verified_with_axiom_deps.to_string(),
            "unverified_axioms" => self.unverified_axioms.to_string(),
            "vacuous" => self.vacuous.to_string(),
            "evidence_gaps" => self.evidence_gaps.to_string(),
            "proof_assert_verified" => self.proof_assert_verified.to_string(),
            "proof_assert_inconclusive" => self.proof_assert_inconclusive.to_string(),
            "verified_native_only" => self.verified_native_only.to_string(),
            "proof_assert_failed" => self.proof_assert_failed.to_string(),
            "proof_assert_errors" => self.proof_assert_errors.to_string(),
            "panics" => self.panics.to_string(),
            "demoted" => self.demoted.to_string(),
            "parse_errors" => self.parse_errors.to_string(),
            "termination_errors" => self.termination_errors.to_string(),
            "logic_recursion_errors" => self.logic_recursion_errors.to_string(),
            "erasure_errors" => self.erasure_errors.to_string(),
            other => unreachable!("WIRE_FIELDS_V1 field {other} has no emitter mapping"),
        }
    }

    /// Decoder-side store of a [`WIRE_FIELDS_V1`] field. `None` = unparsable
    /// value (the caller fails the whole line closed).
    ///
    /// Panics on a manifest name with no struct mapping, mirroring
    /// [`Self::wire_field_value`]; the manifest round-trip unit test catches
    /// that before any decoder can ship.
    fn set_wire_field(&mut self, name: &str, value: &str) -> Option<()> {
        match name {
            "base_exit_code" => self.base_exit_code = value.parse().ok()?,
            "verified" => self.verified = value.parse().ok()?,
            "failed" => self.failed = value.parse().ok()?,
            "errors" => self.errors = value.parse().ok()?,
            "warnings" => self.warnings = value.parse().ok()?,
            "assumed" => self.assumed = value.parse().ok()?,
            "trusted" => self.trusted = value.parse().ok()?,
            "skipped" => self.skipped = value.parse().ok()?,
            "verified_with_axiom_deps" => self.verified_with_axiom_deps = value.parse().ok()?,
            "unverified_axioms" => self.unverified_axioms = value.parse().ok()?,
            "vacuous" => self.vacuous = value.parse().ok()?,
            "evidence_gaps" => self.evidence_gaps = value.parse().ok()?,
            "proof_assert_verified" => self.proof_assert_verified = value.parse().ok()?,
            "proof_assert_inconclusive" => self.proof_assert_inconclusive = value.parse().ok()?,
            "verified_native_only" => self.verified_native_only = value.parse().ok()?,
            "proof_assert_failed" => self.proof_assert_failed = value.parse().ok()?,
            "proof_assert_errors" => self.proof_assert_errors = value.parse().ok()?,
            "panics" => self.panics = value.parse().ok()?,
            "demoted" => self.demoted = value.parse().ok()?,
            "parse_errors" => self.parse_errors = value.parse().ok()?,
            "termination_errors" => self.termination_errors = value.parse().ok()?,
            "logic_recursion_errors" => self.logic_recursion_errors = value.parse().ok()?,
            "erasure_errors" => self.erasure_errors = value.parse().ok()?,
            other => unreachable!("WIRE_FIELDS_V1 field {other} has no decoder mapping"),
        }
        Some(())
    }

    /// Parse a wire line into a `StructuredVerificationResult`.
    ///
    /// Returns `None` if the line doesn't start with the expected prefix or
    /// omits required fields. Unknown keys are ignored for forward
    /// compatibility. The known-key set and the required-field mask both
    /// derive from [`WIRE_FIELDS_V1`], so the decoder cannot drift from the
    /// emitter or from the checked-in conformance fixture.
    #[must_use]
    pub fn from_wire_line(line: &str) -> Option<Self> {
        const REQUIRED_FIELDS: u32 = wire_required_mask();

        let rest = line.strip_prefix(WIRE_PREFIX)?.trim_start();
        let mut result = Self::default();
        let mut seen_fields = 0u32;

        for pair in rest.split_whitespace() {
            let (key, value) = pair.split_once('=')?;
            // Forward compatibility: ignore keys the manifest does not know.
            let Some(index) = WIRE_FIELDS_V1.iter().position(|(name, _)| *name == key) else {
                continue;
            };
            result.set_wire_field(key, value)?;
            seen_fields |= 1 << index;
        }

        (seen_fields & REQUIRED_FIELDS == REQUIRED_FIELDS).then_some(result)
    }

    /// Merge another result into this one by summing counters.
    ///
    /// After merging, `base_exit_code` is normalized from the merged counters
    /// while preserving a nonzero producer-provided base code when no counter
    /// explains the failure.
    pub fn merge(&mut self, other: &Self) {
        let producer_base_exit_code =
            preserve_nonzero_exit_code(self.base_exit_code, other.base_exit_code);

        self.verified += other.verified;
        self.failed += other.failed;
        self.errors += other.errors;
        self.warnings += other.warnings;
        self.assumed += other.assumed;
        self.trusted += other.trusted;
        self.skipped += other.skipped;
        self.verified_with_axiom_deps += other.verified_with_axiom_deps;
        self.unverified_axioms += other.unverified_axioms;
        self.vacuous += other.vacuous;
        self.evidence_gaps += other.evidence_gaps;
        self.proof_assert_verified += other.proof_assert_verified;
        self.verified_native_only += other.verified_native_only;
        self.proof_assert_failed += other.proof_assert_failed;
        self.proof_assert_errors += other.proof_assert_errors;
        self.panics += other.panics;
        self.demoted += other.demoted;
        self.parse_errors += other.parse_errors;
        self.termination_errors += other.termination_errors;
        self.logic_recursion_errors += other.logic_recursion_errors;
        self.erasure_errors += other.erasure_errors;

        self.base_exit_code = producer_base_exit_code;
        self.normalize_exit_code();
    }

    /// True when the run examined no proof obligation at all.
    ///
    /// Every counter in the record is zero, so the engine compiled the input
    /// and then had nothing to say about it — the usual cause being a file or
    /// crate that carries no contracts. A caller that asked for a verdict must
    /// not read that silence as success: nothing was proved.
    ///
    /// `base_exit_code` is deliberately excluded. It is derived from these same
    /// counters by [`Self::normalize_exit_code`], so including it would make
    /// the predicate depend on its own consequence.
    #[must_use]
    pub fn examined_nothing(&self) -> bool {
        self.verified == 0
            && self.failed == 0
            && self.errors == 0
            && self.warnings == 0
            && self.assumed == 0
            && self.trusted == 0
            && self.skipped == 0
            && self.verified_with_axiom_deps == 0
            && self.unverified_axioms == 0
            && self.vacuous == 0
            && self.evidence_gaps == 0
            && self.proof_assert_verified == 0
            && self.proof_assert_failed == 0
            && self.proof_assert_errors == 0
            && self.panics == 0
            && self.demoted == 0
            && self.parse_errors == 0
            && self.termination_errors == 0
            && self.logic_recursion_errors == 0
            && self.erasure_errors == 0
    }

    /// Return the fail-closed process/status code represented by this record.
    ///
    /// Structured counters are authoritative whenever they explain a nonzero
    /// result. A producer-provided nonzero `base_exit_code` is preserved only
    /// for older/malformed records where no counter explains the failure.
    #[must_use]
    pub fn effective_exit_code(&self) -> i32 {
        match self.compute_exit_code() {
            0 => self.base_exit_code,
            computed => computed,
        }
    }

    /// Rewrite `base_exit_code` to the fail-closed status represented by this record.
    pub fn normalize_exit_code(&mut self) {
        self.base_exit_code = self.effective_exit_code();
    }

    /// Recompute exit code from counters using driver precedence.
    ///
    /// Priority: parse errors (3) > failures (1) > errors/soundness gaps (2) > 0.
    fn compute_exit_code(&self) -> i32 {
        if self.parse_errors > 0 {
            return 3;
        }
        if self.termination_errors > 0 || self.logic_recursion_errors > 0 || self.erasure_errors > 0
        {
            return 2;
        }

        let has_failed = self.failed > 0 || self.proof_assert_failed > 0;
        let has_errors = self.errors > 0 || self.proof_assert_errors > 0 || self.panics > 0;

        if has_failed {
            1
        } else if has_errors || self.has_soundness_gap() {
            2
        } else {
            0
        }
    }

    /// True when the run carries a soundness gap: something was accepted
    /// without proof (trusted, skipped, assumed, axiom-dependent, vacuous) or
    /// verified without accepted evidence. Gaps alone force exit 2.
    #[must_use]
    pub fn has_soundness_gap(&self) -> bool {
        self.trusted > 0
            || self.skipped > 0
            || self.assumed > 0
            || self.verified_with_axiom_deps > 0
            || self.unverified_axioms > 0
            || self.vacuous > 0
            || self.evidence_gaps > 0
    }
}

fn preserve_nonzero_exit_code(current: i32, incoming: i32) -> i32 {
    if current != 0 {
        current
    } else {
        incoming
    }
}

// ---------------------------------------------------------------------------
// Wire values and per-obligation diagnostic records
// ---------------------------------------------------------------------------

/// Bytes that travel unescaped inside a `key=value` wire field.
fn is_plain_wire_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.' | b':' | b'/' | b'@')
}

/// Percent-encode a value for a `key=value` wire field.
///
/// Every byte outside `[A-Za-z0-9_.:/@-]` becomes `%XX` (upper-case hex), so
/// an encoded value never contains whitespace, `=` or a literal `%`, and a
/// wire line stays splittable on spaces. This is the encoding
/// `trust-wp-rustc` uses for `TRUST_WP_DIAGNOSTIC:v1` fields; the exact
/// inverse is [`decode_wire_value`].
#[must_use]
pub fn encode_wire_value(value: &str) -> String {
    use std::fmt::Write as _;

    let mut encoded = String::with_capacity(value.len());
    for byte in value.bytes() {
        if is_plain_wire_byte(byte) {
            encoded.push(byte as char);
        } else {
            let _ = write!(encoded, "%{byte:02X}");
        }
    }
    encoded
}

/// Decode a value produced by [`encode_wire_value`].
///
/// Malformed escapes (`%` not followed by two hex digits) are kept verbatim
/// rather than rejected, so a consumer still sees the field; decoded bytes
/// that are not valid UTF-8 are replaced with U+FFFD.
#[must_use]
pub fn decode_wire_value(value: &str) -> String {
    let bytes = value.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            let hi = (bytes[i + 1] as char).to_digit(16);
            let lo = (bytes[i + 2] as char).to_digit(16);
            if let (Some(hi), Some(lo)) = (hi, lo) {
                // Both digits are < 16, so the product fits a byte.
                #[allow(clippy::cast_possible_truncation)]
                decoded.push((hi * 16 + lo) as u8);
                i += 3;
                continue;
            }
        }
        decoded.push(bytes[i]);
        i += 1;
    }
    String::from_utf8(decoded)
        .unwrap_or_else(|err| String::from_utf8_lossy(err.as_bytes()).into_owned())
}

/// One `TRUST_WP_DIAGNOSTIC:v1` line, decoded.
///
/// `trust-wp-rustc` emits one such line per obligation that did not verify
/// cleanly (failed, unknown, assumed, evidence gap) when
/// `TRUST_WP_RESULT_PROTOCOL` is set; clean obligations emit nothing. The
/// four named fields are always present; every field — including those four
/// — is also kept, decoded and in wire order, in [`fields`](Self::fields), so
/// consumers can read keys added by newer producers without a schema change.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VerificationDiagnosticRecord {
    /// Fully qualified path of the function the obligation belongs to.
    pub def_path: String,
    /// Obligation kind, e.g. `function_contract`, `proof_assert`, `loop_preservation`.
    pub kind: String,
    /// `verified`, `failed`, `assumed`, `unknown` or `other`.
    pub status: String,
    /// `none`, `counterexample`, or the engine's unknown/assumed reason text.
    pub reason: String,
    /// Every `key=value` field of the line, decoded, in wire order.
    pub fields: Vec<(String, String)>,
}

impl VerificationDiagnosticRecord {
    /// Parse a diagnostic wire line.
    ///
    /// Returns `None` when the prefix is not `TRUST_WP_DIAGNOSTIC:v1` or any of
    /// `def_path`, `kind`, `status` is missing. Unknown keys are kept.
    #[must_use]
    pub fn from_wire_line(line: &str) -> Option<Self> {
        let rest = line.trim_end().strip_prefix(DIAGNOSTIC_WIRE_PREFIX)?;
        if !rest.is_empty() && !rest.starts_with(char::is_whitespace) {
            return None;
        }
        let mut record = Self::default();
        for token in rest.split_whitespace() {
            let (key, raw) = token.split_once('=')?;
            let value = decode_wire_value(raw);
            match key {
                "def_path" => record.def_path.clone_from(&value),
                "kind" => record.kind.clone_from(&value),
                "status" => record.status.clone_from(&value),
                "reason" => record.reason.clone_from(&value),
                _ => {}
            }
            record.fields.push((key.to_string(), value));
        }
        let has = |key: &str| record.fields.iter().any(|(k, _)| k == key);
        (has("def_path") && has("kind") && has("status")).then_some(record)
    }

    /// Look up a field by key (decoded value, sentinels included).
    #[must_use]
    pub fn field(&self, key: &str) -> Option<&str> {
        self.fields
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
    }

    /// Look up a field, mapping the producer's `none` sentinel to `None`.
    #[must_use]
    pub fn field_opt(&self, key: &str) -> Option<&str> {
        self.field(key).filter(|value| *value != NONE_SENTINEL)
    }

    /// Look up a numeric field. `none`, a missing key and an unparsable value
    /// are all `None` — a consumer must not distinguish them by guessing.
    #[must_use]
    pub fn field_u64(&self, key: &str) -> Option<u64> {
        self.field_opt(key).and_then(|value| value.parse().ok())
    }

    /// Look up a tri-state boolean field.
    ///
    /// `Some(Some(bool))` for `true`/`false`, `Some(None)` when the producer
    /// said `unknown` (it had no evidence to report), `None` when the key is
    /// absent or holds something else.
    #[must_use]
    pub fn field_tristate_bool(&self, key: &str) -> Option<Option<bool>> {
        match self.field(key) {
            Some("true") => Some(Some(true)),
            Some("false") => Some(Some(false)),
            Some(UNKNOWN_SENTINEL) => Some(None),
            _ => None,
        }
    }

    /// Fields this record's named accessors do not cover, in wire order.
    ///
    /// Keys a newer producer added arrive here rather than being dropped.
    pub fn extra<'a>(
        &'a self,
        known: &'a [&'a str],
    ) -> impl Iterator<Item = (&'a str, &'a str)> + 'a {
        self.fields
            .iter()
            .filter(move |(key, _)| !known.contains(&key.as_str()))
            .map(|(key, value)| (key.as_str(), value.as_str()))
    }

    /// Re-encode the record as a wire line, preserving field order.
    #[must_use]
    pub fn to_wire_line(&self) -> String {
        let mut line = String::from(DIAGNOSTIC_WIRE_PREFIX);
        for (key, value) in &self.fields {
            line.push(' ');
            line.push_str(key);
            line.push('=');
            line.push_str(&encode_wire_value(value));
        }
        line
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Path of the checked-in wire-field conformance fixture.
    fn wire_fixture_path() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/creusot_compat/wire_fields.v1.txt")
    }

    /// The checked-in fixture must equal the manifest the code is built from.
    ///
    /// Update path when a field change is intended: regenerate with
    /// `TRUST_WP_BLESS_WIRE_FIXTURE=1 cargo test -p trust-wp-core --lib
    /// wire_manifest`, commit the fixture TOGETHER with the manifest change,
    /// and teach the Python mirrors — their pytest pins against the same file
    /// name exactly what is missing.
    #[test]
    fn wire_manifest_fixture_matches_code() {
        let path = wire_fixture_path();
        let expected = wire_fields_v1_manifest();
        if std::env::var_os("TRUST_WP_BLESS_WIRE_FIXTURE").is_some() {
            std::fs::write(&path, &expected)
                .unwrap_or_else(|err| panic!("bless: cannot write {}: {err}", path.display()));
        }
        let on_disk = std::fs::read_to_string(&path).unwrap_or_else(|err| {
            panic!(
                "cannot read {}: {err}\nregenerate: TRUST_WP_BLESS_WIRE_FIXTURE=1 \
                 cargo test -p trust-wp-core --lib wire_manifest",
                path.display()
            )
        });
        assert_eq!(
            on_disk, expected,
            "tests/creusot_compat/wire_fields.v1.txt no longer matches WIRE_FIELDS_V1. \
             If the field change is intended: TRUST_WP_BLESS_WIRE_FIXTURE=1 cargo test \
             -p trust-wp-core --lib wire_manifest, commit BOTH files, and update the \
             Python decoders (tests/creusot_compat/harness_model.py, \
             scripts/compare_baselines.py) — their pytest pins will fail until they \
             match this fixture."
        );
    }

    /// Every manifest field must be wired to a struct member on both the
    /// emitter and decoder sides (distinct per-field values, so a missing or
    /// crossed accessor arm breaks the round-trip), and the emitted line must
    /// render exactly the manifest keys in manifest order.
    #[test]
    fn wire_manifest_drives_emitter_and_decoder() {
        let mut result = StructuredVerificationResult::default();
        for (index, (name, _)) in WIRE_FIELDS_V1.iter().enumerate() {
            result
                .set_wire_field(name, &(index + 1).to_string())
                .unwrap_or_else(|| panic!("manifest field {name} rejected a numeric value"));
        }

        let line = result.to_wire_line();
        let emitted_keys: Vec<&str> = line
            .strip_prefix(WIRE_PREFIX)
            .expect("wire line must carry the v1 prefix")
            .split_whitespace()
            .map(|pair| pair.split_once('=').expect("key=value").0)
            .collect();
        let manifest_keys: Vec<&str> = WIRE_FIELDS_V1.iter().map(|(name, _)| *name).collect();
        assert_eq!(
            emitted_keys, manifest_keys,
            "to_wire_line must render exactly WIRE_FIELDS_V1, in order"
        );

        let parsed = StructuredVerificationResult::from_wire_line(&line)
            .expect("a freshly emitted line must parse");
        assert_eq!(parsed, result, "manifest round-trip must be lossless");
    }

    /// The manifest's Required/Optional classification is what the decoder
    /// enforces: dropping any required key fails the line closed, dropping any
    /// optional key keeps it parseable.
    #[test]
    fn wire_manifest_presence_governs_decoder() {
        let full = StructuredVerificationResult::default().to_wire_line();
        for (name, presence) in WIRE_FIELDS_V1 {
            let without = full
                .split_whitespace()
                .filter(|pair| !pair.starts_with(&format!("{name}=")))
                .collect::<Vec<_>>()
                .join(" ");
            let parsed = StructuredVerificationResult::from_wire_line(&without);
            match presence {
                WireFieldPresence::Required => assert!(
                    parsed.is_none(),
                    "dropping required field {name} must fail the line closed"
                ),
                WireFieldPresence::Optional => assert!(
                    parsed.is_some(),
                    "dropping optional field {name} must keep the line parseable"
                ),
            }
        }
    }

    #[test]
    fn roundtrip_default() {
        let result = StructuredVerificationResult::default();
        let line = result.to_wire_line();
        let parsed = StructuredVerificationResult::from_wire_line(&line).unwrap();
        assert_eq!(result, parsed);
    }

    #[test]
    fn roundtrip_with_values() {
        let result = StructuredVerificationResult {
            base_exit_code: 1,
            verified: 5,
            failed: 2,
            errors: 1,
            warnings: 3,
            assumed: 0,
            trusted: 1,
            skipped: 0,
            verified_with_axiom_deps: 0,
            unverified_axioms: 2,
            vacuous: 4,
            evidence_gaps: 5,
            proof_assert_inconclusive: 6,
            proof_assert_verified: 3,
            verified_native_only: 0,
            proof_assert_failed: 1,
            proof_assert_errors: 0,
            panics: 0,
            demoted: 0,
            parse_errors: 0,
            termination_errors: 0,
            logic_recursion_errors: 0,
            erasure_errors: 0,
        };
        let line = result.to_wire_line();
        assert!(line.starts_with(WIRE_PREFIX));
        let parsed = StructuredVerificationResult::from_wire_line(&line).unwrap();
        assert_eq!(result, parsed);
    }

    /// A run whose only obligations are `proof_assert!` has proved something,
    /// and must not be mistaken for a run that examined nothing.
    #[test]
    fn a_proof_assert_only_run_has_examined_something() {
        let mut wire = StructuredVerificationResult::default();
        assert!(wire.examined_nothing());
        wire.proof_assert_verified = 1;
        assert!(!wire.examined_nothing());
        assert_eq!(wire.effective_exit_code(), 0);
    }

    /// The field is optional on the wire: a producer that predates it omits the
    /// key, and the record must still parse.
    #[test]
    fn proof_assert_verified_round_trips_and_is_optional() {
        let mut wire = StructuredVerificationResult::default();
        wire.proof_assert_verified = 4;
        let line = wire.to_wire_line();
        assert!(line.contains("proof_assert_verified=4"), "{line}");
        let parsed = StructuredVerificationResult::from_wire_line(&line)
            .expect("a freshly written line must parse");
        assert_eq!(parsed.proof_assert_verified, 4);

        let without = line
            .split_whitespace()
            .filter(|pair| !pair.starts_with("proof_assert_verified="))
            .collect::<Vec<_>>()
            .join(" ");
        let older = StructuredVerificationResult::from_wire_line(&without)
            .expect("a record without the optional key must still parse");
        assert_eq!(older.proof_assert_verified, 0);
    }

    #[test]
    fn from_wire_line_rejects_wrong_prefix() {
        assert!(
            StructuredVerificationResult::from_wire_line("TRUST_WP_RESULT:v2 verified=1").is_none()
        );
        assert!(StructuredVerificationResult::from_wire_line("NOT_TRUST_WP verified=1").is_none());
    }

    #[test]
    fn from_wire_line_ignores_unknown_keys() {
        let line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=3 failed=0 errors=0 warnings=0 \
                     assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 \
                     unverified_axioms=0 vacuous=0 evidence_gaps=0 proof_assert_failed=0 \
                     proof_assert_errors=0 panics=0 demoted=0 \
                     parse_errors=0 termination_errors=0 logic_recursion_errors=0 \
                     erasure_errors=0 future_field=42";
        let parsed = StructuredVerificationResult::from_wire_line(line).unwrap();
        assert_eq!(parsed.verified, 3);
        assert_eq!(parsed.base_exit_code, 0);
    }

    #[test]
    fn from_wire_line_rejects_malformed_value() {
        let line = "TRUST_WP_RESULT:v1 base_exit_code=abc";
        assert!(StructuredVerificationResult::from_wire_line(line).is_none());
    }

    #[test]
    fn merge_sums_counters() {
        let mut a = StructuredVerificationResult {
            base_exit_code: 0,
            verified: 3,
            failed: 0,
            errors: 0,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            base_exit_code: 1,
            verified: 2,
            failed: 1,
            errors: 0,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.verified, 5);
        assert_eq!(a.failed, 1);
        // Recomputed: failed > 0 → exit code 1
        assert_eq!(a.base_exit_code, 1);
    }

    #[test]
    fn merge_recomputes_exit_code_from_merged_counters() {
        let mut a = StructuredVerificationResult {
            base_exit_code: 0,
            verified: 2,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            base_exit_code: 2,
            errors: 3,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.base_exit_code, 2);
    }

    #[test]
    fn merge_preserves_unexplained_nonzero_base_exit_code() {
        let mut a = StructuredVerificationResult {
            base_exit_code: 2,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            verified: 3,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.base_exit_code, 2);
    }

    #[test]
    fn merge_recomputes_failure_precedence_over_soundness_gap() {
        let mut a = StructuredVerificationResult {
            skipped: 1,
            ..Default::default()
        };
        a.normalize_exit_code();

        let b = StructuredVerificationResult {
            base_exit_code: 1,
            failed: 1,
            ..Default::default()
        };

        a.merge(&b);
        assert_eq!(a.base_exit_code, 1);
    }

    #[test]
    fn merge_parse_errors_take_highest_priority() {
        let mut a = StructuredVerificationResult {
            base_exit_code: 1,
            failed: 1,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            parse_errors: 1,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.base_exit_code, 3);
    }

    #[test]
    fn compute_exit_code_assumed_only() {
        let result = StructuredVerificationResult {
            assumed: 2,
            ..Default::default()
        };
        assert_eq!(result.compute_exit_code(), 2);
    }

    #[test]
    fn effective_exit_code_fails_closed_for_structural_error_counters() {
        let parse = StructuredVerificationResult {
            base_exit_code: 0,
            parse_errors: 1,
            ..Default::default()
        };
        assert_eq!(parse.effective_exit_code(), 3);

        let termination = StructuredVerificationResult {
            base_exit_code: 0,
            termination_errors: 1,
            ..Default::default()
        };
        assert_eq!(termination.effective_exit_code(), 2);

        let logic_recursion = StructuredVerificationResult {
            base_exit_code: 0,
            logic_recursion_errors: 1,
            ..Default::default()
        };
        assert_eq!(logic_recursion.effective_exit_code(), 2);
    }

    #[test]
    fn normalize_exit_code_sets_result_status_for_soundness_gaps() {
        let cases = [
            StructuredVerificationResult {
                assumed: 1,
                ..Default::default()
            },
            StructuredVerificationResult {
                trusted: 1,
                ..Default::default()
            },
            StructuredVerificationResult {
                skipped: 1,
                ..Default::default()
            },
        ];

        for mut result in cases {
            result.normalize_exit_code();
            assert_eq!(result.base_exit_code, 2, "{result:?}");
        }
    }

    #[test]
    fn compute_exit_code_axiom_deps_only() {
        let result = StructuredVerificationResult {
            verified_with_axiom_deps: 1,
            ..Default::default()
        };
        assert_eq!(result.compute_exit_code(), 2);
    }

    #[test]
    fn compute_exit_code_trusted_or_skipped_are_soundness_gaps() {
        let trusted = StructuredVerificationResult {
            trusted: 1,
            ..Default::default()
        };
        assert_eq!(trusted.compute_exit_code(), 2);

        let skipped = StructuredVerificationResult {
            skipped: 1,
            ..Default::default()
        };
        assert_eq!(skipped.compute_exit_code(), 2);
    }

    #[test]
    fn compute_exit_code_mixed_soundness_gaps_are_errors() {
        let trusted = StructuredVerificationResult {
            verified: 2,
            trusted: 1,
            ..Default::default()
        };
        assert_eq!(trusted.compute_exit_code(), 2);

        let skipped = StructuredVerificationResult {
            verified: 2,
            skipped: 1,
            ..Default::default()
        };
        assert_eq!(skipped.compute_exit_code(), 2);

        let assumed = StructuredVerificationResult {
            verified: 2,
            assumed: 1,
            ..Default::default()
        };
        assert_eq!(assumed.compute_exit_code(), 2);

        let axiom_deps = StructuredVerificationResult {
            verified: 2,
            verified_with_axiom_deps: 1,
            ..Default::default()
        };
        assert_eq!(axiom_deps.compute_exit_code(), 2);

        let unverified_axioms = StructuredVerificationResult {
            verified: 2,
            unverified_axioms: 1,
            ..Default::default()
        };
        assert_eq!(unverified_axioms.compute_exit_code(), 2);

        let vacuous = StructuredVerificationResult {
            verified: 2,
            vacuous: 1,
            ..Default::default()
        };
        assert_eq!(vacuous.compute_exit_code(), 2);

        let evidence_gap = StructuredVerificationResult {
            verified: 2,
            evidence_gaps: 1,
            ..Default::default()
        };
        assert_eq!(evidence_gap.compute_exit_code(), 2);
    }

    #[test]
    fn wire_line_is_single_line() {
        let result = StructuredVerificationResult {
            base_exit_code: 1,
            verified: 10,
            failed: 1,
            ..Default::default()
        };
        let line = result.to_wire_line();
        assert!(!line.contains('\n'));
    }

    #[test]
    fn from_wire_line_rejects_incomplete_payload() {
        assert!(StructuredVerificationResult::from_wire_line("TRUST_WP_RESULT:v1").is_none());
        assert!(StructuredVerificationResult::from_wire_line(
            "TRUST_WP_RESULT:v1 base_exit_code=0"
        )
        .is_none());
    }

    #[test]
    fn from_wire_line_rejects_legacy_payload_missing_soundness_gap_fields() {
        let line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=1 failed=0 errors=0 warnings=0 \
                    assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 \
                    proof_assert_failed=0 proof_assert_errors=0 panics=0 demoted=0 \
                    parse_errors=0 termination_errors=0 logic_recursion_errors=0";
        assert!(StructuredVerificationResult::from_wire_line(line).is_none());
    }

    #[test]
    fn from_wire_line_rejects_legacy_payload_missing_evidence_gaps() {
        let line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=1 failed=0 errors=0 warnings=0 \
                    assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 \
                    unverified_axioms=0 vacuous=0 proof_assert_failed=0 \
                    proof_assert_errors=0 panics=0 demoted=0 \
                    parse_errors=0 termination_errors=0 logic_recursion_errors=0";
        assert!(StructuredVerificationResult::from_wire_line(line).is_none());
    }

    #[test]
    fn from_wire_line_rejects_legacy_payload_missing_erasure_errors() {
        // Phase 5c: erasure_errors is a newly required field.
        let line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=1 failed=0 errors=0 warnings=0 \
                    assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 \
                    unverified_axioms=0 vacuous=0 evidence_gaps=0 proof_assert_failed=0 \
                    proof_assert_errors=0 panics=0 demoted=0 \
                    parse_errors=0 termination_errors=0 logic_recursion_errors=0";
        assert!(StructuredVerificationResult::from_wire_line(line).is_none());
    }

    #[test]
    fn effective_exit_code_fails_closed_for_erasure_errors() {
        // Phase 5c: erasure_errors triggers exit code 2 (encoding/structural error).
        let erasure = StructuredVerificationResult {
            base_exit_code: 0,
            erasure_errors: 1,
            ..Default::default()
        };
        assert_eq!(erasure.effective_exit_code(), 2);
    }

    #[test]
    fn merge_sums_erasure_errors() {
        let mut a = StructuredVerificationResult {
            erasure_errors: 1,
            ..Default::default()
        };
        let b = StructuredVerificationResult {
            erasure_errors: 2,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.erasure_errors, 3);
        // erasure_errors > 0 should normalize to exit code 2.
        assert_eq!(a.base_exit_code, 2);
    }

    #[test]
    fn wire_values_round_trip_through_percent_encoding() {
        let raw = "demo::f<T> (x = 1, y = \"two\") % done\n";
        let encoded = encode_wire_value(raw);
        assert!(!encoded.contains(' '));
        assert!(!encoded.contains('='));
        assert!(encoded.contains("%20"));
        assert_eq!(decode_wire_value(&encoded), raw);
        // Plain bytes stay plain; the encoder and decoder agree on the alphabet.
        assert_eq!(encode_wire_value("a-b_c.d:e/f@g0"), "a-b_c.d:e/f@g0");
        assert_eq!(decode_wire_value("a-b_c.d:e/f@g0"), "a-b_c.d:e/f@g0");
    }

    #[test]
    fn malformed_percent_escapes_are_kept_verbatim() {
        assert_eq!(decode_wire_value("100%"), "100%");
        assert_eq!(decode_wire_value("%zz"), "%zz");
        assert_eq!(decode_wire_value("%4"), "%4");
        assert_eq!(decode_wire_value("%41%"), "A%");
        // Non-UTF-8 bytes decode lossily instead of panicking.
        assert_eq!(decode_wire_value("%FF"), "\u{FFFD}");
        // Multi-byte UTF-8 input around an escape is not sliced mid-character.
        assert_eq!(decode_wire_value("é%41é"), "éAé");
    }

    #[test]
    fn diagnostic_records_parse_and_round_trip() {
        let line = format!(
            "{DIAGNOSTIC_WIRE_PREFIX} def_path=demo::increment%3CT%3E kind=function_contract \
             status=failed reason=counterexample solve_time_ms=12 assertions=7 timeout_ms=60000 \
             ay_result=sat accepted_for_consumer=true future_key=%7Bjson%7D"
        );
        let record = VerificationDiagnosticRecord::from_wire_line(&line).unwrap();
        assert_eq!(record.def_path, "demo::increment<T>");
        assert_eq!(record.kind, "function_contract");
        assert_eq!(record.status, "failed");
        assert_eq!(record.reason, "counterexample");
        assert_eq!(record.field("solve_time_ms"), Some("12"));
        assert_eq!(record.field("future_key"), Some("{json}"));
        assert_eq!(record.field("missing"), None);
        assert_eq!(record.fields.len(), 10);
        // Re-encoding preserves order and bytes.
        assert_eq!(
            record.to_wire_line(),
            line.split_whitespace().collect::<Vec<_>>().join(" ")
        );
        let again = VerificationDiagnosticRecord::from_wire_line(&record.to_wire_line()).unwrap();
        assert_eq!(again, record);
    }

    #[test]
    fn typed_accessors_map_the_producer_sentinels() {
        let record = VerificationDiagnosticRecord::from_wire_line(
            "TRUST_WP_DIAGNOSTIC:v1 def_path=demo::f kind=function_contract status=unknown \
             reason=timeout solve_time_ms=12 timeout_ms=none assertions=oops \
             accepted_for_consumer=false model_validated=unknown replay_sha256=none \
             verification_level=FullyVerified brand_new=%7B%7D",
        )
        .unwrap();

        assert_eq!(record.field_u64("solve_time_ms"), Some(12));
        // `none`, unparsable and absent are all None: never guess a number.
        assert_eq!(record.field_u64("timeout_ms"), None);
        assert_eq!(record.field_u64("assertions"), None);
        assert_eq!(record.field_u64("missing"), None);

        assert_eq!(
            record.field_opt("verification_level"),
            Some("FullyVerified")
        );
        assert_eq!(record.field_opt("replay_sha256"), None);
        assert_eq!(record.field("replay_sha256"), Some("none"));

        assert_eq!(
            record.field_tristate_bool("accepted_for_consumer"),
            Some(Some(false))
        );
        assert_eq!(record.field_tristate_bool("model_validated"), Some(None));
        assert_eq!(record.field_tristate_bool("missing"), None);
        assert_eq!(record.field_tristate_bool("reason"), None);

        let extra: Vec<_> = record
            .extra(&["def_path", "kind", "status", "reason"])
            .collect();
        assert!(extra.contains(&("brand_new", "{}")));
        assert!(!extra.iter().any(|(key, _)| *key == "def_path"));
    }

    #[test]
    fn soundness_gaps_are_visible_to_consumers() {
        let mut result = StructuredVerificationResult::default();
        assert!(!result.has_soundness_gap());
        result.trusted = 1;
        assert!(result.has_soundness_gap());
        assert_eq!(result.effective_exit_code(), 2);
    }

    #[test]
    fn diagnostic_records_reject_other_lines() {
        assert!(VerificationDiagnosticRecord::from_wire_line("trust-wp: demo::f FAILED").is_none());
        assert!(VerificationDiagnosticRecord::from_wire_line(WIRE_PREFIX).is_none());
        // Wrong version, or a prefix that merely shares the start.
        assert!(VerificationDiagnosticRecord::from_wire_line(
            "TRUST_WP_DIAGNOSTIC:v2 def_path=a kind=b status=c"
        )
        .is_none());
        assert!(VerificationDiagnosticRecord::from_wire_line(
            "TRUST_WP_DIAGNOSTIC:v1x def_path=a kind=b status=c"
        )
        .is_none());
        // Required fields.
        assert!(VerificationDiagnosticRecord::from_wire_line(
            "TRUST_WP_DIAGNOSTIC:v1 def_path=a kind=b"
        )
        .is_none());
        // A token without `=` is malformed.
        assert!(VerificationDiagnosticRecord::from_wire_line(
            "TRUST_WP_DIAGNOSTIC:v1 def_path=a kind=b status=c oops"
        )
        .is_none());
    }
}

#[cfg(test)]
mod native_only_authority_tests {
    use super::*;

    #[test]
    fn a_hole_rule_makes_a_proof_unreplayable_elsewhere() {
        let holey = "(assume t0 (< x 0))\n(step t1 (cl false) :rule hole)\n";
        assert!(!alethe_proof_is_externally_checkable(holey));

        let clean = "(assume t0 (< x 0))\n(step t1 (cl false) :rule la_generic :args (1))\n";
        assert!(alethe_proof_is_externally_checkable(clean));
    }

    /// `hole` must be matched as a RULE, not as a substring. A rule whose name
    /// merely begins with those letters, or a step that mentions the word
    /// somewhere else, is checkable.
    #[test]
    fn the_word_hole_elsewhere_does_not_count() {
        assert!(alethe_proof_is_externally_checkable(
            "(step t1 (cl (= whole 1)) :rule eq_reflexive)"
        ));
        assert!(alethe_proof_is_externally_checkable(
            "(step t1 (cl false) :rule resolution) ; no hole here"
        ));
        // ...but the real spelling is caught however it is spaced.
        assert!(!alethe_proof_is_externally_checkable(
            "(step t1 (cl false) :rule   hole)"
        ));
    }

    #[test]
    fn the_counter_round_trips_and_is_optional() {
        let mut wire = StructuredVerificationResult::default();
        wire.verified = 7;
        wire.verified_native_only = 2;
        let line = wire.to_wire_line();
        assert!(line.contains("verified_native_only=2"), "{line}");
        let parsed = StructuredVerificationResult::from_wire_line(&line).expect("round trip");
        assert_eq!(parsed.verified_native_only, 2);
        assert_eq!(parsed.verified, 7);

        // A record from a producer that predates the field, or cannot determine
        // it, must still decode.
        let older: String = line
            .split_whitespace()
            .filter(|field| !field.starts_with("verified_native_only="))
            .collect::<Vec<_>>()
            .join(" ");
        let parsed =
            StructuredVerificationResult::from_wire_line(&older).expect("the field is optional");
        assert_eq!(parsed.verified_native_only, 0);
    }

    /// Native-only authority is a caveat on a verified result, never a failure:
    /// it must not change the exit code on its own.
    #[test]
    fn native_only_authority_is_not_an_error() {
        let mut wire = StructuredVerificationResult::default();
        wire.verified = 3;
        wire.verified_native_only = 3;
        assert_eq!(
            wire.compute_exit_code(),
            0,
            "verified with a caveat is still verified"
        );
        assert!(!wire.has_soundness_gap());
    }
}
