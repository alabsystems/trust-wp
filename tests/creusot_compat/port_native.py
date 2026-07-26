#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""R4 mechanical-tier port: Creusot attributes -> first-class native clauses.

Rewrites corpus tests whose spec surface is ENTIRELY mechanical-tier
(#[requires]/#[ensures] on fns, #[invariant]/#[variant] on while/loop loops)
into the native Trust clause grammar:

    #[requires(p)] #[ensures(q)] fn f(x: u64) -> u64 { .. }
        -> fn f(x: u64) -> u64 requires p ensures q { .. }

    #[invariant(i)] #[variant(v)] while c { .. }
        -> while c invariant i decreases v { .. }

The 2026-07-22 emitter extends the tool into the semantic tier: a `#[logic]`
fn whose body the pearlite→Clean translator accepts is ported by ROUTE —
an all-machine signature drops the attribute and stays a Rust fn (the E6
lane admits its MIR body as `trust_import_<mangled>`); an all-Int signature
is deleted and re-emitted as a def inside a `clean { .. }` island prepended
to the file. Any surviving reference to a deleted fn's name refuses (the
`by`-citation wiring is a later increment); island defs must arrive in
dependency order (the kernel's declaration order is strict).

FAIL-CLOSED, per file: any unhandled semantic-tier construct (pearlite!,
proof_assert!, snapshot!/ghost!, ...), any no-native-lane construct
(extern_spec!, trait contracts, impl Invariant, closure contracts), any
pearlite-only predicate syntax (`@` model deref, `^` prophecy final,
`.shallow_model()`, `Seq`/`Int` spec types), any for-loop invariant, or any
attribute the scanner cannot place refuses the WHOLE file with a recorded
reason. The port never guesses: an unported file simply stays on the legacy
surface.

Every ported file is parse-validated with the stage2 trustc (`-Zparse-only`)
so the emitted clause grammar is checked by the real compiler, not by this
script's opinion of it.

Usage:
    python3 tests/creusot_compat/port_native.py \
        --corpus <reference/creusot root> --out <ported mirror dir> \
        [--trustc <path>] [--report <json>]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from unittest import mock

# Constructs whose presence refuses the file (semantic tier / no native lane).
REFUSAL_PATTERNS: dict[str, re.Pattern[str]] = {
    "logic_attr": re.compile(r"#\[logic\b"),
    "law_attr": re.compile(r"#\[law\b"),
    "open_attr": re.compile(r"#\[open\b"),
    "predicate_attr": re.compile(r"#\[predicate\b"),
    "pearlite_macro": re.compile(r"\bpearlite!\s*[\{\(\[]"),
    "proof_assert": re.compile(r"\bproof_assert!\s*[\{\(\[]"),
    "snapshot": re.compile(r"\bsnapshot!\s*[\{\(\[]|\bSnapshot\b"),
    "ghost": re.compile(r"\bghost!\s*[\{\(\[]|\bGhost(Box)?\b|#\[check\(ghost\)\]"),
    "extern_spec": re.compile(r"\bextern_spec!\s*[\{\(\[]"),
    "trusted_attr": re.compile(r"#\[trusted\b"),
    "check_terminates": re.compile(r"#\[check\(terminates\)\]"),
    "terminates_attr": re.compile(r"#\[terminates\b"),
    "type_invariant_impl": re.compile(
        r"\bimpl(\s*<[^>]*>)?\s+Invariant(\s*<[^>]*>)?\s+for\b"
    ),
}

# Pearlite-only predicate syntax the native clause grammar does not admit.
# `==>`, `forall`, `exists`, `old(..)`, `result` ARE native spec vocabulary.
PREDICATE_REFUSALS: dict[str, re.Pattern[str]] = {
    "model_deref_at": re.compile(r"@"),
    "prophecy_final": re.compile(r"\^"),
    "shallow_model": re.compile(r"\.shallow_model\(\)|\.model\(\)"),
    "spec_types": re.compile(r"\bSeq\b|\bInt\b|\bFMap\b|\bFSet\b"),
    "view_call": re.compile(r"\.view\(\)"),
    # Creusot fn-contract reflection (`T::f.precondition((args,))`) is
    # semantic-tier vocabulary, not native clause grammar.
    "contract_reflection": re.compile(r"\.precondition\(|\.postcondition\("),
}

CONTRACT_ATTRS = ("requires", "ensures", "invariant", "variant")

# R4 §2 clause-tier rewrite: pearlite `forall<i: T> P` → the native E3
# spelling `forall i: T, P`. E3 admits ONE binder, clause-head only, over
# exactly this closed type set — everything else refuses with attribution.
E3_CLAUSE_BINDER_TYPES = ("nat", "u8", "u16", "u32", "u64", "bool")
CLAUSE_QUANT_RE = re.compile(r"\b(forall|exists)\s*<([^>]*)>")


def rewrite_clause_binders(pred: str) -> tuple[str | None, str | None]:
    """Rewrite one clause predicate's pearlite binder to the native spelling,
    or refuse with an attributed reason. FAIL-CLOSED on everything E3 does
    not admit: untyped binders (the probe's territory — no guessing),
    Int binders (the island/§3 reading), types outside the closed set
    (usize included), multiple binders or a non-head quantifier (E3 is
    single-binder, clause-head only — a non-head quantifier would PARSE and
    then fail elaboration, so it must never be emitted)."""
    matches = list(CLAUSE_QUANT_RE.finditer(pred))
    if not matches:
        return pred, None
    if len(matches) > 1:
        return None, "clause_binder_multi"
    m = matches[0]
    if not pred.lstrip().startswith(m.group(0)):
        return None, "clause_binder_not_head"
    inner = m.group(2).strip()
    if "," in inner:
        return None, "clause_binder_multi"
    if ":" not in inner:
        return None, "clause_binder_untyped"
    name, ty = (part.strip() for part in inner.split(":", 1))
    if ty == "Int":
        return None, "clause_binder_int"
    if ty not in E3_CLAUSE_BINDER_TYPES:
        return None, f"clause_binder_type_unsupported_{ty[:20]}"
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        return None, "clause_binder_pattern"
    rewritten = pred.replace(m.group(0), f"{m.group(1)} {name}: {ty},", 1)
    return rewritten, None


def _mask_rust_noncode(src: str) -> str:
    """Mask Rust comments and literals without changing offsets.

    Discovery regexes must never see syntax-looking text inside a string, byte
    string, C string, character literal, or nested block comment.  Keeping the
    byte-for-byte length (and newlines) lets spans found on the mask slice the
    original source safely.
    """

    out = list(src)
    length = len(src)

    def blank(start: int, end: int) -> None:
        for pos in range(start, end):
            if src[pos] not in "\r\n":
                out[pos] = " "

    def token_boundary(pos: int) -> bool:
        return pos == 0 or not (src[pos - 1].isalnum() or src[pos - 1] == "_")

    def raw_string_end(pos: int) -> int | None:
        if not token_boundary(pos):
            return None
        prefix_len = 0
        for prefix in ("br", "cr", "r"):
            if src.startswith(prefix, pos):
                prefix_len = len(prefix)
                break
        if not prefix_len:
            return None
        cursor = pos + prefix_len
        while cursor < length and src[cursor] == "#":
            cursor += 1
        if cursor >= length or src[cursor] != '"':
            return None
        hashes = src[pos + prefix_len : cursor]
        closing = '"' + hashes
        end = src.find(closing, cursor + 1)
        return length if end < 0 else end + len(closing)

    def quoted_end(quote_pos: int, quote: str) -> int:
        cursor = quote_pos + 1
        while cursor < length:
            char = src[cursor]
            if char == "\\":
                cursor += 2
                continue
            if char == quote:
                return cursor + 1
            cursor += 1
        return length

    index = 0
    while index < length:
        if src.startswith("//", index):
            end = src.find("\n", index + 2)
            end = length if end < 0 else end
            blank(index, end)
            index = end
            continue

        if src.startswith("/*", index):
            depth = 1
            cursor = index + 2
            while cursor < length and depth:
                if src.startswith("/*", cursor):
                    depth += 1
                    cursor += 2
                elif src.startswith("*/", cursor):
                    depth -= 1
                    cursor += 2
                else:
                    cursor += 1
            blank(index, cursor)
            index = cursor
            continue

        raw_end = raw_string_end(index)
        if raw_end is not None:
            blank(index, raw_end)
            index = raw_end
            continue

        prefix_len = 0
        quote = ""
        if token_boundary(index) and (
            src.startswith('b"', index) or src.startswith('c"', index)
        ):
            prefix_len, quote = 1, '"'
        elif token_boundary(index) and src.startswith("b'", index):
            prefix_len, quote = 1, "'"
        elif src[index] == '"':
            quote = '"'
        elif src[index] == "'":
            # `'name` and `'_` are lifetimes, while `'x'` is a character.
            cursor = index + 1
            if cursor < length and (src[cursor].isalpha() or src[cursor] == "_"):
                cursor += 1
                while cursor < length and (src[cursor].isalnum() or src[cursor] == "_"):
                    cursor += 1
                if cursor >= length or src[cursor] != "'":
                    index += 1
                    continue
            quote = "'"

        if quote:
            end = quoted_end(index + prefix_len, quote)
            blank(index, end)
            index = end
            continue

        index += 1

    return "".join(out)


def mask_noncode(src: str) -> str:
    """Mask comments and literals for syntax discovery/refusal scans."""
    return _mask_rust_noncode(src)


def find_attrs(src: str) -> list[tuple[int, int, str, str]]:
    """Every mechanical contract attribute as (start, end, kind, predicate).

    Balanced-paren extraction so multi-line predicates survive. Returns spans
    over the ORIGINAL source (comments included), sorted by position.
    """
    out: list[tuple[int, int, str, str]] = []
    masked = mask_noncode(src)
    for kind in CONTRACT_ATTRS:
        for m in re.finditer(rf"#\[{kind}\(", masked):
            depth = 1
            i = m.end()
            while i < len(masked) and depth:
                if masked[i] == "(":
                    depth += 1
                elif masked[i] == ")":
                    depth -= 1
                i += 1
            if depth:
                raise ValueError(f"unbalanced {kind} attribute at byte {m.start()}")
            # Expect the closing `]` immediately (modulo whitespace).
            j = i
            while j < len(masked) and masked[j] in " \t\r\n":
                j += 1
            if j >= len(masked) or masked[j] != "]":
                raise ValueError(f"malformed {kind} attribute at byte {m.start()}")
            out.append((m.start(), j + 1, kind, src[m.end() : i - 1].strip()))
    return sorted(out)


def next_code_token_line(src: str, pos: int) -> str:
    """The first non-attribute, non-empty code line at/after pos."""
    for line in src[pos:].splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("//") or stripped.startswith("#["):
            continue
        return stripped
    return ""


LOGIC_ATTR_RE = re.compile(r"#\[logic\b(?:\(([^]]*)\))?\]")
NEUTRAL_LOGIC_ARGS = ("inline", "opaque", "sealed")

PEARLITE_WRAP_RE = re.compile(r"^pearlite!\s*([{(])(.*)([})])$", re.S)


def unwrap_pearlite(body: str) -> str:
    """A logic body that is exactly one `pearlite! { E }` wrapper denotes E —
    the macro exists to switch creusot's parser into pearlite mode, which is
    precisely the mode the translator implements. Anything else (partial
    wrap, trailing code) is returned unchanged and refuses downstream."""
    m = PEARLITE_WRAP_RE.match(body.strip())
    if m and {"{": "}", "(": ")"}[m.group(1)] == m.group(3):
        return m.group(2).strip()
    return body


def extract_logic_fns(src: str) -> tuple[list[dict], str | None]:
    """Every `#[logic]` fn as spans + route + island rendering, or a refusal.

    Spans are found on an offset-preserving non-code mask so they slice the
    original cleanly without discovering declarations inside literals.
    Fail-closed: any logic fn this cannot fully account for refuses the
    whole file with an attributed reason.
    """
    from pearlite_to_clean import INT_SUFFIX_RE, Refused, translate_expr

    masked = mask_noncode(src)
    out: list[dict] = []
    for attr in LOGIC_ATTR_RE.finditer(masked):
        args = [a.strip() for a in (attr.group(1) or "").split(",") if a.strip()]
        semantic = [
            a
            for a in args
            if not (a == "open" or a.startswith("open(") or a in NEUTRAL_LOGIC_ARGS)
        ]
        if semantic:
            return [], "logic_attr_" + "_".join(sorted(set(semantic)))[:40]
        head = FN_HEAD_RE.search(masked, attr.end())
        if head is None:
            return [], "logic_attr_gap"
        gap = masked[attr.end() : head.start()]
        gap = re.sub(r"\bpub(\s*\([^)]*\))?", "", gap)
        gap = re.sub(r"\b(const|unsafe)\b", "", gap)
        if gap.strip():
            return [], "logic_attr_gap"
        if head.group(2):
            return [], "logic_generic_fn"
        brace = masked.find("{", head.end())
        semi = masked.find(";", head.end())
        if brace == -1 or (semi != -1 and semi < brace):
            return [], "logic_bodyless_decl"
        depth, i = 1, brace + 1
        while i < len(masked) and depth:
            if masked[i] == "{":
                depth += 1
            elif masked[i] == "}":
                depth -= 1
            i += 1
        if depth:
            return [], "logic_unbalanced_body"
        body = unwrap_pearlite(masked[brace + 1 : i - 1].strip())
        if not body:
            return [], "logic_empty_body"
        name = head.group(1)
        if re.search(rf"\b{re.escape(name)}\b", body):
            return [], "self_recursion_v1_2"
        try:
            clean = translate_expr(body)
        except Refused as refusal:
            return [], f"logic_body_{refusal}"
        sig = masked[head.end() : brace]
        close = sig.find(")")
        params = [
            (m.group(1), m.group(2))
            for m in re.finditer(
                r"([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([A-Za-z_][A-Za-z0-9_]*)", sig[:close]
            )
        ]
        ret = re.search(r"->\s*([A-Za-z_][A-Za-z0-9_]*)", sig[close:])
        types = [t for _, t in params] + ([ret.group(1)] if ret else [])
        if any(t == "Int" for t in types):
            # Island route — EXACTNESS: every type must be Int. A machine
            # param relaxed to Int widens the domain (different definition);
            # a bool return needs the Bool/Prop doctrine call. Both refuse.
            if ret is None:
                return [], "island_unit_return_v2"
            if not all(t == "Int" for t in types):
                return [], "island_mixed_sig_v2"
            binders = " ".join(f"({p} : Int)" for p, _ in params)
            rendered = f"def {name} {binders} : Int := {clean}".replace("  ", " ")
            out.append(
                {
                    "route": "island",
                    "name": name,
                    "attr_start": attr.start(),
                    "attr_end": attr.end(),
                    "fn_end": i,
                    "island_def": rendered,
                }
            )
        elif all(t == "bool" or INT_SUFFIX_RE.fullmatch(t) for t in types):
            out.append(
                {
                    "route": "e6_admission",
                    "name": name,
                    "attr_start": attr.start(),
                    "attr_end": attr.end(),
                    "fn_end": i,
                }
            )
        else:
            return [], "logic_route_unknown"
    return out, None


def island_insertion_point(src: str) -> int:
    """Byte offset after leading `//!` docs, `#![..]` inner attrs, blanks."""
    offset = 0
    for line in src.splitlines(keepends=True):
        stripped = line.strip()
        if not stripped or stripped.startswith("//!") or stripped.startswith("#!["):
            offset += len(line)
            continue
        break
    return offset


PROOF_ASSERT_RE = re.compile(r"\bproof_assert!\s*([({])")

# Pearlite vocabulary that is NOT an executable Rust expression: a ported
# `assert!` must compile and its obligation enters the ordinary verification
# stream (doctrine §2). Quantifiers/implication/old are native CLAUSE
# vocabulary but not expression vocabulary.
PROOF_ASSERT_NONEXEC = re.compile(r"\bforall\b|\bexists\b|==>|\bold\s*\(|\bdead\b")


def port_proof_asserts(src: str) -> tuple[str | None, str | None]:
    """`proof_assert!(P)` → `assert!(P)` for the executable subset (§2:
    stronger than the ghost assertion — it must verify or the strict build
    fails; that direction is sound). Non-executable or pearlite-only
    predicates refuse the file with an attributed reason."""
    out = []
    last = 0
    masked = mask_noncode(src)
    for m in PROOF_ASSERT_RE.finditer(masked):
        open_ch = m.group(1)
        close_ch = ")" if open_ch == "(" else "}"
        depth, i = 1, m.end()
        while i < len(masked) and depth:
            if masked[i] == open_ch:
                depth += 1
            elif masked[i] == close_ch:
                depth -= 1
            i += 1
        if depth:
            return None, "proof_assert_unbalanced"
        predicate = src[m.end() : i - 1].strip()
        bare_pred = masked[m.end() : i - 1]
        for reason, pattern in PREDICATE_REFUSALS.items():
            if pattern.search(bare_pred):
                return None, f"proof_assert_{reason}"
        if PROOF_ASSERT_NONEXEC.search(bare_pred):
            return None, "proof_assert_nonexecutable"
        out.append(src[last : m.start()])
        out.append(f"assert!({predicate})")
        last = i
        # `proof_assert!{..}` is a statement without `;`; `assert!(..)`
        # needs one — keep an existing `;`, add one otherwise.
        if open_ch == "{" and not src[i:].lstrip().startswith(";"):
            out.append(";")
    out.append(src[last:])
    return "".join(out), None


SNAPSHOT_BIND_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(snapshot|ghost)!\s*([({])"
)


def port_fn_entry_snapshots(src: str) -> tuple[str | None, str | None]:
    """Doctrine §4, the ruled mechanical sub-case: a snapshot taken at fn
    entry maps to the native old()-anchored vocabulary. `let s = snapshot!(E);`
    as the FIRST statement of a fn body is deleted, and every later use of
    `s` — which must occur ONLY inside contract attributes, as `*s` or bare
    `s` — rewrites to `old(E)`. Everything else refuses attributed: a bare
    (non-binding) snapshot!, a mid-body snapshot (two-state territory), an
    expression outside the predicate gates, or a binding that escapes into
    executable code."""
    masked = mask_noncode(src)
    out = src
    binds = list(SNAPSHOT_BIND_RE.finditer(masked))
    total_macros = len(re.findall(r"\b(?:snapshot|ghost)!", masked))
    if not binds:
        if total_macros:
            return None, "snapshot_not_binding"
        return src, None
    if len(binds) != total_macros:
        return None, "snapshot_not_binding"
    attr_spans = [(a, b) for a, b, _, _ in find_attrs(src)]

    def inside_attr(pos: int) -> bool:
        return any(a <= pos < b for a, b in attr_spans)

    for m in reversed(binds):
        name, open_ch = m.group(1), m.group(3)
        close_ch = ")" if open_ch == "(" else "}"
        depth, i = 1, m.end()
        while i < len(masked) and depth:
            if masked[i] == open_ch:
                depth += 1
            elif masked[i] == close_ch:
                depth -= 1
            i += 1
        if depth:
            return None, "snapshot_unbalanced"
        expr = src[m.end() : i - 1].strip()
        end = i
        tail = src[end:]
        if tail.lstrip().startswith(";"):
            end = end + tail.index(";") + 1
        else:
            return None, "snapshot_not_binding"
        brace = masked.rfind("{", 0, m.start())
        if brace == -1 or masked[brace + 1 : m.start()].strip():
            return None, "snapshot_not_fn_entry"
        for reason, pattern in PREDICATE_REFUSALS.items():
            if pattern.search(mask_noncode(expr)):
                return None, f"snapshot_expr_{reason}"
        replacement = f"old({expr})"
        uses = [
            u
            for u in re.finditer(rf"\*?\b{re.escape(name)}\b", masked)
            if u.start() >= end
        ]
        for u in uses:
            if not inside_attr(u.start()):
                return None, "snapshot_escapes_to_code"
        for u in reversed(uses):
            out = out[: u.start()] + replacement + out[u.end() :]
        line_start = out.rfind("\n", 0, m.start()) + 1
        line_end = end
        if out[line_end : line_end + 1] == "\n":
            line_end += 1
        out = out[:line_start] + out[line_end:]
    return out, None


def port_file(src: str) -> tuple[str | None, str | None]:
    """Return (ported_source, None) or (None, refusal_reason)."""
    if re.search(r"\b(?:snapshot|ghost)!", mask_noncode(src)):
        ported, refusal = port_fn_entry_snapshots(src)
        if ported is None:
            return None, refusal
        src = ported
    if re.search(r"\bSnapshot\b", mask_noncode(src)):
        return None, "snapshot_type"
    if re.search(r"\bGhost(?:Box)?\b|#\[check\(ghost\)\]", mask_noncode(src)):
        return None, "ghost_type"
    if REFUSAL_PATTERNS["proof_assert"].search(mask_noncode(src)):
        ported, refusal = port_proof_asserts(src)
        if ported is None:
            return None, refusal
        src = ported
    bare = mask_noncode(src)
    for reason, pattern in REFUSAL_PATTERNS.items():
        if reason in ("logic_attr", "proof_assert", "pearlite_macro", "snapshot", "ghost"):
            continue  # handled with finer attribution (pearlite: post-scan)
        if pattern.search(bare):
            return None, reason

    logic_fns: list[dict] = []
    if REFUSAL_PATTERNS["logic_attr"].search(bare):
        logic_fns, refusal = extract_logic_fns(src)
        if refusal is not None:
            return None, refusal
    try:
        attrs = find_attrs(src)
    except ValueError as error:
        return None, f"scanner: {error}"
    # Contract attrs inside a to-be-deleted island fn would dangle.
    for start, _, _, _ in attrs:
        for fn in logic_fns:
            if fn["route"] == "island" and fn["attr_start"] < start < fn["fn_end"]:
                return None, "island_fn_contract_v2"
    if not attrs and not logic_fns:
        return src, None  # zero-construct file: byte-identical port.

    for _, _, _, predicate in attrs:
        for reason, pattern in PREDICATE_REFUSALS.items():
            if pattern.search(mask_noncode(predicate)):
                return None, f"predicate: {reason}"

    # R4 §2 clause tier: rewrite pearlite binder spellings to native E3 form
    # (or refuse attributed). Applied to the predicate text the clause
    # assembly below consumes, positionally by attr span.
    rewritten_attrs = []
    for start, end, kind, predicate in attrs:
        if "forall<" in predicate.replace(" ", "") or "exists<" in predicate.replace(" ", ""):
            rewritten, refusal = rewrite_clause_binders(predicate)
            if rewritten is None:
                return None, refusal
            predicate = rewritten
        rewritten_attrs.append((start, end, kind, predicate))
    attrs = rewritten_attrs

    # Group attributes by the code construct that follows them.
    edits: list[tuple[int, int, str]] = []  # (start, end, replacement)
    i = 0
    while i < len(attrs):
        group = [attrs[i]]
        while i + 1 < len(attrs) and not src[attrs[i][1] : attrs[i + 1][0]].strip():
            i += 1
            group.append(attrs[i])
        i += 1
        target = next_code_token_line(src, group[-1][1])
        kinds = {kind for _, _, kind, _ in group}
        fn_like = bool(re.match(r"(pub(\s*\([^)]*\))?\s+)?(const\s+)?(unsafe\s+)?fn\b", target))
        loop_like = bool(re.match(r"('\w+\s*:\s*)?(while\b|loop\b)", target))
        if fn_like and kinds <= {"requires", "ensures"}:
            clause = " ".join(
                f"{kind} {pred}"
                for _, _, kind, pred in sorted(group, key=lambda a: a[2] == "ensures")
            )
            edits.append((group[0][0], group[-1][1], ""))
            edits.append(("FN_CLAUSE", target, clause))  # type: ignore[arg-type]
        elif loop_like and kinds <= {"invariant", "variant"}:
            clause = " ".join(
                f"{'decreases' if kind == 'variant' else 'invariant'} {pred}"
                for _, _, kind, pred in group
            )
            edits.append((group[0][0], group[-1][1], ""))
            edits.append(("LOOP_CLAUSE", target, clause))  # type: ignore[arg-type]
        elif re.match(r"for\b", target):
            return None, "for_loop_invariant"
        else:
            return None, f"unplaceable: {sorted(kinds)} before {target[:40]!r}"

    # Logic-fn edits join the same back-to-front span pass: Route A drops
    # just the attribute (the fn stays Rust; the E6 lane admits its MIR
    # body); Route B deletes the whole fn — its island def is prepended
    # below, and any surviving reference to the name refuses the file.
    for fn in logic_fns:
        if fn["route"] == "island":
            edits.append((fn["attr_start"], fn["fn_end"], ""))
        else:
            edits.append((fn["attr_start"], fn["attr_end"], ""))

    # Apply deletions (real spans) back-to-front, remembering clause inserts.
    fn_clauses: list[tuple[str, str]] = []
    loop_clauses: list[tuple[str, str]] = []
    for edit in edits:
        if edit[0] == "FN_CLAUSE":
            fn_clauses.append((edit[1], edit[2]))
        elif edit[0] == "LOOP_CLAUSE":
            loop_clauses.append((edit[1], edit[2]))
    ported = src
    for start, end, replacement in sorted(
        (e for e in edits if isinstance(e[0], int)), reverse=True
    ):
        # Swallow the trailing newline of the removed attribute block.
        while end < len(ported) and ported[end] in " \t":
            end += 1
        if end < len(ported) and ported[end] == "\n":
            end += 1
        ported = ported[:start] + replacement + ported[end:]

    def reinsert(text: str, target: str, clause: str) -> tuple[str | None, str | None]:
        # Insert after the matched head. FAIL CLOSED on ambiguity: the target
        # must match exactly once, outside comments and literals (a commented
        # or quoted twin could otherwise absorb the clause and corrupt a file).
        # A bodyless trait-method DECLARATION ends in `;` — the clause belongs
        # BEFORE the semicolon (`fn f(..) -> T ensures Q;`), so strip it from
        # the matched head and re-emit it after the clause.
        head = target.split("{")[0].rstrip()
        # The first `{` must open the loop/fn BODY. When the head ends in a
        # binding/connective token (`while let pat = { .. } {}` —
        # block-expression scrutinee; `while a &&` — multiline condition),
        # that `{` is mid-expression and inserting a clause there would
        # corrupt the file. Refuse, attributed. (A generic return type
        # legitimately ends in `>`, so comparison-shaped suffixes stay
        # allowed; the parse-validation stage backstops anything subtler.)
        if head.endswith(("=", "|", "&")):
            return None, "clause_target_brace_in_expression"
        trailing_semi = head.endswith(";")
        if trailing_semi:
            head = head[:-1].rstrip()
        bare = mask_noncode(text)
        if bare.count(head) != 1 or text.count(head) != 1:
            return None, f"reinsert: ambiguous or commented target {head[:40]!r}"
        at = text.index(head) + len(head)
        suffix = text[at:]
        if trailing_semi and suffix.lstrip().startswith(";"):
            semi_at = at + suffix.index(";")
            return text[:at] + " " + clause + text[semi_at:], None
        return text[:at] + " " + clause + suffix, None

    for target, clause in fn_clauses + loop_clauses:
        result, failure = reinsert(ported, target, clause)
        if result is None:
            return None, failure
        ported = result

    # Ported files leave the legacy macro surface behind.
    ported = re.sub(r"^\s*use\s+creusot_contracts\b[^;]*;\s*$", "", ported, flags=re.M)
    ported = re.sub(r"^\s*extern\s+crate\s+creusot_contracts\s*;\s*$", "", ported, flags=re.M)

    # Island synthesis for Route-B fns. FAIL-CLOSED: a surviving reference
    # to a deleted fn's name (a clause calling it, code using it) refuses —
    # the `by`-citation wiring is a later increment; and a def referencing a
    # LATER def would be rejected by the kernel's strict declaration order,
    # so it refuses here with attribution instead.
    island_defs = [fn["island_def"] for fn in logic_fns if fn["route"] == "island"]
    if island_defs:
        names = [fn["name"] for fn in logic_fns if fn["route"] == "island"]
        remaining = mask_noncode(ported)
        for name in names:
            if re.search(rf"\b{re.escape(name)}\b", remaining):
                return None, "island_name_cited_v2"
        for idx, rendered in enumerate(island_defs):
            for later in names[idx + 1 :]:
                if re.search(rf"\b{re.escape(later)}\b", rendered):
                    return None, "island_forward_ref_v2"
        at = island_insertion_point(ported)
        block = "clean {\n" + "\n\n".join("    " + d for d in island_defs) + "\n}\n\n"
        ported = ported[:at] + block + ported[at:]

    # A pearlite! that survived porting (a Route-A body wrapper, a ghost
    # context, a stray expression) has no macro to expand against — the
    # legacy crate is gone from ported files. Refuse, attributed.
    if REFUSAL_PATTERNS["pearlite_macro"].search(mask_noncode(ported)):
        return None, "pearlite_macro_residual"
    return ported.lstrip("\n"), None


def parse_validate(trustc: str, path: str) -> str | None:
    """Parse the ported file with the real compiler; None = OK, else stderr tail."""
    # `-Zparse-only` was removed upstream; `-Zunpretty=normal` parses the file
    # and exits non-zero on any syntax error, resolving nothing.
    result = subprocess.run(
        [trustc, "-Zunpretty=normal", "--edition=2021", path],
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )
    if result.returncode == 0:
        return None
    return (result.stderr or "parse failed").strip()[-400:]


FN_HEAD_RE = re.compile(
    r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*(<[^>]*>)?\s*\(", re.S
)


UNTYPED_QUANT_RE = re.compile(
    r"^(forall|exists)\s*<\s*([A-Za-z_][A-Za-z0-9_]*)\s*>\s*(.+)$", re.S
)


def probe_untyped_binder(binder_probe: str, src: str, brace: int, end: int, head) -> str:
    """Shell one untyped-binder body to the §2 binder_probe CLI and classify:
    unique | ambiguous | none | unparsed | error. Fail-soft: every failure
    mode is its own verdict string, never an exception — the census refusal
    stands regardless."""
    # Logic bodies normally spell the expression as `pearlite! { ... }`.
    # The census translates the unwrapped expression, so the probe must judge
    # that same expression rather than silently classifying the wrapper as an
    # unparsed binder. Keep the unwrap here as the authority boundary so every
    # caller gets the same behavior.
    body = unwrap_pearlite(src[brace + 1 : end - 1].strip())
    m = UNTYPED_QUANT_RE.match(body)
    if not m:
        return "unparsed"
    quantifier, binder, rest = m.group(1), m.group(2), m.group(3).strip()
    sig = src[head.end() : brace]
    close = sig.find(")")
    pairs = [
        f"{name}:{ty}"
        for name, ty in re.findall(
            r"([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([A-Za-z_][A-Za-z0-9_]*)", sig[:close]
        )
    ]
    try:
        result = subprocess.run(
            [binder_probe, quantifier, binder, rest, *pairs],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return "error"
    if result.returncode != 0:
        return "error"
    try:
        report = json.loads(result.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        return "error"
    if report.get("unique"):
        return "unique"
    hits = sum(1 for ok in report.get("outcomes", {}).values() if ok)
    return "ambiguous" if hits > 1 else "none"


def census_logic(corpus: str, binder_probe: str | None = None) -> dict:
    """Attribute every `#[logic]` fn body to the pearlite→Clean v1 fragment.

    Measurement only — no files are written. For each logic fn the body is
    admitted to `translate_expr` only when it is a SINGLE expression (no `;`,
    no nested block) on a non-generic fn; everything else refuses with an
    attributed reason. The report drives the generator's widening order the
    same way the E6 battery census drives the admission lane's.
    """
    from pearlite_to_clean import INT_SUFFIX_RE, Refused, translate_expr

    total = 0
    translated: list[dict[str, str]] = []
    refused: dict[str, int] = {}

    def refuse(reason: str) -> None:
        refused[reason] = refused.get(reason, 0) + 1

    for sub in ("tests/should_succeed", "tests/should_fail", "examples"):
        base = os.path.join(corpus, sub)
        for dirpath, _, names in os.walk(base):
            for name in sorted(names):
                if not name.endswith(".rs"):
                    continue
                path = os.path.join(dirpath, name)
                rel = os.path.relpath(path, corpus)
                # Census discovery has the same lexical authority boundary as
                # emission: syntax-looking text in literals is never a logic
                # declaration or a body delimiter.
                src = mask_noncode(open(path, encoding="utf-8").read())
                for attr in re.finditer(r"#\[logic\b(?:\(([^]]*)\))?\]", src):
                    total += 1
                    arg_text = attr.group(1) or ""
                    # `open`/`open(..)`/`inline`/`opaque` are visibility and
                    # unfolding hints — translation-neutral for the body.
                    # `prophetic` (prophecy operators) and `law` (auto-applied
                    # lemma role) carry semantics the v1 fragment does not
                    # reproduce; they refuse with their own reasons.
                    args = [a.strip() for a in re.split(r",(?![^(]*\))", arg_text) if a.strip()]
                    semantic = [
                        a
                        for a in args
                        if not (
                            a == "open"
                            or a.startswith("open(")
                            or a in ("inline", "opaque", "sealed")
                        )
                    ]
                    if semantic:
                        refuse("logic_attr_" + "_".join(sorted(set(semantic)))[:40])
                        continue
                    head = FN_HEAD_RE.search(src, attr.end())
                    if head is None:
                        refuse("no_fn_after_attr")
                        continue
                    if head.group(2):
                        refuse("generic_fn")
                        continue
                    brace = src.find("{", head.end())
                    semi = src.find(";", head.end())
                    if brace == -1 or (semi != -1 and semi < brace):
                        refuse("bodyless_decl")
                        continue
                    depth, i = 1, brace + 1
                    while i < len(src) and depth:
                        if src[i] == "{":
                            depth += 1
                        elif src[i] == "}":
                            depth -= 1
                        i += 1
                    if depth:
                        refuse("unbalanced_body")
                        continue
                    body = unwrap_pearlite(src[brace + 1 : i - 1].strip())
                    if not body:
                        refuse("empty_body")
                        continue
                    try:
                        clean = translate_expr(body)
                    except Refused as refusal:
                        reason = str(refusal)
                        # R4 §2: an untyped binder gets its evidence-carrying
                        # probe — the SAME elaborator that discharges ported
                        # clauses judges every E3 typing (binder_probe CLI).
                        # Measurement only: the refusal stands regardless; the
                        # probe verdict (unique/ambiguous/none) is recorded to
                        # size the future bounded-domain auto-fix.
                        if reason == "binder_untyped_v1_3" and binder_probe:
                            verdict = probe_untyped_binder(
                                binder_probe, src, brace, i, head
                            )
                            reason = f"binder_untyped_v1_3_probe_{verdict}"
                        refuse(reason)
                        continue
                    # A body that mentions its own fn is self-recursive; the
                    # island kernel REJECTS self-reference structurally (the
                    # def's name is not in scope during its own elaboration —
                    # soundness-probed 2026-07-22), so it cannot emit until a
                    # principled termination encoding exists.
                    if re.search(rf"\b{re.escape(head.group(1))}\b", body):
                        refuse("self_recursion_v1_2")
                        continue
                    # Route classification (2026-07-22 emitter design):
                    #   island — any pearlite `Int` in the signature: the fn
                    #     cannot compile as Rust; it becomes an island def and
                    #     clauses cite island theorems via `by`.
                    #   e6_admission — all-machine signature: the fn stays a
                    #     plain Rust fn, clauses call it, and the E6 lane
                    #     admits its MIR body as trust_import_<mangled>.
                    sig = src[head.end() : brace]
                    close = sig.find(")")
                    param_types = re.findall(r":\s*([A-Za-z_][A-Za-z0-9_]*)", sig[:close])
                    ret = re.search(r"->\s*([A-Za-z_][A-Za-z0-9_]*)", sig[close:])
                    types = param_types + ([ret.group(1)] if ret else [])
                    if any(t == "Int" for t in types):
                        route = "island"
                    elif all(
                        t == "bool" or INT_SUFFIX_RE.fullmatch(t) for t in types
                    ):
                        route = "e6_admission"
                    else:
                        route = "unknown_types_" + "_".join(sorted(set(types)))[:40]
                    translated.append(
                        {"file": rel, "fn": head.group(1), "route": route, "clean": clean}
                    )

    routes: dict[str, int] = {}
    for entry in translated:
        routes[entry["route"]] = routes.get(entry["route"], 0) + 1
    return {
        "schema": "trust-wp.pearlite-to-clean-census/v2",
        "logic_fns": total,
        "translated": len(translated),
        "routes": dict(sorted(routes.items(), key=lambda kv: -kv[1])),
        "refused_by_reason": dict(sorted(refused.items(), key=lambda kv: -kv[1])),
        "translations": translated,
    }


EMITTER_FIXTURES: list[tuple[str, str, str | None, str | None]] = [
    (
        "island_route",
        """use creusot_contracts::*;

#[logic]
fn sqr(x: Int) -> Int {
    x * x
}

#[requires(n < 100u64)]
#[ensures(result >= n)]
fn step(n: u64) -> u64 {
    n + 1
}
""",
        """clean {
    def sqr (x : Int) : Int := (x * x)
}

fn step(n: u64) -> u64 requires n < 100u64 ensures result >= n {
    n + 1
}
""",
        None,
    ),
    (
        "e6_route_cited",
        """use creusot_contracts::*;

#[logic]
fn is_small(x: u64) -> bool {
    x < 10u64
}

#[ensures(is_small(result))]
fn zero() -> u64 {
    0
}
""",
        """fn is_small(x: u64) -> bool {
    x < 10u64
}

fn zero() -> u64 ensures is_small(result) {
    0
}
""",
        None,
    ),
    (
        "two_island_defs_dependency_order",
        """#[logic]
fn dbl(x: Int) -> Int {
    x + x
}

#[logic]
fn quad(x: Int) -> Int {
    dbl(dbl(x))
}

fn main() {}
""",
        """clean {
    def dbl (x : Int) : Int := (x + x)

    def quad (x : Int) : Int := (dbl (dbl x))
}

fn main() {}
""",
        None,
    ),
    (
        "island_name_cited_refuses",
        """#[logic]
fn sqr(x: Int) -> Int {
    x * x
}

#[ensures(result == sqr(4i64))]
fn sixteen() -> i64 {
    16
}
""",
        None,
        "island_name_cited_v2",
    ),
    (
        "island_forward_ref_refuses",
        """#[logic]
fn quad(x: Int) -> Int {
    dbl(dbl(x))
}

#[logic]
fn dbl(x: Int) -> Int {
    x + x
}

fn main() {}
""",
        None,
        "island_forward_ref_v2",
    ),
    (
        "island_mixed_sig_refuses",
        """#[logic]
fn relax(x: u64) -> Int {
    x + 1
}

fn main() {}
""",
        None,
        "island_mixed_sig_v2",
    ),
    (
        "proof_assert_executable",
        """#[requires(x > 0u64)]
fn f(x: u64) -> u64 {
    proof_assert!(x > 0u64);
    proof_assert! { x + 1u64 > x }
    x
}
""",
        """fn f(x: u64) -> u64 requires x > 0u64 {
    assert!(x > 0u64);
    assert!(x + 1u64 > x);
    x
}
""",
        None,
    ),
    (
        "proof_assert_model_refuses",
        """fn f(s: Vec<u64>) {
    proof_assert!(s@ == s@);
}
""",
        None,
        "proof_assert_model_deref_at",
    ),
    (
        "proof_assert_quantifier_refuses",
        """fn f(x: u64) {
    proof_assert!(forall<i: u64> i >= 0u64);
}
""",
        None,
        "proof_assert_nonexecutable",
    ),
    (
        "pearlite_wrapped_island_body_unwraps",
        """#[logic]
fn tri(n: Int) -> Int {
    pearlite! { n * (n + 1) / 2 }
}

fn main() {}
""",
        """clean {
    def tri (n : Int) : Int := ((n * (n + 1)) / 2)
}

fn main() {}
""",
        None,
    ),
    (
        "while_let_block_scrutinee_refuses",
        """fn f(mut x: Vec<u32>) {
    #[invariant(x == x)]
    while let Some(_) = { (&mut x).pop() } {}
}
""",
        None,
        "clause_target_brace_in_expression",
    ),
    (
        "clause_binder_u64_rewrites",
        """#[ensures(forall<i: u64> i <= result ==> i <= x)]
fn f(x: u64) -> u64 {
    x
}
""",
        """fn f(x: u64) -> u64 ensures forall i: u64, i <= result ==> i <= x {
    x
}
""",
        None,
    ),
    (
        "clause_binder_int_refuses",
        """#[ensures(forall<i: Int> i == i)]
fn f(x: u64) -> u64 {
    x
}
""",
        None,
        # The Int binder falls to the EARLIER spec-types predicate gate; the
        # clause_binder_int arm in rewrite_clause_binders is defense-in-depth
        # should that gate ever narrow.
        "predicate: spec_types",
    ),
    (
        "clause_binder_untyped_refuses",
        """#[ensures(forall<i> i == i)]
fn f(x: u64) -> u64 {
    x
}
""",
        None,
        "clause_binder_untyped",
    ),
    (
        "clause_binder_usize_refuses",
        """#[ensures(forall<i: usize> i == i)]
fn f(x: u64) -> u64 {
    x
}
""",
        None,
        "clause_binder_type_unsupported_usize",
    ),
    (
        "clause_binder_non_head_refuses",
        """#[ensures(x <= result && forall<i: u64> i == i)]
fn f(x: u64) -> u64 {
    x
}
""",
        None,
        "clause_binder_not_head",
    ),
    (
        "snapshot_fn_entry_ports_to_old",
        """fn count_down(mut x: u64) -> u64 {
    let snap = snapshot!(x);
    #[invariant(x <= *snap)]
    #[variant(x)]
    while x > 0u64 {
        x -= 1;
    }
    x
}
""",
        """fn count_down(mut x: u64) -> u64 {
        while x > 0u64 invariant x <= old(x) decreases x {
        x -= 1;
    }
    x
}
""",
        None,
    ),
    (
        "snapshot_mid_body_refuses",
        """fn f(x: u64) -> u64 {
    let y = x + 1;
    let snap = snapshot!(y);
    #[invariant(y <= *snap)]
    while y > 0u64 {}
    y
}
""",
        None,
        "snapshot_not_fn_entry",
    ),
    (
        "snapshot_escape_refuses",
        """fn f(x: u64) -> u64 {
    let snap = snapshot!(x);
    let y = *snap;
    y
}
""",
        None,
        "snapshot_escapes_to_code",
    ),
    (
        "snapshot_model_expr_refuses",
        """fn f(v: Vec<u64>) {
    let snap = snapshot!(v@);
    #[invariant(*snap == *snap)]
    while true {}
}
""",
        None,
        "snapshot_expr_model_deref_at",
    ),
    (
        "ghost_fn_entry_ports_to_old",
        """fn tally(mut x: u64) -> u64 {
    let bound = ghost!(x + 1u64);
    #[invariant(x < *bound)]
    #[variant(x)]
    while x > 0u64 {
        x -= 1;
    }
    x
}
""",
        """fn tally(mut x: u64) -> u64 {
        while x > 0u64 invariant x < old(x + 1u64) decreases x {
        x -= 1;
    }
    x
}
""",
        None,
    ),
    (
        "ghost_imperative_refuses",
        """fn f(x: u64) -> u64 {
    ghost! { let mut acc = 0; acc += x; };
    x
}
""",
        None,
        "snapshot_not_binding",
    ),
    (
        "pearlite_residual_refuses",
        """#[logic]
fn small(x: u64) -> bool {
    pearlite! { x < 10u64 }
}

fn main() {}
""",
        None,
        "pearlite_macro_residual",
    ),
    (
        "syntax_looking_literals_and_nested_comments_are_inert",
        '''fn literals() {
    let a = "proof_assert!(false) #[logic] pearlite! { bad } // not a comment";
    let b = r###"/* #[requires(false)] */ proof_assert!{false}"###;
    let c = b"ghost!{bad} proof_assert!(false)";
    let d = 'x';
}
/* outer comment
   /* #[logic] fn fake() { proof_assert!(false); } */
   pearlite! { also_fake }
*/
''',
        '''fn literals() {
    let a = "proof_assert!(false) #[logic] pearlite! { bad } // not a comment";
    let b = r###"/* #[requires(false)] */ proof_assert!{false}"###;
    let c = b"ghost!{bad} proof_assert!(false)";
    let d = 'x';
}
/* outer comment
   /* #[logic] fn fake() { proof_assert!(false); } */
   pearlite! { also_fake }
*/
''',
        None,
    ),
    (
        "proof_assert_literals_do_not_close_or_trigger_refusals",
        '''fn f<'a>(s: &'a str) {
    proof_assert!(s == r#"forall old(@) ) } proof_assert!(false)"#);
}
''',
        '''fn f<'a>(s: &'a str) {
    assert!(s == r#"forall old(@) ) } proof_assert!(false)"#);
}
''',
        None,
    ),
]


def self_test_emitter() -> int:
    failures = 0
    for label, source, expected, expected_refusal in EMITTER_FIXTURES:
        ported, reason = port_file(source)
        if expected_refusal is not None:
            if ported is not None or (reason or "") != expected_refusal:
                print(f"FAIL {label}: expected refusal {expected_refusal}, "
                      f"got ported={ported is not None} reason={reason}")
                failures += 1
            continue
        if ported is None:
            print(f"FAIL {label}: refused {reason}")
            failures += 1
        elif ported != expected:
            print(f"FAIL {label}: mismatch\n--- got ---\n{ported}\n--- want ---\n{expected}")
            failures += 1
    # Exercise the real census-to-probe shape: Creusot normally wraps logic
    # bodies in pearlite!, while binder_probe accepts the inner expression.
    # A regression here previously made every normal untyped binder look
    # `unparsed` without ever invoking the elaborator.
    source = """#[logic]
fn bounded(x: u64) -> bool {
    pearlite! { forall<i> i <= x }
}
"""
    masked = mask_noncode(source)
    head = FN_HEAD_RE.search(masked)
    assert head is not None
    brace = masked.find("{", head.end())
    end = masked.rfind("}") + 1
    expected_argv = ["binder-probe", "forall", "i", "i <= x", "x:u64"]
    completed = subprocess.CompletedProcess(
        expected_argv,
        0,
        stdout='{"unique":"u64","outcomes":{"u64":true}}\n',
        stderr="",
    )
    with mock.patch.object(subprocess, "run", return_value=completed) as run:
        verdict = probe_untyped_binder("binder-probe", masked, brace, end, head)
    if verdict != "unique" or run.call_count != 1 or run.call_args.args[0] != expected_argv:
        print(
            "FAIL binder_probe_pearlite_unwrap: "
            f"verdict={verdict} calls={run.call_count} "
            f"argv={run.call_args.args[0] if run.call_count else None}"
        )
        failures += 1

    total = len(EMITTER_FIXTURES) + 1
    print(f"emitter self-test: {total - failures}/{total} passed")
    return 1 if failures else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", default=None)
    parser.add_argument("--out", default=None)
    parser.add_argument("--trustc", default=None)
    parser.add_argument("--report", default=None)
    parser.add_argument(
        "--census-logic",
        action="store_true",
        help="measure #[logic] bodies against the pearlite→Clean v1 fragment "
        "(no files written)",
    )
    parser.add_argument(
        "--self-test-emitter",
        action="store_true",
        help="run the golden emitter fixtures (no corpus needed)",
    )
    parser.add_argument(
        "--binder-probe",
        default=None,
        help="path to the trust-spec-elab binder_probe example binary; when "
        "set, --census-logic classifies each untyped binder "
        "(unique/ambiguous/none) via the real elaborator",
    )
    args = parser.parse_args()

    if args.self_test_emitter:
        return self_test_emitter()
    if not args.corpus:
        parser.error("--corpus is required unless --self-test-emitter")

    if args.census_logic:
        report = census_logic(args.corpus, binder_probe=args.binder_probe)
        text = json.dumps(report, indent=2)
        if args.report:
            with open(args.report, "w", encoding="utf-8") as handle:
                handle.write(text)
        print(
            f"logic_fns={report['logic_fns']} translated={report['translated']} "
            f"refused={sum(report['refused_by_reason'].values())}"
        )
        return 0
    if not args.out:
        parser.error("--out is required unless --census-logic")

    ported_count = 0
    refused: dict[str, int] = {}
    parse_failures: list[str] = []
    entries: list[dict[str, str]] = []

    for sub in ("tests/should_succeed", "tests/should_fail", "examples"):
        base = os.path.join(args.corpus, sub)
        for dirpath, _, names in os.walk(base):
            for name in sorted(names):
                if not name.endswith(".rs"):
                    continue
                path = os.path.join(dirpath, name)
                rel = os.path.relpath(path, args.corpus)
                src = open(path, encoding="utf-8").read()
                ported, reason = port_file(src)
                if ported is None:
                    refused[reason or "unknown"] = refused.get(reason or "unknown", 0) + 1
                    entries.append({"file": rel, "status": "refused", "reason": reason or ""})
                    continue
                out_path = os.path.join(args.out, rel)
                os.makedirs(os.path.dirname(out_path), exist_ok=True)
                with open(out_path, "w", encoding="utf-8") as handle:
                    handle.write(ported)
                status = "ported"
                if args.trustc:
                    failure = parse_validate(args.trustc, out_path)
                    if failure is not None:
                        status = "parse-failed"
                        parse_failures.append(rel)
                entries.append({"file": rel, "status": status})
                if status == "ported":
                    ported_count += 1

    report = {
        "schema": "trust-wp.creusot-native-port-dry-run/v1",
        "ported": ported_count,
        "parse_failed": len(parse_failures),
        "refused_by_reason": dict(sorted(refused.items(), key=lambda kv: -kv[1])),
        "parse_failures": parse_failures[:50],
        "entries": entries,
    }
    text = json.dumps(report, indent=2)
    if args.report:
        with open(args.report, "w", encoding="utf-8") as handle:
            handle.write(text)
    print(
        f"ported={ported_count} parse_failed={len(parse_failures)} "
        f"refused={sum(refused.values())}"
    )
    for reason, count in sorted(refused.items(), key=lambda kv: -kv[1])[:10]:
        print(f"  refused {reason}: {count}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
