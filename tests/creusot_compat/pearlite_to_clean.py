#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Pearlite -> Clean body translator, v1.1 (R4 §1-executor, ratified
doctrine 2026-07-22).

Scope (the census's quantifier-free, non-recursive Int-relaxed fragment):
arithmetic (+ - * / %, unary -), comparisons (== != < <= > >=), boolean
connectives (&& || ! ==>), `let x = e; rest` binding chains, block-bodied
`if c { a } else { b }` (else-if chains included), parentheses, integer
literals (machine-int suffixes stripped under Int-relax), and bare
identifiers (parameters / in-scope logic names). Output is a FULLY
PARENTHESIZED Clean expression — precedence can never reshape the tree the
parser built. `let` renders as the island's semicolon spelling
`(let x := e; rest)`; `if` renders `(if c then a else b)` — both spellings
and the Decidable instances for Int comparisons (conjunctive and nested
conditions included) are kernel-verified in the island environment
(trust-certify tests/generator_dialect_pin.rs).

FAIL-CLOSED by construction: any token or construct outside the fragment
raises Refused with an attributed reason — model/prophecy syntax (@ ^),
method/field access (any `.`), indexing, quantifiers, `match`, `let mut`,
pattern/type-ascribed lets, `if` without `else`, string/char literals,
casts, chained comparisons, pearlite's `dead` term, `self` receivers. The
caller ports a logic fn only when its WHOLE body translates; a partial
translation is never emitted.

Usage: `python3 pearlite_to_clean.py --self-test`, or import
`translate_expr(text) -> str` (raises `Refused`).
"""

from __future__ import annotations

import re
import sys


class Refused(Exception):
    """A construct outside the v1 fragment, with an attributed reason."""


# A machine-int suffix on a literal is stripped: under the ratified Int-relax
# doctrine the logic body is read over Int, where `10u32` denotes 10. A SPACED
# `10 u32` is NOT a suffix and still refuses as trailing tokens.
TOKEN_RE = re.compile(
    r"\s*(?:(?P<num>\d[\d_]*(?:[ui](?:8|16|32|64|128|size))?)"
    r"|(?P<ident>[A-Za-z_][A-Za-z0-9_]*)"
    r"|(?P<op>==>|==|!=|<=|>=|&&|\|\||[+\-*/%<>!(){};=,:.@]))"
)

INT_SUFFIX_RE = re.compile(r"[ui](?:8|16|32|64|128|size)$")

# §2 bounded-domain encoding: unsigned fixed-width binder domains as exact
# Int bounds (u<w> values inject into Int as [0, 2^w)).
MACHINE_BINDER_BOUNDS = {
    "u8": 256,
    "u16": 65536,
    "u32": 4294967296,
    "u64": 18446744073709551616,
}

REFUSED_CHARS = {
    "^": "prophecy_final",
    "[": "indexing",
    "]": "indexing",
    '"': "string_literal",
    "'": "char_literal",
    "?": "try_operator",
    "&": "reference_or_bitand",  # lone & (&& is tokenized first)
    "|": "closure_or_bitor",  # lone |
}

REFUSED_KEYWORDS = {
    "match": "match_v1_2",
    "as": "cast",
    # Pearlite's absurd/unreachable term — NOT an ordinary identifier; a bare
    # rendering would be an unbound island name at best and a semantic lie at
    # worst. Refused until the fragment has a principled encoding.
    "dead": "pearlite_dead_term",
    # Logic methods take a receiver; island defs are free functions. The
    # caller must lambda-lift `self` to a named parameter first (v1.1).
    "self": "self_receiver_v1_1",
    "Self": "self_receiver_v1_1",
    "true": None,  # allowed
    "false": None,  # allowed
}


def tokenize(text: str) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    i = 0
    while i < len(text):
        if text[i].isspace():
            i += 1
            continue
        m = TOKEN_RE.match(text[i:])
        if not m or not m.group(0).strip():
            ch = text[i]
            raise Refused(REFUSED_CHARS.get(ch, f"unrecognized_char_{ch!r}"))
        tok = m.group(0).strip()
        if m.group("num"):
            out.append(("num", INT_SUFFIX_RE.sub("", tok).replace("_", "")))
        elif m.group("ident"):
            if tok in REFUSED_KEYWORDS and REFUSED_KEYWORDS[tok] is not None:
                raise Refused(REFUSED_KEYWORDS[tok])
            out.append(("ident", tok))
        else:
            out.append(("op", tok))
        i += m.end()
    return out


# Precedence (binding power), loosest to tightest. `==>` is right-associative;
# comparisons are NON-associative (a < b < c refuses).
IMPLIES, OR, AND, NOT, CMP, ADD, MUL, UNARY = 10, 20, 30, 40, 50, 60, 70, 80

CMP_OPS = {"==": "=", "!=": "≠", "<": "<", "<=": "≤", ">": ">", ">=": "≥"}
ADD_OPS = {"+": "+", "-": "-"}
MUL_OPS = {"*": "*", "/": "/", "%": "%"}


class Parser:
    def __init__(self, tokens: list[tuple[str, str]]):
        self.toks = tokens
        self.pos = 0

    def peek(self) -> tuple[str, str] | None:
        return self.toks[self.pos] if self.pos < len(self.toks) else None

    def next(self) -> tuple[str, str]:
        tok = self.peek()
        if tok is None:
            raise Refused("unexpected_end")
        self.pos += 1
        return tok

    def parse(self) -> str:
        rendered = self.body()
        if self.peek() is not None:
            raise Refused(f"trailing_tokens_{self.peek()[1]!r}")
        return rendered

    def body(self) -> str:
        """`let`-binding chain followed by one final expression, rendered
        right-nested in the island's semicolon spelling."""
        nxt = self.peek()
        if nxt is not None and nxt == ("ident", "let"):
            self.next()
            kind, name = self.next()
            if name == "mut":
                raise Refused("let_mut")
            if kind != "ident":
                raise Refused("let_pattern")
            if self.peek() is None or self.peek() != ("op", "="):
                raise Refused("let_pattern_or_ascription")
            self.next()
            value = self.expr(0)
            if self.peek() is None or self.peek() != ("op", ";"):
                raise Refused("let_missing_semicolon")
            self.next()
            rest = self.body()
            return f"(let {name} := {value}; {rest})"
        return self.expr(0)

    def if_expr(self) -> str:
        """`if c { a } else { b }` (the `if` token already consumed), with
        else-if chains. Arms are bodies (let-chains allowed). Renders the
        island's `(if c then a else b)`; a missing `else` refuses — the
        fragment has no unit type to make a one-armed `if` meaningful."""
        cond = self.expr(0)
        if self.peek() != ("op", "{"):
            raise Refused("if_missing_then_block")
        self.next()
        then_arm = self.body()
        if self.peek() != ("op", "}"):
            raise Refused(f"if_unclosed_then_{(self.peek() or ('', 'EOF'))[1]!r}")
        self.next()
        if self.peek() != ("ident", "else"):
            raise Refused("if_missing_else")
        self.next()
        if self.peek() == ("ident", "if"):
            self.next()
            else_arm = self.if_expr()
        elif self.peek() == ("op", "{"):
            self.next()
            else_arm = self.body()
            if self.peek() != ("op", "}"):
                raise Refused(f"if_unclosed_else_{(self.peek() or ('', 'EOF'))[1]!r}")
            self.next()
        else:
            raise Refused("if_missing_else_block")
        return f"(if {cond} then {then_arm} else {else_arm})"

    def call(self, callee: str) -> str:
        """`f(a, b)` (the `(` still unconsumed) → curried island application
        `(f a b)`; zero-arg `f()` renders bare `f` — the island def it must
        resolve against is nullary. Trailing commas are accepted (Rust
        idiom); anything else out of place refuses. Within-island calls are
        the compositional tier: the emitter orders callee defs before
        callers in ONE island, so no `trust_import_*` citation is involved."""
        self.next()
        args: list[str] = []
        while self.peek() != ("op", ")"):
            args.append(self.expr(0))
            if self.peek() == ("op", ","):
                self.next()
            elif self.peek() != ("op", ")"):
                raise Refused(
                    f"call_malformed_{(self.peek() or ('', 'EOF'))[1]!r}"
                )
        self.next()
        if not args:
            return callee
        return "(" + callee + " " + " ".join(args) + ")"

    def quantifier(self, keyword: str, min_bp: int) -> str:
        """Pearlite `forall<i: Int, ..> body` / `exists<..> body` → the
        island's `(forall i : Int, body)` / `(∃ i : Int, body)`.

        EXACT-DEFINITION discipline: only explicit `Int` binders translate.
        A machine-typed binder (`forall<i: u32>`) ranges over the type's
        finite domain — relaxing it to unbounded Int would define a DIFFERENT
        predicate, so it refuses until a bounding encoding lands with a
        faithfulness argument. An untyped binder is pearlite-inferred; the
        island would infer independently and could land on a different type —
        refused for the same reason. In operand position the quantifier's
        maximal body is ambiguous, so it must be parenthesized."""
        if min_bp > 0:
            raise Refused("quantifier_needs_parens_in_operand")
        if self.peek() != ("op", "<"):
            raise Refused("quantifier_missing_binder")
        self.next()
        binders: list[tuple[str, int | None]] = []
        while True:
            kind, name = self.next()
            if kind != "ident":
                raise Refused("quantifier_binder_pattern")
            if self.peek() != ("op", ":"):
                raise Refused("binder_untyped_v1_3")
            self.next()
            tkind, tname = self.next()
            if tkind != "ident":
                raise Refused("binder_type_unsupported")
            if tname == "Int":
                binders.append((name, None))
            elif tname in MACHINE_BINDER_BOUNDS:
                # Bounded-domain encoding (§2, ratified design + owner
                # ratification 2026-07-22): pearlite logic bodies read as Int
                # arithmetic, so a machine-typed binder MEANS bounded-Int
                # quantification — the u<w> values inject into Int as exactly
                # [0, 2^w). Rendered below with the ∀/∃ duality.
                binders.append((name, MACHINE_BINDER_BOUNDS[tname]))
            elif tname in ("usize", "isize"):
                # Platform-width: a portable definition cannot fix 2^w.
                raise Refused("machine_binder_platform_width")
            elif INT_SUFFIX_RE.fullmatch(tname):
                # Signed domains need [-2^(w-1), 2^(w-1)) with their own
                # battery; not yet landed.
                raise Refused("machine_binder_signed_v1")
            else:
                raise Refused(f"binder_type_unsupported_{tname!r}")
            nxt = self.next()
            if nxt == ("op", ">"):
                break
            if nxt != ("op", ","):
                raise Refused("quantifier_binder_malformed")
        body = self.expr(0)
        for name, bound in reversed(binders):
            if bound is None:
                spelling = "forall" if keyword == "forall" else "∃"
                body = f"({spelling} {name} : Int, {body})"
            elif keyword == "forall":
                # Bounded-∀ guards by IMPLICATION …
                body = (
                    f"(forall {name} : Int, "
                    f"(((0 ≤ {name}) ∧ ({name} < {bound})) → {body}))"
                )
            else:
                # … while bounded-∃ constrains by CONJUNCTION. Collapsing the
                # duality (∃ with →) would make the witness bound vacuous —
                # the classic bounded-quantifier soundness trap.
                body = (
                    f"(∃ {name} : Int, "
                    f"(((0 ≤ {name}) ∧ ({name} < {bound})) ∧ {body}))"
                )
        return body

    def expr(self, min_bp: int) -> str:
        kind, tok = self.next()
        if kind == "num":
            left = tok
        elif tok in ("forall", "exists"):
            left = self.quantifier(tok, min_bp)
        elif tok == "if":
            left = self.if_expr()
        elif tok in ("else", "let"):
            raise Refused(f"unexpected_token_{tok!r}")
        elif kind == "ident":
            if tok in ("true", "false"):
                left = "True" if tok == "true" else "False"
            elif self.peek() == ("op", "("):
                left = self.call(tok)
            else:
                left = tok
        elif tok == "(":
            left = self.expr(0)
            if self.next()[1] != ")":
                raise Refused("unbalanced_paren")
        elif tok == "!":
            left = f"(¬ {self.expr(NOT)})"
        elif tok == "-":
            left = f"(- {self.expr(UNARY)})"
        else:
            raise Refused(f"unexpected_token_{tok!r}")

        # §3 @-view (the ruling's final named element), EXACT fragment: `v@`
        # on a BARE identifier renders as the identifier itself — the island
        # binder for a viewed parameter IS its sequence model (the emitter
        # ports `Seq<Int>`-modeled params as `(v : List Int)`), so the view
        # application is the identity at the island level. `@` on anything
        # other than a bare identifier keeps the historical model_deref_at
        # refusal — HashMap models, nested views, and machine-element
        # collections (whose bounded-element encoding needs its own battery)
        # all stay attributed.
        if self.peek() == ("op", "@"):
            if kind == "ident" and left == tok:
                self.next()
            else:
                raise Refused("model_deref_at")

        # §3 vocabulary (Seq→List mapping, owner-ratified 2026-07-23), entry 1:
        # `.len()` renders the island's `(Int.ofNat (xs.length))` — the exact
        # spelling the generator dialect pin kernel-checks (seq_len_pin). Any
        # other method or field access keeps the historical refusal.
        while self.peek() == ("op", "."):
            self.next()
            kind, method = self.next()
            if kind != "ident" or self.next() != ("op", "("):
                raise Refused("method_or_field_access")
            if method in ("len", "is_empty"):
                if self.next() != ("op", ")"):
                    raise Refused("method_or_field_access")
                if method == "len":
                    left = f"(Int.ofNat ({left}.length))"
                else:
                    # §3 entry 2: definitionally exact — is_empty ⟺ length = 0.
                    left = f"((Int.ofNat ({left}.length)) = 0)"
            elif method == "contains":
                # §3 entry 4: membership is the Prop the kernel already
                # carries — pearlite `xs.contains(x)` IS `List.Mem x xs`
                # (probed: List.Mem registers; Bool-eq spellings do not).
                arg = self.expr(0)
                if self.next() != ("op", ")"):
                    raise Refused("method_or_field_access")
                left = f"(List.Mem {arg} {left})"
            else:
                raise Refused("method_or_field_access")

        while True:
            nxt = self.peek()
            if (
                nxt is None
                or nxt[1] in (")", ";", "{", "}", ",")
                or nxt == ("ident", "else")
            ):
                return left
            op = nxt[1]
            if op == "==>":
                bp, render, right_bp = IMPLIES, "→", IMPLIES  # right-assoc
            elif op == "||":
                bp, render, right_bp = OR, "∨", OR + 1
            elif op == "&&":
                bp, render, right_bp = AND, "∧", AND + 1
            elif op in CMP_OPS:
                bp, render, right_bp = CMP, CMP_OPS[op], CMP + 1
            elif op in ADD_OPS:
                bp, render, right_bp = ADD, ADD_OPS[op], ADD + 1
            elif op in MUL_OPS:
                bp, render, right_bp = MUL, MUL_OPS[op], MUL + 1
            else:
                raise Refused(f"unexpected_operator_{op!r}")
            if bp < min_bp:
                return left
            self.next()
            right = self.expr(right_bp)
            if op in CMP_OPS and self.peek() is not None and self.peek()[1] in CMP_OPS:
                raise Refused("chained_comparison")
            left = f"({left} {render} {right})"


def translate_expr(text: str) -> str:
    """Translate one pearlite body (let-chain + expression) to a fully
    parenthesized Clean expression, or raise [`Refused`] with an attributed
    reason."""
    return Parser(tokenize(text)).parse()


SELF_TESTS_OK = [
    ("x * x", "(x * x)"),
    ("n * (n + 1) / 2", "((n * (n + 1)) / 2)"),
    ("(i + 1) / 2 - 1", "(((i + 1) / 2) - 1)"),
    ("a + b * c", "(a + (b * c))"),
    ("x % 4", "(x % 4)"),
    ("- x + 1", "((- x) + 1)"),
    ("a == b", "(a = b)"),
    ("a != b", "(a ≠ b)"),
    ("0 <= i && i < n", "((0 ≤ i) ∧ (i < n))"),
    ("a && b || c", "((a ∧ b) ∨ c)"),
    ("! done && ok", "((¬ done) ∧ ok)"),
    ("0 <= i ==> a < b ==> c == d", "((0 ≤ i) → ((a < b) → (c = d)))"),
    ("true && ! false", "(True ∧ (¬ False))"),
    ("1_000 + x", "(1000 + x)"),
    ("x < 10u32", "(x < 10)"),
    ("y % 2usize == 0i64", "((y % 2) = 0)"),
    ("let y = x + 1; y * y", "(let y := (x + 1); (y * y))"),
    (
        "let a = 1; let b = a * 2; a + b",
        "(let a := 1; (let b := (a * 2); (a + b)))",
    ),
    ("if x < 0 { - x } else { x }", "(if (x < 0) then (- x) else x)"),
    (
        "if x < 0 { - 1 } else if x == 0 { 0 } else { 1 }",
        "(if (x < 0) then (- 1) else (if (x = 0) then 0 else 1))",
    ),
    ("if c { let y = x; y } else { 0 }", "(if c then (let y := x; y) else 0)"),
    (
        "if 0 <= x && x < n { x } else { 0 }",
        "(if ((0 ≤ x) ∧ (x < n)) then x else 0)",
    ),
    ("xs.len()", "(Int.ofNat (xs.length))"),
    ("xs.len() > 0", "((Int.ofNat (xs.length)) > 0)"),
    ("xs.is_empty()", "((Int.ofNat (xs.length)) = 0)"),
    ("v@", "v"),
    ("s@ == t@", "(s = t)"),
    ("v@.len() > 0", "((Int.ofNat (v.length)) > 0)"),
    ("xs.contains(y)", "(List.Mem y xs)"),
    ("v@.contains(x + 1)", "(List.Mem (x + 1) v)"),
    (
        "! xs.is_empty() ==> xs.len() > 0",
        "((¬ ((Int.ofNat (xs.length)) = 0)) → ((Int.ofNat (xs.length)) > 0))",
    ),
    (
        "let m = if a < b { a } else { b }; m + 1",
        "(let m := (if (a < b) then a else b); (m + 1))",
    ),
    ("sqr(x) + 1", "((sqr x) + 1)"),
    ("min_log(a, b)", "(min_log a b)"),
    ("f()", "f"),
    ("g(x + 1, y * 2)", "(g (x + 1) (y * 2))"),
    ("f(g(x), 2)", "(f (g x) 2)"),
    ("h(a, b,)", "(h a b)"),
    (
        "let s = sq(n); if s < m { s } else { m }",
        "(let s := (sq n); (if (s < m) then s else m))",
    ),
    (
        "forall<i: Int> 0 <= i ==> i * i >= 0",
        "(forall i : Int, ((0 ≤ i) → ((i * i) ≥ 0)))",
    ),
    ("exists<j: Int> n == j + j", "(∃ j : Int, (n = (j + j)))"),
    (
        "forall<i: Int, j: Int> i + j == j + i",
        "(forall i : Int, (forall j : Int, ((i + j) = (j + i))))",
    ),
    ("(forall<i: Int> p(i)) && q", "((forall i : Int, (p i)) ∧ q)"),
    (
        "forall<i: Int> exists<j: Int> i <= j",
        "(forall i : Int, (∃ j : Int, (i ≤ j)))",
    ),
    (
        "forall<i: u32> i + 1 > i",
        "(forall i : Int, (((0 ≤ i) ∧ (i < 4294967296)) → ((i + 1) > i)))",
    ),
    (
        "exists<j: u8> n == j + j",
        "(∃ j : Int, (((0 ≤ j) ∧ (j < 256)) ∧ (n = (j + j))))",
    ),
    (
        "forall<i: u64, j: Int> i <= j",
        "(forall i : Int, (((0 ≤ i) ∧ (i < 18446744073709551616)) → (forall j : Int, (i ≤ j))))",
    ),
]

SELF_TESTS_REFUSE = [
    ("(a + b)@", "model_deref_at"),
    ("xs.len()@", "unexpected_operator_'@'"),
    ("^ x", "prophecy_final"),
    ("x.foo()", "method_or_field_access"),
    ("x.len", "unexpected_end"),
    ("a[0]", "indexing"),
    ("forall i, p i", "quantifier_missing_binder"),
    ("forall<i> i >= 0", "binder_untyped_v1_3"),
    ("forall<i: usize> i >= 0", "machine_binder_platform_width"),
    ("forall<i: i32> i >= 0", "machine_binder_signed_v1"),
    ("forall<s: Seq> true", "binder_type_unsupported_'Seq'"),
    ("p && forall<i: Int> q", "quantifier_needs_parens_in_operand"),
    ("let x: Int = 1; x", "let_pattern_or_ascription"),
    ("match x { }", "match_v1_2"),
    ("let y = x", "let_missing_semicolon"),
    ("let mut x = 1; x", "let_mut"),
    ("let (a, b) = t; a", "let_pattern"),
    ("let (a) = t; a", "let_pattern"),
    ("let y = x; ", "unexpected_end"),
    ("if c { a }", "if_missing_else"),
    ("if c { a } else b", "if_missing_else_block"),
    ("if c == 1; { a } else { b }", "if_missing_then_block"),
    ("x = y", "unexpected_operator_'='"),
    ("x as u8", "cast"),
    ("a < b < c", "chained_comparison"),
    ("a & b", "reference_or_bitand"),
    ("(a + b", "unexpected_end"),
    ("10 u32", "unexpected_operator_'u32'"),
    ("a, b", "trailing_tokens_','"),
    ("f(a; b)", "call_malformed_';'"),
    ("f(,)", "unexpected_token_','"),
    ("dead", "pearlite_dead_term"),
    ("self + x", "self_receiver_v1_1"),
]


def self_test() -> int:
    failures = 0
    for source, expected in SELF_TESTS_OK:
        try:
            got = translate_expr(source)
        except Refused as refusal:
            print(f"FAIL translate {source!r}: refused {refusal}")
            failures += 1
            continue
        if got != expected:
            print(f"FAIL translate {source!r}: {got!r} != {expected!r}")
            failures += 1
    for source, expected_reason in SELF_TESTS_REFUSE:
        try:
            got = translate_expr(source)
        except Refused as refusal:
            if expected_reason not in str(refusal):
                print(f"FAIL refuse {source!r}: {refusal} !~ {expected_reason}")
                failures += 1
        else:
            print(f"FAIL refuse {source!r}: translated to {got!r}")
            failures += 1
    total = len(SELF_TESTS_OK) + len(SELF_TESTS_REFUSE)
    print(f"self-test: {total - failures}/{total} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    print(__doc__)
