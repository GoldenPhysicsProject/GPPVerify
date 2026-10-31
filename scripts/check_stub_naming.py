#!/usr/bin/env python3
"""Enforce the open_-prefix convention on `True`-stubs, and publish an honest count.

This repository parks an open result as `theorem foo : True := trivial` (or
`∀ (_ : True), True`). That is the honest convention -- far better than a `sorry` or an
axiom asserting the open claim -- but it has one sharp edge: a stub reports "does not
depend on any axioms", the cleanest possible bill of health, **while asserting nothing**.
A file full of stubs shows 0 sorry / 0 axiom and can read as fully proved when it is not.

Until 2026-08-30 that edge had actually cut: the repo contained, among others,

    theorem yang_mills_mass_gap : True := trivial
    theorem yang_mills_existence : True := trivial
    theorem weil_criterion : True := trivial
    theorem os_reconstruction : True := trivial

-- Millennium-Prize-scale problems and major open results, carrying the names of the
theorems they are *not*, in a tree advertising zero sorries and zero axioms. Nothing was
being smuggled into a proof (a `True` stub is inert, and none of these were referenced by
real content), but anyone grepping the source could reasonably have concluded otherwise.

The fix is structural rather than editorial: every stub name must begin with `open_`, so
the name itself says the result is open, and this gate makes a non-conforming stub fail
CI. `open_yang_mills_mass_gap : True := trivial` cannot be misread.

## Why this script was rewritten (2026-08-31)

The first version of this gate matched **line by line**: it remembered the most recent
`theorem`/`lemma` line, then looked for `: True := trivial` on some later line. That
misses a stub written like this --

    theorem shadow_discontinuity :
        -- Disc(celestial amplitude) = shadow transform jump = loop integrand
        True := trivial

-- because the line carrying `True := trivial` has no `:` in front of `True` (the colon
is two lines up, separated by a comment). Eight stubs were invisible to the gate for
exactly this reason, and **all eight were unprefixed**, including
`shadow_discontinuity`, `born_rule_from_haar`, `meyer_spectral_weil` and
`adelic_l2_regularization`. The gate reported "All True-stubs correctly prefixed" while
the very names it exists to catch sat in the tree, and the published count was 142 when
the real number was 150.

So the gate no longer reads lines. It strips Lean comments first (both `--` and `/- -/`,
nested), splits the source into whole declarations, and tests each declaration as a unit.
A stub cannot hide behind a comment in the middle of its own statement.

Exit 1 (failing the build) if any `True`-stub declaration lacks the prefix, or if the
count stated in the blueprint has drifted from the real one.

Since 2026-10-31 the gate also enforces closure contracts on stubs (canonization
rule 4): a new stub, or an old stub whose declaration/attached comments have been
touched, fails unless its contract text states the intended statement, a source, and
a closing criterion. Pre-adoption stubs are exempt through
`scripts/stub_contract_baseline.txt`; regenerate that file with
`python3 scripts/check_stub_naming.py --write-baseline`. See the "Closure contracts"
section below for the exact accepted forms.
"""

import hashlib
import re
import sys
from pathlib import Path

# A declaration starts at column 0 with one of these keywords (or an attribute that
# precedes one). Anything indented is inside the declaration we are already in.
DECL_START = re.compile(
    r"^(?:@\[|theorem|lemma|def|noncomputable|instance|structure|inductive|abbrev|example|"
    r"class|opaque|axiom)\b",
    re.M,
)
NAME = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?]*)")

# Applied to a whole declaration with comments already stripped and whitespace flattened.
#
# A stub is any declaration whose *conclusion* is `True` and whose proof is trivial-equivalent.
# Both halves need to be permissive, and each was widened after a stub slipped through:
#
#   `theorem foo : True := trivial`                     -- the original shape
#   `theorem foo : ∀ (_ : True), True := by intro; trivial`
#   `theorem foo : ∀ (_ : ℂ), True := fun _ => trivial` -- binder is NOT `True` …
#   `theorem foo (_ : ℝ) : ∀ (_ : ℂ), True := fun _ => trivial`  -- … and args come first
#
# The third and fourth shapes hid `thm_universal_shadow_product` and
# `scaling_eigenspace_ode` — both unprefixed — until 2026-09-01. The earlier version keyed
# on the binder being literally `True` and the proof being literally `trivial`; neither is
# what makes a declaration vacuous. What makes it vacuous is the conclusion.
STUB = re.compile(
    # (a) The original two shapes, kept verbatim. Widening this pattern must never *lose* a
    #     detection, and taking the union by construction is the only way to guarantee that
    #     -- an earlier attempt at a "cleaner" single pattern silently dropped four stubs
    #     written as `by intro _ <newline> trivial`, because it required a semicolon.
    r":\s*True\s*:=\s*(?:by\s+)?trivial\b"
    r"|∀\s*\(_\s*:\s*True\)\s*,\s*True\s*:="
    # (b) Conclusion `True` under ANY binders, with a trivial-equivalent proof. What makes a
    #     declaration vacuous is its conclusion -- not that the binder is literally `True`,
    #     and not that the proof is literally the token `trivial`. Keying on those was how
    #     `thm_universal_shadow_product` (`∀ (_ : ℂ), True := fun _ => trivial`) and
    #     `scaling_eigenspace_ode` (`(_ : ℝ) : ∀ (_ : ℂ), True := fun _ => trivial`) stayed
    #     invisible -- both unprefixed -- until 2026-09-01.
    r"|:\s*(?:∀[^,]*,\s*)*True\s*:=\s*(?:(?:by|fun|intro|=>|_|;)\s*)*trivial\b"
)

# The blueprint publishes this number in prose; keep it honest automatically.
BLUEPRINT = Path("blueprint/src/web.tex")
BLUEPRINT_COUNT = re.compile(r"There are currently \\textbf\{(\d+)\} such stubs\.")

# --------------------------------------------------------------------------------------
# Reflexivity tautologies -- a SECOND way to assert nothing (added 2026-09-01)
# --------------------------------------------------------------------------------------
#
# Everything above hunts for the conclusion `True`. That is not the only vacuous
# conclusion. A declaration whose conclusion is `X = X` for syntactically identical `X`
# is equally empty, is proved by `rfl`, and reports the same spotless axiom bill -- and
# because it is not `True`, every version of the gate so far walked straight past it.
#
# Eleven were in the tree when this check was written, none of them prefixed, several
# carrying the name of a substantive claim:
#
#   theorem three_generations : (3 : ℕ) = 3 := rfl            -- the headline SM prediction
#   lemma  test_function_fe_symmetric (h) (rho) : h rho = h rho := rfl
#   theorem mirror_baryon_lower_bound : (1 : ℕ) ≤ 1 := le_refl 1
#   theorem dim_sun (n) (_ : 1 ≤ n) : n^2 - 1 = n^2 - 1 := rfl
#   theorem kac_moody_level_appears_in_commutator (k m δ_ab δ_mn) : … = … := rfl
#
# `test_function_fe_symmetric` sat under a section header reading "algebraic spectral
# facts (proved clean)" and was `#check`ed in its file's summary. `three_generations`
# said "OPEN PROBLEM" in capitals in its own docstring.
#
# The check is deliberately syntactic and conservative: it compares the two sides of the
# top-level relation as text, after stripping one layer of type ascription, and only
# fires when they are character-for-character identical. `2 - (2 - Δ) = Δ` is not caught
# (nor should it be -- it is a real theorem); `2 - Δ = 2 - Δ` is.
RELATIONS = (" = ", " ↔ ", " ≤ ", " ⊆ ", " ⊇ ", " ≥ ")
# The type part excludes `,` so that a parenthesized binder `(∀ x : H, P x)` is not
# mistaken for an ascription `(x : H)` -- that collapsed `(∀ x : H, A) ↔ (∀ x : H, B)`
# to `∀ x ↔ ∀ x` and flagged real equivalences (found 2026-09-26).
ASCRIPTION = re.compile(r"^\((.*?)\s*:\s*[^:(),]*\)$")


def _split_top(s: str, tok: str):
    """Split `s` at the first occurrence of `tok` at bracket depth 0."""
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and s.startswith(tok, i):
            return s[:i], s[i + len(tok):]
        i += 1
    return None, None


def _strip_ascription(x: str) -> str:
    x = x.strip()
    m = ASCRIPTION.match(x)
    return m.group(1).strip() if m else x


def is_reflexive_tautology(flat: str) -> bool:
    """True if the declaration's conclusion is `X R X` for identical `X`."""
    head, _ = _split_top(flat, " := ")
    if head is None:
        head, _ = _split_top(flat, ":= by")
    if head is None:
        return False
    _, stmt = _split_top(head, " : ")
    if stmt is None:
        return False
    stmt = stmt.strip()
    # Peel leading `∀ …,` binders so the conclusion is what gets compared.
    while stmt.startswith("∀"):
        _, rest = _split_top(stmt, ", ")
        if rest is None:
            break
        stmt = rest.strip()
    for tok in RELATIONS:
        lhs, rhs = _split_top(stmt, tok)
        if lhs is None:
            continue
        return bool(lhs) and _strip_ascription(lhs) == _strip_ascription(rhs)
    return False


def strip_comments(src: str) -> str:
    """Remove Lean line comments and (nested) block comments, preserving newlines.

    Newlines are preserved so that line numbers stay usable for error messages.
    """
    out: list[str] = []
    i = 0
    depth = 0
    n = len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                break
            out.append(" " * (j - i))
            i = j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def declarations(src: str):
    """Yield (name, line_number, flattened_text) for each theorem/lemma declaration."""
    starts = [m.start() for m in DECL_START.finditer(src)] + [len(src)]
    for a, b in zip(starts, starts[1:]):
        chunk = src[a:b]
        m = NAME.match(chunk)
        if not m:
            continue
        yield m.group(1), src.count("\n", 0, a) + 1, re.sub(r"\s+", " ", chunk).strip()


# --------------------------------------------------------------------------------------
# Gap labels: "MATHLIB GAP" answers the wrong question (added 2026-09-02)
# --------------------------------------------------------------------------------------
#
# The `open_` prefix says a result is open. It does not say *why*, and the tree used one
# label — `MATHLIB GAP:` — for two situations that could not be more different:
#
#   * a known theorem merely absent from Mathlib, which formalization effort closes;
#   * mathematics nobody has, which formalization effort does not touch.
#
# Both are true statements of the form "X is not in Mathlib", so the label fit both and
# distinguished neither. That misdirection has now been caught five separate times:
#
#   open_zero_simplicity          simplicity of ζ's zeros — open, filed as reachable
#                                 (CLAUDE_CORRECTIONS.md entry 12)
#   the shadow-product cluster    blocked on RH; gap statement named Hadamard (entry 16)
#   open_yang_mills_mass_gap      Millennium Prize problem, labelled
#                                 "MATHLIB GAP: All of the above"
#   open_generalised_rh           GRH, labelled "MATHLIB GAP: Hecke L-functions absent"
#   open_weil_positivity_haar_squares
#                                 RH-equivalent by Weil's criterion — which this same repo
#                                 states as an iff one file away — labelled "MATHLIB GAP"
#
# Every one of those points a future session at a library task that will not close it.
#
# The gate does not decide which label is right; it makes the ambiguous one unavailable, so
# that whoever writes the note has to choose:
#
#   LIBRARY GAP    known mathematics, absent from Mathlib. Formalization closes it.
#   OPEN PROBLEM   the mathematics does not exist. Formalization does not close it.
#   FRAMEWORK CLAIM  a proposal of the shadow framework, or a physical prediction. Library
#                    work lets you state it; whether it holds is a research question.
#
# A stub may carry more than one (most `FRAMEWORK CLAIM`s also have a `LIBRARY GAP` before
# they can even be written down). Only the bare word `MATHLIB` as a label is rejected.
#
# Matches a label at the start of a line (optionally after `--`), so prose *discussing* the
# old label — which the correction notes necessarily quote — is not caught.
GAP_LABEL = re.compile(r"^[ \t]*(?:--[ \t]*)?MATHLIB[ \t]+GAPS?[ \t]*:", re.M)


# --------------------------------------------------------------------------------------
# Closure contracts on stubs (canonization rule 4, added 2026-10-31)
# --------------------------------------------------------------------------------------
#
# The `open_` prefix says a result is open. It does not say what the result *is*, what
# fixes its statement, or what would close it -- so closing a stub used to cost
# archaeology before it cost proof. (The five stubs closed on 2026-10-28 were exactly
# the ones whose content was already pinned down in writing.) Rule 4 of the
# canonization protocol (GPP-bridge, adopted 2026-10-31) therefore requires every stub
# to carry a closure contract with three parts:
#
#   (a) the intended statement -- the exact claim the stub is a placeholder for;
#   (b) a source -- the paper/book/section that fixes that statement;
#   (c) a closing criterion -- what counts as closing the stub.
#
# Canonical form (in the stub's docstring, or in attached comments -- the tree's
# existing contracts, e.g. `open_yang_mills_mass_gap`, put SOURCE / CLOSURE CONTRACT
# lines in `--` comments directly under the declaration, and those count):
#
#   /-- <one-line claim>.
#
#       Intended statement: <exact statement to be proved>.
#       Source: <reference that fixes the statement>.
#       Closes when: <what counts as closing this stub>. -/
#   theorem open_foo : True := trivial
#
# Accepted forms (case-insensitive; the check searches the stub's whole contract
# text, defined below):
#   (a) "Intended statement", a line beginning "Intended:", or a line beginning
#       "Statement:".
#   (b) "Source:" or "Sources:" anywhere.
#   (c) "closes when" / "closes exactly when" / "closed when" (any `clos\w*` verb),
#       "closing criterion", "closure criterion", or "closure contract".
#
# The *contract text* of a stub is its attached comments: the comment run immediately
# preceding the declaration (whitespace-only gaps -- this catches the docstring) plus
# every comment inside the declaration's block (up to the next declaration -- this
# catches the under-declaration SOURCE / CLOSURE CONTRACT lines).
#
# Scope: the requirement applies to NEW stubs and to stubs TOUCHED since adoption --
# not as a bulk rewrite of the existing census. `scripts/stub_contract_baseline.txt`
# lists every stub exempted at adoption, keyed by (file, name) with a short hash of
# its source block (contract text + declaration text). If a baselined stub's block
# changes, its hash no longer matches, the exemption lapses, and the stub must carry
# the contract like any new one. Regenerate the baseline (deliberately, in review)
# with:  python3 scripts/check_stub_naming.py --write-baseline

CONTRACT_PARTS: list[tuple[str, list[re.Pattern]]] = [
    (
        "intended statement",
        [
            re.compile(r"intended\s+statement", re.I),
            re.compile(r"^\s*intended\s*:", re.I | re.M),
            re.compile(r"^\s*statement\s*:", re.I | re.M),
        ],
    ),
    (
        "source",
        [re.compile(r"\bsources?\s*:", re.I)],
    ),
    (
        "closing criterion",
        [
            re.compile(r"clos\w*\s+(?:exactly\s+)?when", re.I),
            re.compile(r"closing\s+criterion", re.I),
            re.compile(r"closure\s+criterion", re.I),
            re.compile(r"closure\s+contract", re.I),
        ],
    ),
]

BASELINE = Path("scripts/stub_contract_baseline.txt")


def comment_spans(src: str) -> list[tuple[int, int, str]]:
    """(start, end, inner_text) for every comment in `src`, doc comments included.

    Mirrors `strip_comments`' nesting rules. Inner text excludes the delimiters.
    """
    spans: list[tuple[int, int, str]] = []
    i, n = 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth = 0
            j = i
            while j < n:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                    continue
                if src.startswith("-/", j) and depth:
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                    continue
                j += 1
            spans.append((i, j, src[i + 2 : j - 2] if j - i >= 4 else ""))
            i = j
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                j = n
            spans.append((i, j, src[i + 2 : j]))
            i = j
            continue
        i += 1
    return spans


def strip_comments_preserving(src: str) -> str:
    """`strip_comments`, but length-preserving: the `/-` / `-/` delimiters become
    spaces instead of vanishing.

    The project's `strip_comments` drops the two delimiter characters at each end of
    a block comment, so offsets in its output drift from the raw source by four per
    block comment (line numbers survive; byte offsets do not). `stub_blocks` needs
    true offsets to recover docstrings from the raw source, so it strips with this
    variant. The text content is otherwise identical, and declaration detection on
    it is unchanged (delimiters become whitespace, which the declaration flattening
    already collapses).
    """
    out: list[str] = []
    i = 0
    depth = 0
    n = len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if src.startswith("-/", i) and depth:
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                out.append(" " * (n - i))
                break
            out.append(" " * (j - i))
            i = j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def stub_blocks(raw: str):
    """Yield (name, line_number, contract_text, block_hash) for each True-stub.

    Declaration offsets are taken from `strip_comments_preserving` output, whose
    offsets index the raw source directly -- which is what lets the docstring and
    attached comments be recovered here.
    """
    stripped = strip_comments_preserving(raw)
    spans = comment_spans(raw)
    starts = [m.start() for m in DECL_START.finditer(stripped)] + [len(stripped)]
    for a, b in zip(starts, starts[1:]):
        chunk = stripped[a:b]
        m = NAME.match(chunk)
        if not m:
            continue
        flat = re.sub(r"\s+", " ", chunk).strip()
        stub = STUB.search(flat)
        if not stub:
            continue
        # The comment run immediately before the declaration (whitespace-only gaps).
        before: list[str] = []
        boundary = a
        for s, e, text in reversed([sp for sp in spans if sp[1] <= a]):
            if raw[e:boundary].strip() == "":
                before.append(text)
                boundary = s
            else:
                break
        before.reverse()
        # Every comment inside the declaration's own block.
        inside = [text for s, _e, text in spans if a <= s < b]
        contract = "\n".join(before + inside)
        digest = hashlib.sha256(
            (contract + "\x00" + flat[: stub.end()]).encode("utf-8")
        ).hexdigest()[:12]
        yield m.group(1), stripped.count("\n", 0, a) + 1, contract, digest


def missing_contract_parts(contract: str) -> list[str]:
    """Names of the contract parts absent from `contract` (empty list = complete)."""
    return [
        label
        for label, patterns in CONTRACT_PARTS
        if not any(p.search(contract) for p in patterns)
    ]


def load_baseline(repo: Path) -> dict[tuple[str, str], set[str]]:
    """(relative_path, stub_name) -> set of exempting block hashes."""
    out: dict[tuple[str, str], set[str]] = {}
    path = repo / BASELINE
    if not path.exists():
        return out
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        name, rel, digest = parts
        out.setdefault((rel, name), set()).add(digest)
    return out


def collect_stub_census(repo: Path, root: Path, baseline) -> list[tuple]:
    """(rel_path, name, line, missing_parts, digest, exempt) for every True-stub."""
    census: list[tuple] = []
    for path in sorted(root.rglob("*.lean")):
        rel = str(path.relative_to(repo))
        for name, lineno, contract, digest in stub_blocks(path.read_text(encoding="utf-8")):
            exempt = digest in baseline.get((rel, name), set())
            census.append(
                (rel, name, lineno, missing_contract_parts(contract), digest, exempt)
            )
    return census


def write_baseline(repo: Path, census: list[tuple]) -> Path:
    path = repo / BASELINE
    lines = [
        "# Stub-contract baseline for scripts/check_stub_naming.py (canonization rule 4).",
        "#",
        "# Every stub listed here is exempt from the closure-contract requirement.",
        "# The exemption lapses automatically when the stub's declaration or attached",
        "# comments change: the stored hash of its source block stops matching, and the",
        "# stub is then checked like a new one. Regenerate deliberately, in review,",
        "# with:  python3 scripts/check_stub_naming.py --write-baseline",
        "#",
        "# Format: <stub name>\\t<file>\\t<sha256(block)[:12]>",
    ]
    for rel, name, _lineno, _missing, digest, _exempt in sorted(
        census, key=lambda c: (c[0], c[1])
    ):
        lines.append(f"{name}\t{rel}\t{digest}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    root = repo / "GppVerify"

    if "--write-baseline" in sys.argv:
        census = collect_stub_census(repo, root, load_baseline(repo))
        path = write_baseline(repo, census)
        print(
            f"Wrote {BASELINE}: {len(census)} stub(s) exempted at the current tree. "
            "Review the diff before committing it -- regenerating the baseline is how "
            "a touched stub is deliberately re-exempted, so it should never be routine."
        )
        return 0

    offenders: list[str] = []
    tautologies: list[str] = []
    gap_labels: list[str] = []
    total = 0

    for path in sorted(root.rglob("*.lean")):
        raw = path.read_text()
        for m in GAP_LABEL.finditer(raw):
            lineno = raw.count("\n", 0, m.start()) + 1
            gap_labels.append(f"{path.relative_to(repo)}:{lineno}")
        src = strip_comments(raw)
        for name, lineno, flat in declarations(src):
            if STUB.search(flat):
                total += 1
                if not name.startswith("open_"):
                    offenders.append(f"{path.relative_to(repo)}:{lineno}: {name}")
                continue
            if is_reflexive_tautology(flat):
                tautologies.append(f"{path.relative_to(repo)}:{lineno}: {name}")

    print(f"True-stubs found: {total}")

    failed = False
    if offenders:
        failed = True
        print(f"::error::{len(offenders)} stub(s) do not use the required 'open_' prefix.")
        print("A `True := trivial` stub asserts nothing but reports a clean axiom bill.")
        print("Prefix the name with 'open_' so it cannot be mistaken for a proved result:")
        for entry in offenders:
            print(f"  {entry}")
    else:
        print("All True-stubs correctly prefixed 'open_'.")

    if tautologies:
        failed = True
        print(f"::error::{len(tautologies)} declaration(s) state `X = X` for identical X.")
        print("A reflexivity tautology asserts nothing, exactly like a `True` stub, but")
        print("carries a real-looking statement. Either state what the name claims, or")
        print("make it an honest `open_… : True := trivial` stub so it gets counted:")
        for entry in tautologies:
            print(f"  {entry}")
    else:
        print("No reflexivity tautologies (`X = X`) found.")

    if gap_labels:
        failed = True
        print(f"::error::{len(gap_labels)} gap note(s) use the ambiguous label 'MATHLIB GAP'.")
        print("'X is not in Mathlib' is true both of a known theorem awaiting formalization")
        print("and of mathematics nobody has. Those are opposite situations, and the second")
        print("has been mislabelled as the first five times in this tree — including the")
        print("Yang-Mills mass gap, GRH, and a statement equivalent to RH. Choose one:")
        print("  LIBRARY GAP     known mathematics, absent from Mathlib — formalization closes it")
        print("  OPEN PROBLEM    the mathematics does not exist — formalization does not")
        print("  FRAMEWORK CLAIM a proposal or physical prediction — library work only states it")
        print("More than one may apply. Sites:")
        for entry in gap_labels:
            print(f"  {entry}")
    else:
        print("No ambiguous 'MATHLIB GAP' labels (LIBRARY / OPEN PROBLEM / FRAMEWORK CLAIM).")

    # Closure contracts (canonization rule 4; see the section above). Baselined stubs
    # are exempt until touched; every other stub must state what it is, what fixes its
    # statement, and what closes it.
    census = collect_stub_census(repo, root, load_baseline(repo))
    contract_failures = [c for c in census if not c[5] and c[3]]
    n_checked = sum(1 for c in census if not c[5])
    n_exempt = len(census) - n_checked
    print(
        f"Stub contracts: {n_checked} checked, {n_exempt} exempt under the baseline"
        f" ({BASELINE}), {len(contract_failures)} without a full contract."
    )
    if contract_failures:
        failed = True
        print(
            f"::error::{len(contract_failures)} stub(s) lack a closure contract "
            "(canonization rule 4)."
        )
        print("A stub without a contract costs archaeology before it costs proof. Give")
        print("it the three parts, in its docstring or in attached comments:")
        print("  Intended statement: <exact statement to be proved>")
        print("  Source: <reference that fixes the statement>")
        print("  Closes when: <what counts as closing this stub>")
        print("Offenders (name -- missing parts):")
        for rel, name, lineno, missing, _digest, _exempt in contract_failures:
            print(f"  {rel}:{lineno}: {name} -- missing: {', '.join(missing)}")

    # The blueprint states the stub count in prose. A hand-maintained number drifts --
    # it already had (141 published against 150 actual) -- so check it here rather than
    # trusting whoever edits the LaTeX next.
    blueprint = repo / BLUEPRINT
    if blueprint.exists():
        m = BLUEPRINT_COUNT.search(blueprint.read_text())
        if not m:
            failed = True
            print(
                "::error::Could not find the stub count sentence in "
                f"{BLUEPRINT}. Expected the exact phrasing "
                r"'There are currently \textbf{N} such stubs.'"
            )
        elif int(m.group(1)) != total:
            failed = True
            print(
                f"::error::{BLUEPRINT} states {m.group(1)} stubs; the tree has {total}. "
                "Update the blueprint sentence so the published ledger is not a lie — "
                "`python3 scripts/sync_published_counts.py` does it, and the same run "
                "fixes the matching numbers on index.html."
            )
        else:
            print(f"Blueprint stub count agrees with the tree ({total}).")

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
