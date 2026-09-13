#!/usr/bin/env python3
r"""Gate: every claim on the published landing page must be true of the Lean tree.

Why this exists
---------------
`index.html` is the hand-maintained dashboard that GitHub Pages serves at
lean.goldenphysics.org. Nothing ever checked it against the repository, and by
2026-08-31 an audit found that most of it was false:

  * **10 of its 23 theorem cards named declarations that exist nowhere in the tree**
    (`spectral_weil_connection`, `dm_abundance`, `wightman_axioms_from_gr24`,
    `twistor_googly_resolution`, `majorana_condition_T_boundary`,
    `hurwitz_critical_dims`, `holographic_chain`, `decoding_reality`,
    `dark_energy_t_boundary`, `unified_dipole`), each with a "View source" link
    into a file, several of which did not exist either.
  * **4 cards badged a `True`-stub as "Proved"** -- including
    `l2_constraint_implies_rh` ("L2 constraint forces Re(s) = 1/2"),
    `three_generations`, `anomaly_cancellation_forces_three_generations` and
    `yang_mills_mass_gap`.
  * The stat strip advertised **"0 Open Gaps"** against 150 stubs, "29 Verified
    Files" against 183 modules, and "19 proved clean / 10 proved w/ axioms"
    against a tree with exactly one axiom left.

None of it was malicious; the page was written early and the tree moved under it
for months. But it was the single most public artifact the project has, and every
number and name on it was wrong. Prose drifts silently -- so it gets a gate, the
same as the stub names and the blueprint references.

What this checks
----------------
1. Every `thm-name` on the page resolves to a declaration in `GppVerify/`.
2. Every `File:` path in a `thm-meta` exists.
3. Every "View source" link points at a file that exists.
4. No card badged "Proved" names an `open_`-prefixed declaration (a stub).
5. Any card naming an `open_` declaration is badged Open.
6. The `<head>` prose -- `<title>`, `<meta name="description">`, `og:title`,
   `og:description` -- asserts no result whose backing declaration is an `open_`
   stub. Checks 4 and 5 covered only the card grid. On 2026-09-13 the head was
   found advertising "Machine-checked proofs of shadow=CPT, L^2 forces
   Re(s)=1/2, and three fermion generations" while all three of those results
   were `theorem open_... : True := trivial` in the tree, and while the card
   gate was correctly forcing the body to badge each of them Open. Head prose
   travels further than the body: it is what search engines index and what every
   link preview renders. It gets the same rule.
7. The stat-strip numbers that are derivable from the tree (module count, stub
   count, axiom count) match it, and so do the same numbers restated in prose in
   the og:description.

Names carrying a space or an em dash are treated as prose headings, not
declarations, and are skipped by checks 1 and 4-5 -- but their file paths are
still checked.

Exit status: 0 clean, 1 on any false claim.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LANDING = REPO / "index.html"
LEAN_ROOT = REPO / "GppVerify"

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|structure|inductive|instance|class|opaque)\s+"
    r"(?P<name>[^\s({\[:]+)",
    re.MULTILINE,
)

# NOTE: do *not* try to match a card with `.*?</div>\s*</div>` -- a card's inner divs
# are not consecutive, so that pattern runs past the card boundary to the end of the
# enclosing grid and silently swallows the cards in between. An earlier version of this
# gate did exactly that and passed a card naming a declaration that did not exist. Split
# on the opening tag instead, which cannot skip a card.
CARD_OPEN = '<div class="thm-card '
NAME_RE = re.compile(r'<div class="thm-name">(.*?)</div>', re.DOTALL)
META_RE = re.compile(r'<div class="thm-meta">File:\s*(.*?)</div>', re.DOTALL)
BADGE_RE = re.compile(r'<div class="status-badge badge-(\w+)"')
SRCLINK_RE = re.compile(r'href="https://github\.com/GoldenPhysicsProject/GPPVerify/blob/main/([^"]+)"')
STAT_RE = re.compile(
    r'<span class="stat-num[^"]*"[^>]*>(?P<num>[\d,]+)</span>\s*'
    r'<span class="stat-label">(?P<label>[^<]+)</span>',
    re.DOTALL,
)


def declared_names() -> set[str]:
    names: set[str] = set()
    for path in LEAN_ROOT.rglob("*.lean"):
        for m in DECL_RE.finditer(path.read_text(encoding="utf-8")):
            names.add(m.group("name").split(".")[-1])
    return names


# The stub census and the comment stripper live in check_stub_naming.py. Import them rather
# than keeping a second copy: this file and that one disagreed by two on 2026-09-01 because
# the pattern was widened in one place and not the other, and two gates reporting different
# numbers for the same tree is precisely the drift these gates exist to prevent.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_stub_naming import STUB, strip_comments, declarations  # noqa: E402


def tree_counts() -> dict[str, int]:
    """Numbers the landing page is allowed to state, computed from the tree."""
    modules = 0
    stubs = 0
    axioms = 0
    for path in LEAN_ROOT.rglob("*.lean"):
        modules += 1
        src = strip_comments(path.read_text(encoding="utf-8"))
        axioms += len(re.findall(r"^axiom\s", src, re.M))
        for _name, _lineno, flat in declarations(src):
            if STUB.search(flat):
                stubs += 1
    return {"modules": modules, "stubs": stubs, "axioms": axioms}


# Stat labels the page may carry, mapped to the tree quantity they must equal.
CHECKED_STATS = {
    "Lean Modules": "modules",
    "Open Stubs": "stubs",
    "Axioms": "axioms",
}


# Head metadata fields whose prose is checked. These are the fields that leave the page:
# the browser tab, the search-engine snippet, and the link-preview card.
HEAD_FIELDS = (
    (r"<title>([^<]*)</title>", "<title>"),
    (r'<meta name="description" content="([^"]*)"', 'meta description'),
    (r'<meta property="og:title" content="([^"]*)"', "og:title"),
    (r'<meta property="og:description" content="([^"]*)"', "og:description"),
)

# Prose claims that are only true if a specific result is actually proved, mapped to the
# base name of the declaration that would carry them. A claim is forbidden in head prose
# when its declaration is absent from the tree, or present only under the `open_` prefix.
#
# Keep the patterns broad and the list short. A false positive here costs one deliberate
# edit by a person; a false negative puts an unproved theorem on the front page.
HEAD_CLAIMS: list[tuple[str, str]] = [
    (r"shadow\s*=\s*CPT|shadow[-\s]equals[-\s]CPT|\bCPT theorem\b", "cpt_theorem"),
    # NOTE: the historical text was "L\u00b2 forces Re(s)=\u00bd" with a SUPERSCRIPT two and a
    # vulgar one-half. A first version of this pattern spelled the exponent `2` and matched
    # neither, so the claim sailed through a gate written to catch it. Accept both forms,
    # and keep a standalone "Re(s) = 1/2" alternative so dropping the verb does not help.
    (r"L\s*[\u00b22][^.]{0,40}?forces?[^.]{0,30}?Re\s*\(\s*s\s*\)"
     r"|forces?\s+(the\s+)?critical\s+line"
     r"|(proof|proves|proved|machine-checked)[^.]{0,40}?Re\s*\(\s*s\s*\)\s*=\s*(\u00bd|1/2)",
     "l2_constraint_implies_rh"),
    (r"\bthree\s+(fermion\s+)?generations\b", "three_generations"),
    (r"\bmass\s+gap\b", "yang_mills_mass_gap"),
    (r"\bBorn\s+rule\b", "born_rule_from_haar"),
    (r"\bshadow\s+discontinuity\b", "shadow_discontinuity"),
    (r"(proof|proves|proved|proving)\s+of\s+the\s+Riemann\s+Hypothesis"
     r"|Riemann\s+Hypothesis\s+is\s+(proved|true|established)", "riemann_hypothesis"),
]


def head_claim_failures(html: str, declared: set[str]) -> list[str]:
    """Head prose may not assert a result the tree marks open."""
    out: list[str] = []
    for pattern, field in HEAD_FIELDS:
        m = re.search(pattern, html, re.I)
        if not m:
            continue
        text = m.group(1)
        for claim_re, decl in HEAD_CLAIMS:
            hit = re.search(claim_re, text, re.I)
            if not hit:
                continue
            if decl in declared:
                continue          # the real declaration exists: the claim is earned
            if "open_" + decl in declared:
                out.append(
                    f"{field} claims {hit.group(0)!r}, but the tree has only "
                    f"`open_{decl}` -- that result is an open stub"
                )
            else:
                out.append(
                    f"{field} claims {hit.group(0)!r}, but no declaration `{decl}` "
                    f"or `open_{decl}` exists in the tree"
                )
    return out


def main() -> int:
    if not LANDING.exists():
        print(f"landing page not found at {LANDING}", file=sys.stderr)
        return 1

    html = LANDING.read_text(encoding="utf-8")
    declared = declared_names()
    failures: list[str] = []

    chunks = html.split(CARD_OPEN)[1:]
    if not chunks:
        print("no theorem cards found in index.html -- has the markup changed?")
        return 1
    for chunk in chunks:
        body = chunk
        nm = NAME_RE.search(body)
        meta = META_RE.search(body)
        badge = BADGE_RE.search(body)
        name = nm.group(1).strip() if nm else None
        badge_kind = badge.group(1) if badge else None

        # A "name" containing whitespace or an em dash is a prose heading.
        is_decl = bool(name) and not re.search(r"[\s—]", name)

        if is_decl and name not in declared:
            failures.append(f"card names a declaration that does not exist: {name}")

        if is_decl and name.startswith("open_") and badge_kind == "proved":
            failures.append(
                f"card badges a True-stub as Proved: {name} "
                "(open_ prefix means the result is open)"
            )
        if is_decl and not name.startswith("open_") and badge_kind == "open":
            failures.append(
                f"card badges a real declaration as Open: {name}"
            )

        if meta:
            rel = meta.group(1).strip()
            if not (LEAN_ROOT / rel).exists():
                failures.append(f"card 'File:' path does not exist: GppVerify/{rel}")

        for link in SRCLINK_RE.finditer(body):
            target = link.group(1)
            if not (REPO / target).exists():
                failures.append(f"'View source' link points at a missing file: {target}")

    counts = tree_counts()
    for m in STAT_RE.finditer(html):
        label = m.group("label").strip()
        key = CHECKED_STATS.get(label)
        if key is None:
            continue
        stated = int(m.group("num").replace(",", ""))
        if stated != counts[key]:
            failures.append(
                f"stat '{label}' says {stated}; the tree has {counts[key]}"
            )

    # The visible stat block is not the only place the page states these numbers. The
    # og:description meta tag states them too, in prose, and it is what gets shown when
    # the page is shared anywhere — so a stale value there travels further than one in the
    # page body. It was stale: it read "Zero sorries, one axiom, 151 open stubs" while the
    # visible Axioms stat correctly read 0 and the tree held 156 stubs, because the gate
    # only ever looked at the stat spans. Check the prose too.
    og = re.search(r'<meta property="og:description" content="([^"]*)"', html)
    if og:
        text = og.group(1)
        for label, key in (("open stubs", "stubs"), ("axioms", "axioms")):
            m = re.search(r"(\d+)\s+" + re.escape(label), text)
            if m and int(m.group(1)) != counts[key]:
                failures.append(
                    f"og:description says {m.group(1)} {label}; the tree has {counts[key]}"
                )
        words = {"zero": 0, "one": 1, "two": 2, "three": 3}
        for word, n in words.items():
            if re.search(rf"\b{word} axioms?\b", text, re.I) and n != counts["axioms"]:
                failures.append(
                    f"og:description says '{word} axiom(s)'; the tree has {counts['axioms']}"
                )
            if re.search(rf"\b{word} sorries\b", text, re.I) and n != 0:
                failures.append(f"og:description says '{word} sorries'")

    failures.extend(head_claim_failures(html, declared))

    if failures:
        print("Landing-page claim check FAILED.\n")
        for f in failures:
            print(f"  {f}")
        print(
            "\nindex.html is served at lean.goldenphysics.org. Every name, path and\n"
            "number on it must be true of this tree. Fix the page, not this gate.\n"
            "\nThe three counts above are derived from the tree and have a fixer:\n"
            "  python3 scripts/sync_published_counts.py\n"
            "Names, paths, links and badges do not, and should not — a claim that has\n"
            "gone false is for a person to look at, not for a script to rewrite."
        )
        return 1

    print(
        f"Landing-page claim check passed "
        f"({counts['modules']} modules, {counts['stubs']} stubs, {counts['axioms']} axiom(s))."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
