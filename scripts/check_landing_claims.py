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
6. The stat-strip numbers that are derivable from the tree (module count, stub
   count, axiom count) match it.

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

    if failures:
        print("Landing-page claim check FAILED.\n")
        for f in failures:
            print(f"  {f}")
        print(
            "\nindex.html is served at lean.goldenphysics.org. Every name, path and\n"
            "number on it must be true of this tree. Fix the page, not this gate."
        )
        return 1

    print(
        f"Landing-page claim check passed "
        f"({counts['modules']} modules, {counts['stubs']} stubs, {counts['axioms']} axiom(s))."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
