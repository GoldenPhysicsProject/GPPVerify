#!/usr/bin/env python3
"""Rewrite the derived numbers on `index.html` to match the Lean tree.

## Why this exists

`check_landing_claims.py` gates the published landing page against the tree: the module,
stub and axiom counts in the stat strip, and the same counts stated in prose in the
`og:description` meta tag, must all be true. That gate is worth keeping strict — the page is
served at lean.goldenphysics.org and is the most public artifact the project has.

But those three numbers are *derived*. Nobody decides them; the tree does. So every branch
that adds or removes a Lean module, or parks a new `open_… : True := trivial` stub, makes
them stale as a side effect, and the gate then reds on a staleness the branch author did not
choose and cannot be said to have got wrong. That is the failure mode a gate should not have:
it produces red runs that everyone learns to wave through, which is exactly how a gate stops
being read at all.

Concretely, on 2026-09-02 the `wire root` dispatch — the whole point of which is to be a
one-command mechanical fix — went red on:

    stat 'Lean Modules' says 187; the tree has 188

after wiring in a single module. Every legitimate wiring run would have done that.

So: the gate stays, and this script is its fixer. Same pairing as
`check_import_graph.py` (detects modules outside the root graph) and `wire_root.py` (fixes
them).

## The counts come from the gate, not from a second implementation

`tree_counts()` is imported from `check_landing_claims.py` rather than reimplemented. This is
deliberate and it is the whole reason the script is short. On 2026-09-01
`check_landing_claims.py` and `check_stub_naming.py` disagreed by two about the stub count,
because the stub pattern was widened in one and not the other — two scripts reporting
different numbers for the same tree, which is precisely the drift these gates exist to
prevent. A *fixer* that counted independently of the gate it feeds would be the same bug with
a shorter fuse: it would write a number the gate then rejects.

## What it does NOT touch

Only the three derived counts, and only where the gate already looks. Theorem-card names,
file paths, source links, badges and every word of prose on the page stay exactly as written
— those are claims a person made, and a claim that has gone false is a thing for a person to
fix, not for a script to quietly rewrite into truth. The distinction this script draws is
between a number the tree computes and a statement someone chose to make.

## Use

    python3 scripts/sync_landing_stats.py            # rewrite the numbers
    python3 scripts/sync_landing_stats.py --check    # report only, exit 1 if any are stale
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_landing_claims import (  # noqa: E402
    CHECKED_STATS,
    LANDING,
    tree_counts,
)

# Number words the og:description is allowed to use, and how to write a count back as one.
# The gate reads "zero axioms" and "one axiom" as claims about the tree, so the fixer has to
# be able to write them; above three it falls back to a numeral rather than inventing prose.
WORDS = {0: "zero", 1: "one", 2: "two", 3: "three"}
WORD_VALUES = {word: n for n, word in WORDS.items()}


def sync_stats(html: str, counts: dict[str, int]) -> str:
    """Rewrite the stat-strip spans whose label names a derived quantity."""

    def repl(m: re.Match[str]) -> str:
        key = CHECKED_STATS.get(m.group("label").strip())
        if key is None:
            return m.group(0)
        return m.group(0).replace(f">{m.group('num')}<", f">{counts[key]}<", 1)

    # Rebuilt from the gate's own STAT_RE shape, but with the number and label captured
    # separately from the surrounding tags so the replacement can put the tags back
    # untouched — the spans carry inline `style` attributes that must survive.
    pattern = re.compile(
        r'<span class="stat-num[^"]*"[^>]*>(?P<num>[\d,]+)</span>\s*'
        r'<span class="stat-label">(?P<label>[^<]+)</span>',
        re.DOTALL,
    )
    return pattern.sub(repl, html)


def sync_og(html: str, counts: dict[str, int]) -> str:
    """Rewrite the counts stated in prose in the og:description meta tag.

    That tag is what gets shown wherever the page is shared, so a stale number there travels
    further than one in the page body. It has been stale before: it read "one axiom" while
    the visible Axioms stat correctly read 0.
    """
    m = re.search(r'(<meta property="og:description" content=")([^"]*)(")', html)
    if not m:
        return html
    text = m.group(2)

    for label, key in (("open stubs", "stubs"), ("axioms", "axioms"), ("axiom", "axioms")):
        text = re.sub(
            r"\d+(?=\s+" + re.escape(label) + r"\b)",
            str(counts[key]),
            text,
        )

    def word_repl(m: re.Match[str]) -> str:
        n = counts["axioms"]
        word = WORDS.get(n, str(n))
        # Keep the original capitalisation: the tag opens with "Zero sorries, ...".
        if m.group(1)[0].isupper():
            word = word.capitalize()
        return f"{word} {'axiom' if n == 1 else 'axioms'}"

    text = re.sub(
        r"\b(" + "|".join(WORD_VALUES) + r")\s+(axioms?)\b",
        word_repl,
        text,
        flags=re.I,
    )
    return html[: m.start(2)] + text + html[m.end(2) :]


def main() -> int:
    check_only = "--check" in sys.argv[1:]
    if not LANDING.exists():
        print(f"landing page not found at {LANDING}", file=sys.stderr)
        return 1

    counts = tree_counts()
    html = LANDING.read_text(encoding="utf-8")
    new = sync_og(sync_stats(html, counts), counts)

    summary = (
        f"{counts['modules']} modules, {counts['stubs']} stubs, {counts['axioms']} axiom(s)"
    )
    if new == html:
        print(f"Landing-page numbers already match the tree ({summary}).")
        return 0

    if check_only:
        print(f"Landing-page numbers are stale; the tree has {summary}.")
        print("Run without --check to rewrite them.")
        return 1

    LANDING.write_text(new, encoding="utf-8")
    print(f"Synced the landing page's derived numbers to the tree ({summary}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
