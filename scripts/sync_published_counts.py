#!/usr/bin/env python3
"""Rewrite every published count that is derived from the Lean tree, so it matches the tree.

Three surfaces publish those counts, and a gate checks each of them:

* `index.html` — the stat strip (`Lean Modules`, `Open Stubs`, `Axioms`) and the same numbers
  stated in prose in the `og:description` meta tag. Gated by `check_landing_claims.py`.
* `blueprint/src/web.tex` — the sentence "There are currently \\textbf{N} such stubs."
  Gated by `check_stub_naming.py`.
* `README.md` — the sentence "The library holds N Lean modules." and the per-directory
  file counts in the Layout table. Gated by this script's own `--check` mode, which the
  Build workflow runs alongside the other two gates. The README counts joined the set on
  2026-11-23: the sentence still read "about 1,200" against a 1,459-module tree, and the
  Layout table's largest row read 585 against 795 files — the same staleness as the other
  two surfaces, on the one surface nobody had thought to gate. A hand-written count is a
  claim about the tree that the tree keeps falsifying; the fix is the same as everywhere
  else in this script: the number is written from the tree, or it is not written.

## Why this exists

Both gates are worth keeping strict: `index.html` is served at lean.goldenphysics.org and is
the most public artifact the project has, and the blueprint sentence is the published stub
ledger.

But those numbers are *derived*. Nobody decides them; the tree does. So every branch that adds
or removes a Lean module, or parks a new `open_… : True := trivial` stub, makes them stale as
a side effect, and the gates then red on a staleness the branch author did not choose and
cannot be said to have got wrong. That is the failure mode a gate should not have: it produces
red runs everyone learns to wave through, which is exactly how a gate stops being read at all.

Concretely, on 2026-09-02 the `wire root` dispatch — the whole point of which is to be a
one-command mechanical fix — went red on:

    stat 'Lean Modules' says 187; the tree has 188

after wiring in a single module. Every legitimate wiring run would have done that. The first
version of this script fixed only `index.html`, and the very next self-test — a fixture module
carrying one stub, which is what a real payload branch looks like — went red on the *other*
derived number:

    blueprint/src/web.tex states 157 stubs; the tree has 158

Same bug, second surface. Hence the wider scope and the name: the unit that needs fixing is
"published counts", not "the landing page".

So: the gates stay, and this script is their fixer. Same pairing as `check_import_graph.py`
(detects modules outside the root graph) and `wire_root.py` (fixes them).

## The counts and the patterns come from the gates, not from a second implementation

`tree_counts()` is imported from `check_landing_claims.py`, and the blueprint path and regex
from `check_stub_naming.py`, rather than reimplemented here. This is deliberate and it is the
whole reason the script is short. On 2026-09-01 those two gates disagreed by two about the
stub count, because the stub pattern was widened in one and not the other — two scripts
reporting different numbers for the same tree, which is precisely the drift these gates exist
to prevent. A *fixer* that counted independently of the gate it feeds would be the same bug
with a shorter fuse: it would write a number the gate then rejects.

## What it does NOT touch

Only the derived counts, and only where a gate looks. Theorem-card names, file paths,
source links, badges, and every other word of prose on any surface stay exactly as written
— those are claims a person made, and a claim that has gone false is a thing for a person to
fix, not for a script to quietly rewrite into truth. The distinction this script draws is
between a number the tree computes and a statement someone chose to make.

## Use

    python3 scripts/sync_published_counts.py            # rewrite the numbers
    python3 scripts/sync_published_counts.py --check    # report only, exit 1 if any are stale
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_landing_claims import (  # noqa: E402
    CHECKED_STATS,
    LANDING,
    REPO,
    tree_counts,
)
from check_stub_naming import BLUEPRINT, BLUEPRINT_COUNT  # noqa: E402

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


def sync_blueprint(tex: str, counts: dict[str, int]) -> str:
    """Rewrite the blueprint's published stub count.

    The pattern is the gate's own `BLUEPRINT_COUNT`, so the sentence this writes is by
    construction the sentence `check_stub_naming.py` reads.
    """
    return BLUEPRINT_COUNT.sub(
        lambda m: m.group(0).replace(m.group(1), str(counts["stubs"]), 1), tex
    )


README = REPO / "README.md"

# The README's module sentence. The count is written exactly (no "about"): a rounded
# number is still a claim, and it goes stale at the same speed as an exact one while
# telling the reader less.
README_MODULES = re.compile(r"The library holds (?:about )?[\d,]+ Lean modules")

# One Layout-table row: `| <dirs> | <count> | <contents> |`. Only the count cell is
# rewritten, and only on rows whose first cell leads with a `GppVerify/…` directory —
# those are the rows stating a count of tree files. Rows for `discovery/`, `docs/` and
# the rest carry no count and are not touched.
README_TABLE_ROW = re.compile(r"^(\|[^|]*\| )[\d,]+( \|.*)$")


def _lean_files_under(rel: str) -> int:
    base = REPO / rel
    if not base.is_dir():
        return 0
    return sum(1 for _ in base.rglob("*.lean"))


def _layout_row_dirs(first_cell: str) -> list[str]:
    """Directories a Layout row counts, or [] if the row is not a tree-count row.

    The lead token must be a full `GppVerify/…` path. Combined rows name the first
    directory in full and the rest bare (`` `ThreadHT/` ``), and a bare token after a
    `GppVerify/` lead is its sibling under `GppVerify/`.
    """
    tokens = re.findall(r"`([^`]+)`", first_cell)
    dirs: list[str] = []
    for tok in tokens:
        if not tok.endswith("/"):
            continue
        if tok.startswith("GppVerify/"):
            dirs.append(tok.rstrip("/"))
        elif dirs and "/" not in tok.rstrip("/"):
            dirs.append("GppVerify/" + tok.rstrip("/"))
        else:
            return []
    return dirs


def sync_readme(text: str, counts: dict[str, int]) -> str:
    """Rewrite the README's module sentence and its Layout-table file counts."""
    text = README_MODULES.sub(
        f"The library holds {counts['modules']:,} Lean modules", text
    )
    lines = []
    for line in text.split("\n"):
        m = README_TABLE_ROW.match(line)
        if m:
            dirs = _layout_row_dirs(m.group(1))
            if dirs:
                total = sum(_lean_files_under(d) for d in dirs)
                line = f"{m.group(1)}{total:,}{m.group(2)}"
        lines.append(line)
    return "\n".join(lines)


def main() -> int:
    check_only = "--check" in sys.argv[1:]
    counts = tree_counts()
    summary = (
        f"{counts['modules']} modules, {counts['stubs']} stubs, {counts['axioms']} axiom(s)"
    )

    # (path, description, rewriter). A missing surface is not an error: the blueprint is a
    # separate build and a checkout without it should still be able to fix the landing page.
    surfaces = [
        (LANDING, "landing page", lambda t: sync_og(sync_stats(t, counts), counts)),
        (REPO / BLUEPRINT, "blueprint", lambda t: sync_blueprint(t, counts)),
        (README, "README", lambda t: sync_readme(t, counts)),
    ]

    stale: list[str] = []
    writes: list[tuple[Path, str]] = []
    for path, what, rewrite in surfaces:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        new = rewrite(text)
        if new != text:
            stale.append(what)
            writes.append((path, new))

    if not stale:
        print(f"Published counts already match the tree ({summary}).")
        return 0

    if check_only:
        print(f"Stale published counts in: {', '.join(stale)}. The tree has {summary}.")
        print("Run without --check to rewrite them.")
        return 1

    for path, new in writes:
        path.write_text(new, encoding="utf-8")
    print(f"Synced the {', '.join(stale)} to the tree ({summary}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
