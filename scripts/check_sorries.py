#!/usr/bin/env python3
"""Fail the build if any Lean source in `GppVerify/` contains a live `sorry`.

## Why this exists — the gate it replaces was blinded by the build cache

`build.yml` has gated on `sorry` since the beginning, and it gated on the right thing:
Lean's own `declaration uses 'sorry'` diagnostic rather than a grep of the source. Its
reasoning was sound — grepping source false-positives on every doc comment discussing a
gap (this repo has ~17 such lines) and false-negatives on sorries a tactic introduces.

But it read that diagnostic out of `lake build` output, under this assumption, stated in
its own comment:

    # `lake` replays warnings for cached modules, so this is reliable on a
    # fully-cached build.

**That is false.** A module Lake replays from cache emits no diagnostic at all:

    $ lake build GppVerify.RiemannHypothesis.SechFourthIntegral | grep -c "uses 'sorry'"
    0        # ... on a module that does contain one

So the gate reported "OK — no declaration uses 'sorry'" precisely when the cache was warm,
which on CI is almost always. On 2026-08-31 a `sorry` in
`hasDerivAt_sechFourthAntideriv` rode into `main` through PR #133 — whose title was
"Mathlib 4.19.0 → 4.33.1: the whole tree builds clean" — and sat there through four
further merges and several status reports quoting "0 sorries", because every one of those
runs was cached. It was found by accident, from a stray warning in a local build that
happened to recompile that module.

The lesson generalises past this repo: **a gate that reads build output inherits the build
cache's blind spots.** Any check that must hold for the whole tree should read the tree.

## What this checks

Source-level, so no cache can hide it: strip comments and string literals, then look for
`sorry`/`sorryAx` as a whole token. That deliberately re-introduces the original concern
about doc comments — and answers it by actually removing the comments first, using the
same `strip_comments` helper the stub gate uses, rather than by avoiding source-reading.

This does NOT replace the build-log check or the axiom audit; all three run:

* this script catches a literal `sorry` regardless of cache state;
* the build-log check catches tactic-introduced sorries when the module is recompiled;
* `check_axioms.lean` catches `sorryAx` reaching a flagship theorem through any route.

Each has a blind spot the others cover. Quote all of sorry / axiom / stub counts in any
status claim about this tree — see `docs/FORMALIZATION_PLAN.md`.

## Reading the three together: `sorryAx` without a source `sorry`

Codex hit this on 2026-09-01 and recorded it in `gpp-bridge/CODEX_RESEARCH_NOTES.md`:
**a module that fails to elaborate emits `sorryAx`.** Lean fills the hole left by a failed
proof with the same axiom a literal `sorry` produces, so the axiom audit can report `sorryAx`
while this script correctly reports zero — no `sorry` was ever written.

So when the two disagree, the disagreement is itself the diagnosis:

| this script | axiom audit | means |
|---|---|---|
| clean | clean | genuinely clean |
| **finds one** | `sorryAx` | a real `sorry` was committed |
| **clean** | `sorryAx` | **a module failed to build** — fix the build error, do not hunt for a `sorry` |

Do not "reconcile" the two by weakening either. The third row is the useful one: it points
at a compile failure that a green root build may be hiding, which is exactly what
`check_import_graph.py` guards against from the other direction.
"""

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_stub_naming import strip_comments  # noqa: E402

# Whole-token match, so `sorryAx`, `sorry_foo` and `Real.sorry` are handled sensibly:
# the first two are caught (a live sorry and a name containing one is worth a look), a
# member access is not a bare token so it is not.
SORRY = re.compile(r"(?<![A-Za-z0-9_.])sorry(?:Ax)?(?![A-Za-z0-9_'])")

# String literals can legitimately contain the word (error messages, test fixtures).
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    root = repo / "GppVerify"
    hits: list[str] = []

    for path in sorted(root.rglob("*.lean")):
        src = strip_comments(path.read_text())
        # Blank string literals but keep line structure so line numbers stay right.
        src = STRING.sub(lambda m: " " * len(m.group(0)), src)
        for lineno, line in enumerate(src.splitlines(), start=1):
            if SORRY.search(line):
                rel = path.relative_to(repo)
                hits.append(f"{rel}:{lineno}: {line.strip()[:100]}")

    if hits:
        print(f"::error::{len(hits)} live `sorry` token(s) in GppVerify/.")
        print("Standing rule: no sorry is ever committed. Park an open result as an")
        print("`open_… : True := trivial` stub instead — it is counted and it is honest.")
        for h in hits:
            print(f"  {h}")
        return 1

    print("No `sorry` tokens in GppVerify/ (source-level check, cache-independent).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
