#!/usr/bin/env python3
"""Gate: every registered named pointer resolves to a declaration in the tree.

Why this exists
---------------
The repo's canon (2026-11-22) is to claim existence by pointing, not by sentence:
where the prose needs to say a result exists, it names the declaration. A sentence
rots silently — PR #672 removed ~816 of them — but a pointer can be *checked*.
`scripts/named_pointers.txt` registers the load-bearing pointers: the explicit
formula declarations whose "not formalized" docstrings started the sweep, the
sparse-cutoff criterion that was its second stale instance, and the names the
README cites for the dictionary and the RH reduction. If one of those names stops
resolving — renamed, moved, deleted — this gate fails in the same change that
breaks it, instead of leaving the README pointing at nothing.

What it checks
--------------
For each registered fully qualified name, the tree must contain a declaration of
that name: a declaration keyword (`theorem`, `lemma`, `def`, …) introducing it,
under a `namespace` stack that composes to the registered prefix. Comments are
stripped first (with `check_stub_naming.strip_comments`, the same stripper the
other gates use), so a name mentioned in a comment does not count — the pointer
must land on a declaration, not on prose about one.

Limits, stated plainly
----------------------
This guards the registered pointers only; it is not a general prose parser, and
a name used in prose but never registered is not checked. The scan is textual:
it tracks `namespace`/`section`/`end` nesting line by line, and it does not see
names produced by metaprogramming, `export` re-exports, or declarations whose
keyword does not start a line. A pointer that resolves only through one of those
mechanisms would need the declaration found by the kernel instead — none of the
registered names is of that kind today.

Exit status: 0 clean, 1 on any unresolved pointer.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_landing_claims import DECL_RE, LEAN_ROOT  # noqa: E402
from check_stub_naming import strip_comments  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
REGISTRY = Path(__file__).resolve().parent / "named_pointers.txt"

NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.']*)")
SECTION_RE = re.compile(r"^\s*section\b(?:\s+([A-Za-z_][\w.']*))?")
END_RE = re.compile(r"^\s*end\b(?:\s+([A-Za-z_][\w.']*))?")


def declared_full_names() -> set[str]:
    """Every declaration name in the tree, composed with its namespace stack."""
    names: set[str] = set()
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        src = strip_comments(path.read_text(encoding="utf-8"))
        lines = src.split("\n")
        # Events in source order: (line, kind, payload). Directives are found per
        # line; declarations by the gate-shared DECL_RE over the whole text, with
        # the match's line recovered by counting newlines, as in
        # check_stub_naming.declarations.
        events: list[tuple[int, int, str, str]] = []
        for idx, line in enumerate(lines):
            if m := NAMESPACE_RE.match(line):
                events.append((idx, 0, "ns", m.group(1)))
            elif m := SECTION_RE.match(line):
                events.append((idx, 0, "section", m.group(1) or ""))
            elif m := END_RE.match(line):
                events.append((idx, 0, "end", m.group(1) or ""))
        for m in DECL_RE.finditer(src):
            lineno = src.count("\n", 0, m.start())
            events.append((lineno, 1, "decl", m.group("name")))
        events.sort(key=lambda e: (e[0], e[1]))

        stack: list[tuple[str, str]] = []  # (kind, dotted name) frames
        for _line, _ord, kind, payload in events:
            if kind == "ns":
                stack.append(("ns", payload))
            elif kind == "section":
                stack.append(("section", payload))
            elif kind == "end":
                if not payload:
                    if stack:
                        stack.pop()
                else:
                    # Pop frames until the named frame is closed.
                    for j in range(len(stack) - 1, -1, -1):
                        if stack[j][1] == payload or stack[j][1].endswith("." + payload):
                            del stack[j:]
                            break
            else:  # decl
                prefix = ".".join(name for k, name in stack if k == "ns" and name)
                short = payload.split(".")[-1]
                if "." in payload:
                    names.add(payload)
                if prefix:
                    names.add(f"{prefix}.{short}")
                names.add(short)
    return names


def load_registry() -> list[str]:
    pointers = []
    for raw in REGISTRY.read_text(encoding="utf-8").split("\n"):
        line = raw.strip()
        if line and not line.startswith("#"):
            pointers.append(line)
    return pointers


def main() -> int:
    pointers = load_registry()
    names = declared_full_names()
    missing = [p for p in pointers if p not in names]
    if missing:
        print(f"Unresolved named pointer(s): {len(missing)} of {len(pointers)} registered.")
        print("A registered name no longer resolves to a declaration in the tree.")
        print("Fix the pointer (named_pointers.txt) or restore the declaration —")
        print("do not leave prose pointing at a name that is not there.")
        for p in missing:
            print(f"  {p}")
        return 1
    print(f"All {len(pointers)} registered named pointers resolve to declarations in the tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
