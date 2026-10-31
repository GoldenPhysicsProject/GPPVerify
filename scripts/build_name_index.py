#!/usr/bin/env python3
"""Generate the name-to-module index of declarations (canonization rule 5).

Rule 5 of the canonization protocol (GPP-bridge, adopted 2026-10-31): one generated
map that every seat reads before any audit, so that an audit never again runs on a
partial view of the tree and "does module X exist / where does Y live" stops being a
grep session. This script is that map. It also makes rule 3 (search before build)
mechanical: the aliases a builder must search are enumerable from one file.

## Parsing

The declarations come from the project's own machinery, not a fresh parser:
`DECL_RE` is imported from `check_landing_claims.py` (the same pattern the landing
gate uses) and applied to comment-stripped source (`strip_comments`, imported from
`check_stub_naming.py`). Fully qualified names are reconstructed with a scope
stack: `namespace` pushes a name component, `section` pushes a marker that does not
affect names, and a column-0 `end` pops. What the index records is therefore the
name Lean itself would resolve inside the file, for the constructs `DECL_RE`
recognises. It does not resolve `open` aliases, and an anonymous `instance` (no
name to index) is skipped.

## Use

    python3 scripts/build_name_index.py           # (re)generate docs/NAME_INDEX.md
    python3 scripts/build_name_index.py --check   # fail if the committed index is stale

`--check` regenerates the index using the tree-head SHA recorded in the committed
file (so the header is stable across the commit that carries the index) and
compares byte for byte; only the declaration rows can make it fail.
"""

import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_landing_claims import DECL_RE  # noqa: E402
from check_stub_naming import strip_comments  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO / "GppVerify"
INDEX = REPO / "docs" / "NAME_INDEX.md"

NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][\w.]*)")
SECTION = re.compile(r"^section\b")
END = re.compile(r"^end\b")
KIND = re.compile(r"\b(theorem|lemma|def|abbrev|axiom|structure|inductive|instance|class|opaque)\b")
SHA_LINE = re.compile(r"^Tree head: `([^`]+)`", re.M)


def head_sha() -> str:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO,
            capture_output=True,
            text=True,
            check=True,
        )
        return out.stdout.strip()
    except Exception:
        return "unknown"


def collect_entries() -> list[tuple[str, str, str]]:
    """(fully qualified name, kind, repo-relative module) for every declaration."""
    entries: list[tuple[str, str, str]] = []
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        rel = str(path.relative_to(REPO))
        src = strip_comments(path.read_text(encoding="utf-8"))
        scopes: list[tuple[str, str]] = []  # ("ns", name) | ("section", "")
        for line in src.splitlines():
            ns = NAMESPACE.match(line)
            if ns:
                scopes.append(("ns", ns.group(1)))
                continue
            if SECTION.match(line):
                scopes.append(("section", ""))
                continue
            if END.match(line):
                if scopes:
                    scopes.pop()
                continue
            m = DECL_RE.match(line)
            if not m:
                continue
            name = m.group("name")
            if name == ":":
                continue  # anonymous instance: nothing to index
            kind = KIND.search(m.group(0))
            prefix = ".".join(part for tag, part in scopes if tag == "ns" and part)
            full = f"{prefix}.{name}" if prefix else name
            entries.append((full, kind.group(1) if kind else "", rel))
    entries.sort(key=lambda e: (e[0], e[2], e[1]))
    return entries


def render(entries: list[tuple[str, str, str]], sha: str) -> str:
    lines = [
        "# Name index",
        "",
        "GENERATED FILE -- do not edit by hand. Regenerate with:",
        "",
        "    python3 scripts/build_name_index.py",
        "",
        "Verify freshness with `python3 scripts/build_name_index.py --check`.",
        "",
        f"Tree head: `{sha}`",
        f"Declarations indexed: {len(entries)}",
        "",
        "One row per declaration recognised by the project's own declaration pattern",
        "(`DECL_RE` in `scripts/check_landing_claims.py`, over comment-stripped source).",
        "Names are fully qualified by the enclosing `namespace`s; the module is the",
        "repo-relative Lean file. Canonization rule 5: read this map before any audit,",
        "and search it (under every alias) before formalizing a new object.",
        "",
        "| Name | Kind | Module |",
        "| --- | --- | --- |",
    ]
    for name, kind, rel in entries:
        lines.append(f"| `{name}` | {kind} | `{rel}` |")
    return "\n".join(lines) + "\n"


def main() -> int:
    entries = collect_entries()
    if "--check" in sys.argv:
        if not INDEX.exists():
            print(f"::error::{INDEX.relative_to(REPO)} does not exist. Generate it.")
            return 1
        committed = INDEX.read_text(encoding="utf-8")
        m = SHA_LINE.search(committed)
        sha = m.group(1) if m else "unknown"
        fresh = render(entries, sha)
        if fresh != committed:
            diff = [
                (i + 1, a, b)
                for i, (a, b) in enumerate(
                    zip(committed.splitlines(), fresh.splitlines())
                )
                if a != b
            ]
            print(
                f"::error::{INDEX.relative_to(REPO)} is stale: the tree's declarations "
                f"no longer match it ({len(diff)} differing line(s) in the common "
                "prefix). Regenerate with `python3 scripts/build_name_index.py`."
            )
            for lineno, old, new in diff[:5]:
                print(f"  line {lineno}: committed {old!r} != fresh {new!r}")
            return 1
        print(
            f"Name index is fresh: {len(entries)} declarations, "
            f"generated at tree head {sha}."
        )
        return 0

    sha = head_sha()
    INDEX.write_text(render(entries, sha), encoding="utf-8")
    print(
        f"Wrote {INDEX.relative_to(REPO)}: {len(entries)} declarations indexed "
        f"at tree head {sha}."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
