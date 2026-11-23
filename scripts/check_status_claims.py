#!/usr/bin/env python3
"""Gate: no stale status claims in comments, docstrings or notes.

Why this exists
---------------
On 2026-11-22 a seat read a docstring asserting that the Weil explicit formula "is not
formalized" and trusted the sentence over the tree. The formula *is* formalized
(`GppExplicitFormulaAssembly.explicit_formula_even`, `explicit_formula_zeroSum`), and had
been for some time; the sentence was a true-when-written scope note that the tree had
quietly falsified, and nothing in the repo ever re-read it. PR #672 swept the tree and
removed ~816 such sentences across 531 files — every free-text assertion of the form
"X is not formalized / not proved / not claimed / remains open" that a reader could
mistake for the current state of the tree.

A sweep is a one-time cleanup. This gate is what makes it permanent: the pattern family
the sweep hunted is now un-writable. A new disclaimer of that family, in a Lean comment
or docstring or in any Markdown file, fails the build at the moment it is written,
while the sentence is still cheap to fix — instead of months later, in front of a
reader who trusts it.

What it checks
--------------
Every `.lean` file's comments and docstrings, and every `.md` file's text, is scanned
for the disclaimer pattern family:

    not (yet) formalized/proved/proven · unformalized · does not prove ·
    do not prove/claim · no claim · not claimed · nothing here proves ·
    remains open · open problem · placeholder · to be formalized · not established

Code is not scanned — only comment text in `.lean` files. (String literals are tracked
so a `--` inside a string is not mistaken for a comment start.)

The allowlist
-------------
Some lines in that family are not disclaimers; they are the repo's records, and PR #672
adjudicated them as keeps: the OPEN registries and `open_` stub records, the
THEOREM/LEAN/OPEN/KILLED label lines, hypothesis statements naming what a proved result
takes, the proved-false ledger, correction and retirement records, definitional and
framework-claim guards, and dated historical notes (which are kept as written —
editing a dated record to match today's tree would falsify the record). Each is exempted
by an entry in `scripts/status_claims_allowlist.txt`:

    PATH :: LINE-REGEX :: REASON

`PATH` is a repo-relative path or glob; `LINE-REGEX` is a Python regex the hit line
must match (`*` exempts every hit in the file — used only where the whole file is one
record of the stated kind); `REASON` is required and says which adjudicated class the
line belongs to. An exemption without a reason does not parse. New disclaimers do not
get allowlist entries; they get rewritten to state what is proved and name the
hypotheses it takes.

Exit status: 0 clean, 1 on any non-allowlisted hit (each printed as file:line).
"""

from __future__ import annotations

import fnmatch
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
ALLOWLIST = Path(__file__).resolve().parent / "status_claims_allowlist.txt"

PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("not-formalized/proved", re.compile(r"\bnot\s+(?:yet\s+)?(?:formali[sz]ed|proved|proven)\b", re.I)),
    ("unformalized", re.compile(r"\bunformali[sz]ed\b", re.I)),
    ("does-not-prove", re.compile(r"\bdoes\s+not\s+prove\b", re.I)),
    ("do-not-prove/claim", re.compile(r"\bdo\s+not\s+(?:prove|claim)\b", re.I)),
    ("no-claim", re.compile(r"\bno\s+claim\b", re.I)),
    ("not-claimed", re.compile(r"\bnot\s+claimed\b", re.I)),
    ("nothing-here-proves", re.compile(r"\bnothing\s+here\s+proves\b", re.I)),
    ("remains-open", re.compile(r"\bremains?\s+open\b", re.I)),
    ("open-problem", re.compile(r"\bopen\s+problem\b", re.I)),
    ("placeholder", re.compile(r"\bplaceholder\b", re.I)),
    ("to-be-formalized", re.compile(r"\b(?:still\s+|yet\s+)?to\s+be\s+formali[sz]ed\b", re.I)),
    ("not-established", re.compile(r"\bnot\s+(?:yet\s+)?established\b", re.I)),
]


def lean_comment_lines(src: str):
    """Yield (line_number, text) for each line of comment text in a Lean source.

    Handles `--` line comments and nested `/- … -/` block comments (which include
    `/--` and `/-!` doc comments). String literals are tracked so comment markers
    inside a string are not mistaken for comments. This is the inverse of
    `check_stub_naming.strip_comments`, written separately because that function
    discards the comment text this gate exists to read.
    """
    i, n = 0, len(src)
    depth = 0
    in_str = False
    lineno = 1
    buf: list[str] = []
    buf_line = 1

    def flush():
        if buf:
            text = "".join(buf)
            for k, part in enumerate(text.split("\n")):
                yield (buf_line + k, part)
            buf.clear()

    while i < n:
        c = src[i]
        if c == "\n":
            lineno += 1
            if depth:
                buf.append(c)
            i += 1
            continue
        if depth:
            if src.startswith("/-", i):
                depth += 1
                buf.append("/-")
                i += 2
                continue
            if src.startswith("-/", i):
                depth -= 1
                buf.append("-/")
                i += 2
                if depth == 0:
                    yield from flush()
                continue
            buf.append(c)
            i += 1
            continue
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                j = n
            yield (lineno, src[i:j])
            i = j
            continue
        if src.startswith("/-", i):
            depth = 1
            buf = ["/-"]
            buf_line = lineno
            i += 2
            continue
        i += 1
    yield from flush()


def load_allowlist() -> list[tuple[str, re.Pattern[str] | None, str]]:
    """Parse the allowlist. A malformed entry is a hard error, not a silent skip:
    an exemption that does not parse must never quietly become a whole-file pass."""
    entries: list[tuple[str, re.Pattern[str] | None, str]] = []
    for raw in ALLOWLIST.read_text(encoding="utf-8").split("\n"):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = [p.strip() for p in line.split("::")]
        if len(parts) != 3 or not parts[0] or not parts[2]:
            raise SystemExit(f"Malformed allowlist entry (want PATH :: REGEX :: REASON): {raw!r}")
        path, regex, reason = parts
        entries.append((path, None if regex == "*" else re.compile(regex, re.I), reason))
    return entries


def allowlisted(entries, rel: str, text: str) -> bool:
    for path, regex, _reason in entries:
        if fnmatch.fnmatch(rel, path) and (regex is None or regex.search(text)):
            return True
    return False


def scan_files():
    for path in sorted(REPO.rglob("*")):
        parts = path.relative_to(REPO).parts
        if ".git" in parts or ".lake" in parts or not path.is_file():
            continue
        if path.suffix in (".lean", ".md"):
            yield path


def main() -> int:
    entries = load_allowlist()
    failures: list[str] = []
    exempt = 0
    for path in scan_files():
        rel = str(path.relative_to(REPO))
        src = path.read_text(encoding="utf-8")
        lines = lean_comment_lines(src) if path.suffix == ".lean" else enumerate(src.split("\n"), 1)
        for lineno, text in lines:
            for name, pat in PATTERNS:
                if pat.search(text):
                    if allowlisted(entries, rel, text):
                        exempt += 1
                    else:
                        failures.append(f"{rel}:{lineno}: [{name}] {text.strip()[:140]}")
                    break
    if failures:
        print(f"Stale status claims: {len(failures)} non-allowlisted hit(s).")
        print("Canon: state what is proved and name the hypotheses it takes; no disclaimers.")
        print("If a hit is one of the adjudicated record classes, exempt it in")
        print("scripts/status_claims_allowlist.txt with its reason — do not weaken the patterns.")
        for f in failures:
            print(f"  {f}")
        return 1
    print(f"No stale status claims. ({exempt} allowlisted record line(s) exempted.)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
