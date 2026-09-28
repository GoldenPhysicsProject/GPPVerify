#!/usr/bin/env python3
"""Assemble the site served at lean.goldenphysics.org.

Layout:
  /                 index.html, the plain-language landing page (gated by check_landing_claims.py)
  /status.json      live counts from the Lean tree (landing_status.py)
  /blueprint/...    the leanblueprint output (blueprint/src/web)
  /<page>.html      redirect stubs for every blueprint page that used to live at the root,
                    so links from before the move (sect0003.html, dep_graph_document.html, ...)
                    keep working

Usage: python3 scripts/assemble_site.py OUTDIR
"""

from __future__ import annotations

import html
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
WEB = REPO / "blueprint" / "src" / "web"

STUB = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>Moved to the blueprint</title>
<link rel="canonical" href="/blueprint/{page}">
<meta http-equiv="refresh" content="0; url=/blueprint/{page}">
<script>location.replace('/blueprint/{page}' + location.hash);</script>
</head><body style="background:#050505;color:#e4e1d8;font-family:sans-serif">
<p>This page moved to <a style="color:#d4af37" href="/blueprint/{page}">/blueprint/{page}</a>.</p>
</body></html>
"""


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    out = Path(sys.argv[1])
    if not WEB.is_dir():
        print(f"blueprint output not found at {WEB}; run `leanblueprint web` first")
        return 1
    if out.exists():
        shutil.rmtree(out)
    shutil.copytree(WEB, out / "blueprint")
    (out / "blueprint" / "CNAME").unlink(missing_ok=True)
    shutil.copy2(REPO / "index.html", out / "index.html")
    subprocess.run([sys.executable, str(REPO / "scripts" / "landing_status.py"),
                    str(out / "status.json")], check=True)
    stubs = 0
    for page in sorted(WEB.glob("*.html")):
        if page.name == "index.html":
            continue
        (out / page.name).write_text(STUB.format(page=html.escape(page.name)), encoding="utf-8")
        stubs += 1
    (out / "CNAME").write_text("lean.goldenphysics.org\n", encoding="utf-8")
    print(f"assembled {out}: landing page, blueprint/, status.json, {stubs} redirect stubs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
