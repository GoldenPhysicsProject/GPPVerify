# Which Way Is Forward? — source and exact core

Daniel Toupin, *Which Way Is Forward? Orientation, Matter, Mass, and the Two-Lift Structure of
Relativistic Physics*, v26, 22 September 2026.

| File | What it is |
|---|---|
| `Which_Way_Is_Forward_v26.tex` | The paper. Latest of v4–v26 in Drive (`GPP/Newer rh physics stuff`). |
| `gppaudit.sty` | House style the paper loads. |
| `verify_which_way_is_forward.py` | The paper's own check script (standard library only). All nine checks pass. |

**Provenance.** Both `.tex` and `.sty` were rebuilt from Google Drive's text export, which
escapes Markdown-special characters. They were unescaped mechanically. The rebuilt `.tex` has
balanced environments and braces, but it has not been compiled here because this container has
no TeX installation. If it disagrees with the PDF in Drive, the PDF is authoritative. The
`.py` was transcribed from the same kind of export, and it runs green, which checks the
transcription.

## What is formalized

`GppVerify/StandardModel/OrientationCliffordCore.lean` proves, by kernel `decide` over `ℤ[i]`,
the paper's explicit finite core:

- the Cl(2,2) carrier;
- the orientation algebra;
- the unitary four-lift intertwiner;
- the order-16 carrier group with center {±1, ±χ};
- Fix(D) = {(a, b, b, a)} and the agreement of the two half flips on it;
- the Cl(3,1) realization.

Not yet formalized:

- the coordinate-blade signature scan;
- the Spin(6,2)/Spin(10,2) B B̄ signs;
- the determinant cover.

## The paper's Lean inventory

Appendix "Lean verification inventory" lists 34 modules. As of 2026-09-26, 33 of them exist
only on `codex/orientation-mass-time-formalization` (Codex's draft PR #173), which is not merged.
A clean local build of that branch fails in 69 modules. Of the 34 listed:

- 9 build: 8 on that branch, plus `TauDifferential`, which is on `main`;
- 14 fail on their own errors;
- 11 are blocked by a failed dependency.

The paper's sentence "the companion formalizations cover …" is not yet true of `main`.
