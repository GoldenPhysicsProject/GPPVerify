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

The appendix "Lean verification inventory" lists 34 modules.

**Before 2026-09-26:** only `TauDifferential` was on `main`. The other 33 lived only on
`codex/orientation-mass-time-formalization` (Codex's draft PR #173). A clean build of that
branch failed in 69 modules. Of the paper's 34, 9 built, 14 failed on their own errors, and 11
were blocked by a failed dependency.

**Now:** all 34 are on `main` and build. The 33 missing modules were ported from Codex's
branch at head `780de22`, along with the 15 further modules they import, and
`GrassmannianJacobian` gained Codex's split-complement Jacobian.

The statements are Codex's. What changed:

- Proofs were repaired to compile under Lean 4.33.1 / current Mathlib. The fixes were mostly
  mechanical: missing `noncomputable`, `open Matrix`, `λ` used as an identifier, `rfl` on real
  negation, and stale `ring` calls.
- A few proofs were rewritten outright:
  - the double-complement involutions, using an explicit `D`;
  - the Klein reflection, using bilinearity;
  - the Jordan-block eigenvalue lemma.
- One real logic error was fixed: `bool_odd_map_id_or_not` had its two cases swapped.
- Two hypotheses no proof used were dropped:
  - `hD` in `row_reduced_annihilator_is_complement`;
  - `hinv` in `two_penrose_representations_same_bulk`.
- Two docstrings contained `+/-`. In Lean, `/-` opens a nested comment, so each became `±`.

Every ported file also compiles with `autoImplicit` off. No statement silently generalized over
a misspelled type.

The rest of Codex's branch is not ported and remains hers. That is 229 further changed Lean files, many
of which still fail to build there.
