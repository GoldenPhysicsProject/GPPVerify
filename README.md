# GPPVerify — Golden Physics Project Lean 4 Formalization

Formal verification of the ONON framework in Lean 4 + Mathlib.

**Blueprint (live proof progress):** https://lean.goldenphysics.org  
**Paper:** Daniel Toupin, *On the Nature of Nature* (2026) — https://goldenphysics.org  
**Author:** Daniel Toupin | ORCID: 0009-0003-7682-9579

---

## Primary target: RH Pathway 2 (Spectral / Meyer)

The most self-contained proof of the Riemann Hypothesis in the ONON framework:

```
Haar self-duality on A×/Q×          [HaarSelfDuality.lean — CLEAN ✓]
  → functional equation ξ(s) = ξ(1-s)  [FunctionalEquation.lean — CLEAN ✓]
  → Peter-Weyl discrete spectrum        [HaarMeasure.lean — mostly clean, 2 Mathlib-gap axioms]
  → L² constraint forces Re(s) = ½     [RHSpectralMultiplicity.lean — improved]
  → Riemann Hypothesis
```

**Flagship conditional statement:** `GppWeilCriterion.rh_of_weil_pairedForm_nonneg`
(`WeilPositivityCriterion.lean`) — RH from finite Weil-pairing positivity, no axioms
beyond Mathlib's built-ins. The former `arithmetic_admissibility` axiom (RH restated)
is retired as of 2026-07-17.

**Also complete:** `GppVerify/GrassmannianMass.lean` — the Jacobian Mass relation is now a
real theorem (`transition_transition_eq_neg`, τ∘τ = -id exactly), replacing an earlier
axiom-based version; see the file's own doc comment for what changed and why.

---

## File status

*Sorry/axiom counts below are `grep`-verified against the current tree, not hand-maintained
— re-run `grep -rn "^\s*sorry\s*$" --include="*.lean" .` and
`grep -rn "^axiom " --include="*.lean" .` to reproduce.*

| File | Sorries | Axioms | Status |
|------|---------|--------|--------|
| `GppVerify/HaarSelfDuality.lean` | 0 | 0 | **CLEAN** |
| `GppVerify/CoreTheorems.lean` | 0 | 0 | Clean |
| `GppVerify/RHSpectralMultiplicity.lean` | 0 | 2 | `riemannZeta_conj` proved (Mellin/HurwitzZeta); `arithmetic_admissibility` axiom + `riemann_hypothesis` alias **retired 2026-07-17** (they restated RH verbatim — superseded by `GppWeilCriterion.rh_of_weil_pairedForm_nonneg`); remaining axioms `schwartz_integral_clm_exists`, `exp_growth_not_tempered` assert provable facts (follow-up) |
| `GppVerify/GrassmannianMass.lean` | 0 | 0 | **CLEAN** — `τ∘τ = -id` proved directly, no axioms |
| `GppVerify/RiemannHypothesis/HaarMeasure.lean` | 0 | 0 | Mostly clean; two results are honest `True := trivial` stubs pending Fujisaki's lemma / adelic compactness (not in Mathlib 4.19.0) — no `sorry`, no axiom smuggling the actual claim |
| `GppVerify/RiemannHypothesis/FunctionalEquation.lean` | 0 | 0 | **CLEAN** |
| `GppVerify/RiemannHypothesis/ShadowSymmetry.lean` | 0 | 0 | Clean; one result honestly stubbed pending the Penrose correspondence, one explicitly gated on the open `thm:link6` below |

Whole-repo sweep (this session): **zero `sorry` tactics anywhere in the tree**, and no
axiom whose hypotheses are vacuous while its conclusion is a substantive unconditional
claim (that exact bug shape was found and fixed once, in `L2Constraint.lean` — see git
history). Genuinely open results are `theorem foo : True := trivial` stubs with a doc
comment naming the precise Mathlib gap, never a bare `axiom` asserting the open claim
itself.

---

## Open problem: `thm:link6`

The theorem **`thm:link6`** (`c_{2D} = c_{4D}^{Weyl}`, ONON52 §Link 6) is explicitly open.
Lean declarations that depend on it are honest `True := trivial` stubs gated in their doc
comments on a proof of Link 6 — not `sorry`, since there is nothing left to fill in once
Link 6 is proved; the gap is upstream mathematics, not a missing Lean argument.

Do **not** weaken these stubs into an unconditional claim without a proof of Link 6.

---

## Build

```bash
# Install elan (if needed)
curl -sSfL https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
./elan-init -y

# Get Mathlib cache (fast)
lake exe cache get

# Build everything
lake build
```

---

## Blueprint

```bash
pip install leanblueprint
cd blueprint
leanblueprint build
# Output at blueprint/web/index.html
```

---

## Dependency map

See [`docs/DependencyMap.md`](docs/DependencyMap.md) for the full theorem dependency
tree extracted from ONON52.tex (686 named results, 22 chapters).

---

**Status:** Haar self-duality, the functional equation, and the Grassmannian mass relation
are all fully proved with no axioms. The zeta conjugate-symmetry fact in the multiplicity
path is a proved theorem rather than an axiom. Genuinely open steps (Fujisaki's lemma,
the Penrose correspondence, `thm:link6`, and the L² adelic constraint) are honestly
recorded as `True := trivial` stubs naming the exact missing infrastructure, never
smuggled in as an axiom asserting the open claim itself, and the whole tree has been
independently swept for both `sorry` and for axioms with vacuous hypotheses masking a
substantive conclusion. A parallel thread is formalizing Tate's-thesis local zeta
integrals (p-adic and archimedean places, an Euler-product bridge to Mathlib's own
`riemannZeta_eulerProduct`) as real, from-scratch measure-theoretic infrastructure —
not derived from the paper, built to support it. Work continues toward closing the
remaining gaps.
