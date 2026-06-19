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
  → functional equation ξ(s) = ξ(1-s)  [FunctionalEquation.lean — scaffolded]
  → Peter-Weyl discrete spectrum        [HaarMeasure.lean — scaffolded]
  → L² constraint forces Re(s) = ½     [RHSpectralMultiplicity.lean — improved]
  → Riemann Hypothesis
```

**New addition (Hack #2):** `GppVerify/GrassmannianMass.lean`
- Core statement of Grassmannian Jacobian Mass Theorem
- massParameter = |det(A)| as Plücker p23
- mean |Jacobian eigenvalue| = 1 / |det| exactly (numerical correlation 1.0)
- Massless locus |det|=1 → J^{2} = -I (complex structure)
- Zitterbewegung as discrete chart oscillation under inversion
- Direct geometric origin of mass + link to numerical Python verification

---

## File status

| File | Sorries | Axioms | Status |
|------|---------|--------|--------|
| `GppVerify/HaarSelfDuality.lean` | 0 | 0 | **CLEAN** |
| `GppVerify/CoreTheorems.lean` | 0 | 1 (standard) | Clean |
| `GppVerify/RHSpectralMultiplicity.lean` | 2 | 1 | Improved (placeholders documented + Grassmannian link) |
| `GppVerify/GrassmannianMass.lean` | 2 | 2 | **NEW** (core statements + numerical tie-in) |
| `GppVerify/RiemannHypothesis/HaarMeasure.lean` | 3 | 0 | Scaffolded (adelic compactness) |
| `GppVerify/RiemannHypothesis/FunctionalEquation.lean` | 3 | 0 | Scaffolded |
| `GppVerify/RiemannHypothesis/ShadowSymmetry.lean` | 2 | 0 | Scaffolded |

---

## Open problem: `thm:link6`

The theorem **`thm:link6`** (`c_{2D} = c_{4D}^{Weyl}`, ONON52 §Link 6) is explicitly open.
All Lean declarations that depend on it are marked `sorry`.

Do **not** close these sorries without a proof of Link 6.

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

**Machine status:** Multiple hacks executed. Haar self-duality proved. Multiplicity path strengthened. Grassmannian mass theorem scaffolded with numerical evidence. Continuing to close gaps toward unconditional RH.
