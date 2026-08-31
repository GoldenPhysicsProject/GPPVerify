> **Update 2026-07-17:** the `arithmetic_admissibility` axiom and the
> `GppRH.riemann_hypothesis` alias referenced below are **retired**. The flagship
> conditional is now `GppWeilCriterion.rh_of_weil_pairedForm_nonneg`
> (`WeilPositivityCriterion.lean`). Mentions below are historical.

# ONON52 — Lean 4 Formalization Dependency Map
## Golden Physics Project | GPPVerify

**Source:** `ONON52.tex` — Daniel Toupin, *On the Nature of Nature* (2026)  
**Generated:** 2026-06-03  
**Status:** Pre-formalization survey — awaiting Daniel's confirmation before writing .lean files

---

## 1. BOOK STRUCTURE

22 chapters + appendices. 686 named results (theorems, lemmas, definitions, conjectures, propositions).  
527 `\label`-tagged results. 393 theorems/lemmas/conjectures with names.

| Chapter | Label | Key Contents |
|---------|-------|-------------|
| Prologue + Ch 1 | `chap:introduction` | Shadow=T identification, Δ=2s, central claim |
| Ch 2 | `chap:haar-intro` | Conceptual Haar measure intro |
| Ch 3 | *(background)* | Measure theory, spectral theory, diff geometry toolkit |
| Ch 4 | `chap:quantum-foundations` | Born rule, measurement, decoherence from Haar |
| Ch 5 | `chap:twistor-grassmannian` | Penrose twistor, Gr(2,4), Plücker embedding |
| Ch 6 | `chap:celestial` | Celestial holography, shadow discontinuity, c=0 |
| Ch 7 | `chap:einstein` | Einstein equations as Ward identities |
| Ch 8 | `chap:isomorphism-rh` | Canonical dictionary Δ=2s (5 proofs), Hasse-Weil |
| Ch 9 | `chap:rh` | Five RH pathways (main target) |
| Ch 10 | `chap:bsd` | BSD for analytic rank ≤1, parity conjecture |
| Ch 11 | `chap:wightman` | Wightman axioms from Peter-Weyl |
| Ch 12 | `chap:yang-mills` | Yang-Mills mass gap |
| Ch 13 | `chap:decoding-reality` | Arithmetic: constants, CP, quark masses |
| Ch 14 | `chap:cpt-cosmology` | T-symmetric cosmology |
| Ch 15 | `chap:standard-model` | SM gauge group, 3 generations, Weinberg angle |
| Ch 16 | `chap:grassmannian-spinor` | Spinor bundle, chirality, dark matter |
| Ch 17 | `chap:dark-matter` | DM density profile from shadow kernel |
| Ch 18-22 | discussion, predictions, falsification, philosophy, conclusion | |

---

## 2. MOST-CITED RESULTS (cross-reference counts)

These are the load-bearing theorems — formalize these first.

| Rank | Label | Name | Citations |
|------|-------|------|-----------|
| 1 | `thm:shadow-cpt` | Shadow symmetry = time reversal T | 16× |
| 2 | `lem:adelic-l2-regularization` | L² regularization for adelic integrals | 14× |
| 3 | `thm:dm-abundance` | Dark matter abundance | 13× |
| 4 | `cor:three-generations-anomaly` | Exactly 3 generations from c=0 | 12× |
| 5 | `thm:l2-constraint` | L² constraint forces Re(s)=½ | 12× |
| 6 | `lem:born-rule-haar` | Born rule from Haar uniqueness | 11× |
| 7 | `thm:link6` | Link 6: c₂D = c₄D^Weyl | 10× |
| 8 | `thm:shadow-discontinuity` | Shadow discontinuity = loop amplitude | 10× |
| 9 | `thm:rigidity` | Einstein gravity uniqueness | 10× |
| 10 | `thm:spectral-weil` | Spectral-Weil correspondence | 10× |
| 11 | `thm:plancherel-spinj` | Plancherel for spin-j | 9× |
| 12 | `thm:rg-mass-gap-onon` | Mass gap for all g²>0 via RG | 8× |
| 13 | `conj:spectral-transfer-onon` | Spectral Transfer Conjecture | 8× |
| 14 | `thm:canonical-dict` | Canonical dictionary Δ=2s | 8× |
| 15 | `thm:k-factorization` | K-factorization for celestial OPE | 7× |

---

## 3. THE FIVE RH PATHWAYS

All five use the same root: **self-dual Haar measure on locally compact groups**.

### Pathway 1 — Geometric (Section `sec:pathway1-geometric`)
**Claim:** L² constraint from Haar self-duality + functional equation + Peter-Weyl is overdetermined with unique solution σ=½.

**Key lemmas in order:**
1. `lem:haar-self-duality` (L 16374) — Haar measure on A×/Q× is self-dual: d×(a⁻¹) = d×a
2. `thm:functional-equation-adelic` (L 16391) — ξ(s)=ξ(1-s) follows from Haar self-duality
3. `thm:peter-weyl-compact` (L 16592) — Peter-Weyl gives discrete spectrum on compact quotient
4. `thm:l2-constraint` (L 16806) — the three constraints together force Re(s)=½
5. `lem:invariant-mean-cesaro` (8×) — Cesàro regularization via amenability theory
6. `lem:quotient-structure` (L 16887) — A×/Q× quotient structure

**Gap:** Cesàro regularization step (amenability of the idèle class group) is not yet in Mathlib.  
**Lean status:** `lem:haar-self-duality` proved in `HaarSelfDuality.lean` (zero sorries).

---

### Pathway 2 — Spectral / Meyer (Section `sec:pathway2-spectral`)
**Claim:** Meyer (Duke Math J 2005) constructs unconditional spectral realization. Stone's theorem + Haar self-duality forces Re(s)=½.

**Key lemmas in order:**
1. `lem:haar-self-duality` — same as Pathway 1
2. `thm:stone` (L 2799) — Stone's theorem (in Mathlib: `MeasureTheory.Measure.Haar`)
3. `thm:meyer-precise` (L 16404) — Meyer 2005 spectral identity (external reference)
4. `thm:spectral-weil` (L 16418) — Spectral-Weil correspondence
5. `lem:adelic-l2-regularization` — L² regularization

**Gap:** `thm:meyer-precise` requires Meyer's 2005 paper result which is not in Mathlib. This is **the arithmetic_admissibility axiom** in `RHSpectralMultiplicity.lean`.  
**Lean status:** `two_zeros_at_ordinate` proved (zero sorries). `riemann_hypothesis` closes via `arithmetic_admissibility` axiom.  
**Most self-contained pathway for Lean.**

---

### Pathway 3 — Probabilistic / BPY (Section `sec:pathway3-probabilistic`)
**Claim:** Biane-Pitman-Yor (Bull. AMS 2001): E[V^s] = 2ξ(s). Off-critical zero → non-normalizable or ghost state → contradiction with positive-definite Hilbert space.

**Key lemmas:**
1. `thm:biane-pitman-yor` — BPY theorem (external, not in Mathlib)
2. `thm:adelic-positivity-main` (L 23395) — Adelic Hilbert space is positive-definite
3. `thm:no-ghost` (L 20496) — Off-line zeros create ghost states
4. `lem:born-rule-haar` — Born rule bridges distributional and L² interpretations

**Gap:** BPY result not in Mathlib. Probabilistic setup requires significant infrastructure.

---

### Pathway 4 — Physics / Celestial (Section `sec:pathway4-physics`)
**Claim:** Celestial unitarity forces Re(Δ)=1; under Δ=2s this gives Re(s)=½. BMS Ward identities discretize the spectrum.

**Key lemmas:**
1. `thm:shadow-cpt` — Shadow=T (most cited, L 666)
2. `thm:canonical-dict` — Δ=2s canonical dictionary
3. `thm:ward-discretization` (L 20061) — BMS Ward identities discretize spectrum
4. `thm:l2-constraint-celestial` (L 23855) — L² constraint from celestial side
5. `thm:rh-direct-haar` (L 24028) — RH: direct Haar proof

**Gap:** Requires entire celestial holography apparatus (Chapters 5-8). Most physics-heavy pathway.

---

### Pathway 5 — Completeness / Yakaboylu (Section `sec:spectral-completeness`)
**Claim:** Beurling-Malliavin + Weil-Bombieri: RH ↔ completeness of Yakaboylu eigensystem in L². Pathways 1-4 establish RH, so completeness follows.

**Key lemmas:**
1. `thm:yakaboylu` (L 24091) — Yakaboylu 2025 result (external preprint)
2. `thm:celestial-weil` (L 24576) — Celestial unitarity implies Weil positivity
3. `thm:Q-equals-W-dense` (L 24731) — Q-form equals W-form on dense subspace
4. `thm:rh-unconditional` (L 24812) — Unconditional RH proof

**Gap:** Yakaboylu 2025 is a recent preprint; Beurling-Malliavin not in Mathlib.

---

## 4. DEPENDENCY GRAPH (Core RH chain)

```
Haar self-duality on (R+,×)
        │
        ├─→ thm:haar-self-dual [lem:haar-self-duality]
        │         │
        │         ├─→ thm:functional-equation-adelic  
        │         │         │
        │         │         └─→ thm:peter-weyl-compact
        │         │                   │
        │         │                   └─→ thm:l2-constraint ──→ RH (Pathway 1)
        │         │
        │         └─→ thm:meyer-precise [axiom: arithmetic_admissibility]
        │                   │
        │                   └─→ thm:spectral-weil ──→ RH (Pathway 2) ← CURRENT LEAN FOCUS
        │
        └─→ thm:shadow-cpt [Shadow = T, most cited]
                  │
                  ├─→ thm:canonical-dict [Δ = 2s]
                  │         │
                  │         └─→ thm:ward-discretization ──→ RH (Pathway 4)
                  │
                  └─→ cor:three-generations-anomaly [c=0 → 3 gens]
                            │
                            └─→ thm:link6 [OPEN: c_2D = c_4D^Weyl]
```

---

## 5. GAPS AND OPEN RESULTS

| Result | Label | Status | Notes |
|--------|-------|--------|-------|
| Link 6 | `thm:link6` | **OPEN** | c_2D = c_4D^Weyl needs rigorous proof; 10× cited |
| Spectral Transfer | `conj:spectral-transfer-onon` | **Conjecture** | 8× cited; YM mass formula conditional on this |
| Arithmetic Admissibility | (axiom in Lean) | **Axiom** | Core RH gap; equivalent to Meyer 2005 |
| CP phase | `conj:cp-alpha` | **Conjecture** | CP phase and fine structure constant |
| W/Z from BSD | `conj:higgs-bsd` | **Conjecture** | Higgs mechanism as BSD rank-1 lifting |
| Geometric hierarchy | `conj:geometric-hierarchy` | **Conjecture** | Topological hierarchy protection |
| DM abundance | `thm:dm-abundance` | **Conditional** | 13× cited; subject to mirror sector assumptions |
| `temperedness_iff_critical_line` | (Lean) | **Two sorries** | SchwartzMap.tsum not in Mathlib |

---

## 6. EXISTING LEAN FILES

Located at `/home/user/website/lean/GppVerify/`:

### `HaarSelfDuality.lean`
- **Status:** Zero sorries, zero errors ✓
- **Proves:** `haar_invariant_under_automorphism`, `grassmannian_haar_self_duality`
- **Maps to:** `lem:haar-self-duality` (L 16374)
- **Uses:** Mathlib's `MulEquiv.isHaarMeasure_map`, `isMulLeftInvariant_eq_smul_of_regular`

### `CoreTheorems.lean`  
- **Status:** Zero sorries; one axiom (`haar_uniqueness`) ✓
- **Proves:** 12 theorems: shadow involution, googly resolution, T⁴=id, Δ=2s functional equation, etc.
- **Maps to:** `thm:shadow-cpt` (partially), involution structure, `shadow_maps_to_functional_equation`
- **Note:** `haar_uniqueness` axiom is standard; full proof would use `thm:haar-existence`

### `RHSpectralMultiplicity.lean`
- **Status:** Core proven; two sorries in `temperedness_iff_critical_line`; one axiom (`arithmetic_admissibility`)
- **Proves:** `companion_im_eq`, `companion_ne_of_off_critical`, `zeta_zero_implies_fe_zero`, `two_zeros_at_ordinate`
- **Maps to:** Pathway 2 scaffolding; `thm:haar-self-dual`, spectral multiplicity argument
- **Gap:** `arithmetic_admissibility` = the Meyer 2005 step; `temperedness_iff_critical_line` needs `SchwartzMap.tsum`

---

## 7. RECOMMENDED FORMALIZATION ORDER

### Phase 0 — Infrastructure (already done)
- [x] `lem:haar-self-duality` → `HaarSelfDuality.lean`
- [x] Shadow involution structure → `CoreTheorems.lean`
- [x] Functional equation structure → `CoreTheorems.lean`
- [x] Two-zeros-at-ordinate → `RHSpectralMultiplicity.lean`

### Phase 1 — Fix existing sorries (immediate next step)
1. **`temperedness_iff_critical_line`** in `RHSpectralMultiplicity.lean`
   - Needs `SchwartzMap.tsum` or a workaround
   - Forward direction: `a≠0` → counterexample via `exp(au)` on Schwartz space
   - Backward direction: `a=0` → Fourier evaluation functional
2. **`arithmetic_admissibility`** — the big axiom
   - Approach: formalize Tate's thesis integrals using Mathlib's adele ring
   - Target: `Mathlib.NumberTheory.NumberField.Adeles`

### Phase 2 — Functional equation from Haar (Pathway 1 core)
3. New file: `RiemannHypothesis/FunctionalEquation.lean`
   - Formalize `thm:functional-equation-adelic` (L 16391)
   - Input: `lem:haar-self-duality` (done)
   - Output: ξ(s)=ξ(1-s) from Haar self-duality

### Phase 3 — L² constraint (Pathway 1 completion)
4. New file: `RiemannHypothesis/L2Constraint.lean`
   - Formalize `thm:l2-constraint` (L 16806)
   - Formalize `thm:peter-weyl-compact` for adelic quotient
   - Uses Mathlib: `MeasureTheory.Measure.Haar.Basic`, `Analysis.RCLike.L2`

### Phase 4 — Shadow=T theorem (most-cited result)
5. New file: `CelestialHolography/ShadowCPT.lean`
   - Formalize `thm:shadow-cpt` (L 666) — the 3-step proof
   - Step 1: Hodge star on Plücker coordinates
   - Step 2: Energy inversion ω→ω⁻¹
   - Step 3: Mellin → Δ↔2-Δ

### Phase 5 — Three generations (high-impact, self-contained)
6. New file: `StandardModel/ThreeGenerations.lean`
   - Formalize `cor:three-generations-anomaly` (L ~31614)
   - Depends on: c=0 anomaly, Boyle-Turok (external), Plücker partition theorem

### Phase 6 — Complete RH (Pathway 2)
7. Fill `arithmetic_admissibility` with Tate integral formalization
8. Close all sorries in `RHSpectralMultiplicity.lean`

---

## 8. MATHLIB COVERAGE

| shadow-framework concept | Mathlib location | Status |
|---|---|---|
| Haar measure existence | `MeasureTheory.Measure.Haar.Basic` | ✓ |
| Haar measure uniqueness | `MeasureTheory.Measure.Haar.Unique` | ✓ |
| Peter-Weyl theorem | Not yet in Mathlib | ✗ |
| Adele ring | `Mathlib.NumberTheory.NumberField.Adeles` | Partial |
| Riemann zeta | `Mathlib.NumberTheory.LSeries.RiemannZeta` | ✓ |
| Functional equation ξ(s)=ξ(1-s) | Not in Mathlib | ✗ |
| Schwartz space | `Mathlib.Analysis.Distribution.SchwartzSpace` | ✓ |
| SchwartzMap.tsum | Not in Mathlib | ✗ |
| Stone's theorem | `Mathlib.Topology.Algebra.Module.UniformConvergence` | Partial |
| L^p spaces | `Mathlib.MeasureTheory.Function.Lp*` | ✓ |
| Beurling-Malliavin | Not in Mathlib | ✗ |
| Meyer 2005 result | Not in Mathlib | ✗ |
| Grassmannian | `Mathlib.LinearAlgebra.Grassmannian` | Partial |

---

## 9. FLAGS

### Circularities to watch:
- `thm:link6` (c₂D = c₄D^Weyl) is 10× cited but explicitly noted as needing proof. Do NOT assume it.
- `conj:spectral-transfer-onon` conditions the mass formula — mark all downstream results as conditional.
- `arithmetic_admissibility` is equivalent to RH in one direction — cannot be used to prove RH without the other direction.

### Physical intuition vs. formal proof:
- Pathway 4 (celestial holography) uses physical gauge-fixing and Ward identities; these require careful BRST/functional-integral axioms not in standard Mathlib.
- The BMS algebra Jacobi identity is verified numerically but formal proof pending.
- `thm:rigidity` (Einstein uniqueness) assumes standard Wightman axioms as input.

### Verified numerically, not formally:
- c=0 (5 independent calculations, each to >10 sig figs in Python) — formal proof needed
- Glueball ratios 3/2 (< 2% vs lattice) — formal proof via Sugawara conditional
- Koide Q=2/3 to 0.03% — formal computation done; proof of WHY needs more work

---

## 10. SUMMARY

**Best single file to formalize next:** `temperedness_iff_critical_line` in `RHSpectralMultiplicity.lean` — it has two sorries and is the gateway to closing Pathway 2. Requires `SchwartzMap.tsum` workaround in Mathlib 4.19.

**Most impactful new file:** `RiemannHypothesis/FunctionalEquation.lean` — formalizes the functional equation from Tate's thesis using the existing `HaarSelfDuality.lean` as foundation.

**Most self-contained RH pathway for Lean:** Pathway 2 (Spectral/Meyer). The three key sorries are:
1. `temperedness_iff_critical_line` (infrastructure)
2. `arithmetic_admissibility` (Meyer 2005 step)
3. The two-zeros argument is **already clean** in `RHSpectralMultiplicity.lean`.
