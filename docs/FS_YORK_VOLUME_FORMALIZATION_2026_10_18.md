# Fubini–Study / York-volume formalization ledger (2026-10-18)

**Purpose:** Develop a proof-checked bridge from quantum projective-state geometry to the proper-volume work variable in Jacobson's causal-diamond entanglement equilibrium. Distinguish mathematical statements **proved in Lean** from physical identifications that remain hypotheses. This file accompanies PR #389.

## Existing verified assets reused

- `GppVerify/CelestialHolography/FubiniStudyAntipodal.lean`: corrected CP1 Fubini–Study unsigned measure under antipodal map, **including Jacobian**; disproves bare density invariance.
- `GppVerify/CelestialHolography/FubiniStudyOrientation.lean`: signed/oriented symplectic two-form reverses, unsigned density preserved.
- `GppVerify/QuantumGravity/CausalDiamondFisherCancellation.lean`: exact scalar cancellation `KL-density × BW-kernel = (2/pi) lambda²`, away from the removable endpoint.
- `GppVerify/GeneralRelativity/VolumeConstraintEntanglement.lean`: first-law algebra, explicit conditional Einstein/CKV curvature identity, RNC deficits and linearized stationary-constraint hyperplane uniqueness.

## New files

1. `GppVerify/GeneralRelativity/YorkVolumeSymplectic.lean`: exact finite-sum ADM trace-momentum pairing; `Ω(δYork, δ)=2c δV` in the specified discretized canonical data; explicit ADM coefficient `c=(1-n)α`; linearized Hamiltonian constraint implies `K=0` for nontrivial York shifts and `n≠1`; independent-cell weighted-volume rigidity proves that equality with unweighted response for all variations forces spatially constant weights; momentum-reversal antisymplectic identity.
2. `GppVerify/QuantumGravity/FubiniStudyLocalKahler.lean`: local CP1 metric and symplectic form with common density `(1+r)⁻²`; `J²=-id`, `ω(u,v)=g(Ju,v)`, metric nonnegativity, antiunitary metric invariance and symplectic sign reversal.
3. `GppVerify/QuantumGravity/FubiniStudyYorkBridge.lean`: projective horizontal projection and scalar-ray invariance; conditional equivalence `dV=0 ↔ g(JδYork,δ)=0`; conditional entropy stationarity correspondence; explicit normalization counterexample.

## Source mathematics and exact limits

- Belin, Lewkowycz, Sárosi, *Complexity and the bulk volume, a new York time story*, JHEP 03 (2019) 044, https://arxiv.org/abs/1811.03097. Their York formula is in **bulk symplectic geometry**; the boundary Fubini–Study equality is proven in specified holographic source-state settings, not in generic causal-diamond QFT.
- Jacobson & Visser, *Gravitational thermodynamics of causal diamonds in (A)dS*, SciPost Phys. 7 (2019) 079, https://arxiv.org/abs/1812.01596. Their unweighted proper-volume work term is geometric, with a specific variation class and normalization.
- Toupin, *The volume constraint in entanglement equilibrium* and *The Fisher form of the causal diamond*: retain distinction between **Kubo–Mori** mixed-state Fisher Hessian and **Fubini–Study** pure-state Kähler geometry.
- Projective normalization annihilates scalar phase directions but **cannot by itself imply fixed geometric volume**; `normalized_state_tangent_with_nonzero_volume` proves the finite-dimensional independence.
- The exact conditional FS–York theorem assumes two specific identities: (i) `ω_bulk=ω_boundary,FS` on the admitted variation space, and (ii) `ω_bulk(δYork,δ)=c dV(δ)`, with `c≠0`. Their physical validity, including boundary conditions, is **not** an output of the abstract bridge lemma.

## Still open / do not claim checked

- Covariant Einstein–Hilbert symplectic form from arbitrary smooth solutions with boundaries, and its equivalence to the ADM canonical pairing.
- That the specific York variation is tangent to the true gravitational constraint surface for arbitrary background, rather than only admissible in studied maximal-slice situations.
- Boundary/bulk symplectic correspondence outside the holographic contexts of Belin et al.
- Universal relation between Araki relative-entropy / Kubo–Mori information geometry and projective Fubini–Study data.
- A derivation of `dV=0` **solely** from normalizing quantum states / factoring out scalar modular shifts.
- The full higher-curvature/generalized-volume analogue; a true nonlinear classification of volume-constrained ensembles.

## Upstreaming plan

GPPVerify main is the immediate upstream target for the PR. The local complex structure and phase-horizontal projection are generic mathematics and are possible candidates for **Mathlib** as projective/complex-Hermitian geometry develops. Existing Mathlib projectivization definitions, desired APIs and proof dependencies must be checked before submitting to leanprover-community/mathlib4; avoid a stand-alone physics-specific file. A candidate pure CP1 chart was staged as **draft** `GoldenPhysicsProject/mathlib4` PR #1 on `gpp/fs-local-kahler-candidate-20261018`. It does **not** constitute acceptance by official `leanprover-community/mathlib4`. Mathlib fork CI, API integration and maintainer feedback are required.

## Reproducibility

See `.github/workflows/fs-york-targeted.yml` for the fresh module build and source-aware sorry checks; full GPPVerify CI additionally verifies imports, axioms, vacuity and stubs. **Status is determined by CI on the exact head commit, not by the presence of Lean source.**
