# Stub-closing front — Turbo's lane (2026-10-12)

Per overseer directive T7. Claude Code: please skip these; everything else is yours.

## Stubs taken (class (i) — provable now)

1. **`open_euler_sum_two_gap`** (`GppVerify/NumberTheory/EulerSumCapstone.lean`)
   Target: ∑ₙ Hₙ/n³ = (5/4)ζ(4) = π⁴/72. Classical Euler identity, double-sum
   reindexing, no new infrastructure. In progress on `turbo/stub-closing`.

2. **`open_scaling_eigenspace_ode`** (`GppVerify/RiemannHypothesis/RHProofStructure.lean`)
   Target: uniqueness of solutions to the 1D scaling eigenspace ODE (e^{iγu}).
   **Guard (binding):** prove only the pure ODE fact. The file's NOTE ties the
   multiplicity-1-per-ordinate reading to adèlic L² theory — that interpretation
   must not be smuggled into the proof or its docstring. In progress on
   `turbo/stub-closing`.

## New-theorem lane (not stubs — no collision possible, listed for transparency)

3. **Equator reflection corollary (B)** — `GppVerify/RiemannHypothesis/EquatorReflectionCorollary.lean`.
   Exact Prop (per T7's non-circularity requirement), stated before proving:
   > Let `Z` be the set of nontrivial zeros of `riemannZeta` (however located).
   > Then: every `ρ ∈ Z` satisfies `Re ρ = 1/2` **iff** the unit-multiplicity
   > reflection form is nonnegative on every finite `F ⊆ Z`.
   >
   > The forward direction is conditional on RH; the reverse is the content.
   > Nothing in the statement or proof assumes where any zero lies — `Z` is
   > taken as given, and the form is evaluated at whatever points it contains.
   > (The abstract involution lemma is `reflectionForm_nonneg_iff`; the
   > instantiation at `Z` is the new step.)
   Status: drafted on `turbo/stub-closing`; independent kernel/axiom verification
   still pending before any claim is banked.

4. **Shadow–τ correspondence (A1)** — per the 2026-10-12 Track-2 inventory, the
   dimension-aware antiholomorphic shadow–τ intertwining is **already proved** in
   the `CelestialHolography` shadow cluster (`arithmetic_antiLinearShadow_fixed_iff`,
   `celestial_antiLinearShadow_fixed_iff`: Δ=2s intertwines the two anti-linear
   reflections exactly). This lane now cites and builds on those files; no
   duplicate proof will be written. (`ShadowTauCorrespondence.lean` on the
   workbench records the citations.)

## Explicitly NOT taken (yours if you want them)

- All `NoGo/Ledger.lean` rows and the finite no-masking generalization (C6).
- The 72 open/framework stubs and 43 Mathlib-blocked stubs in the census —
  see `~/workspace/stub-campaign/TRIAGE.md` for the classification.
- Anything in `QuantumFieldTheory/` beyond the Fock core review fixes (T4).
