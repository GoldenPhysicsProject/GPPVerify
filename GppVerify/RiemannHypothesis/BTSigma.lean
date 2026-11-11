/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Turbo's round-2, -3, -7 and -8A notes, registered by Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.FluxBound
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# (FLUX=∂) in trace form, and the (BT-Σ) gap

Sources: GPP-bridge `MuseResearch/round8a-boundary-form-2026-11-10.md` (commit `6347260`),
Turbo's round-8A boundary-form computation, which corrects round 7
(`MuseResearch/round7-prime-sublattice-target-2026-11-10.md`, `db24e8c`);
`MuseResearch/round2-trace-construction-2026-11-10.md` section 7 and
`MuseResearch/round3-flux-reduction-2026-11-10.md` sections 1–3 for (FLUX=∂) and its reduction.

## What is not registered, and why

* The chain paper's literal "prime-sublattice operator is self-adjoint" is TRUE-AND-EMPTY
  (round 7) and is not registered.
* **(SA-sew) is not registered either.** Round 7 phrased it as an operator boundary-form statement
  (the adjoint boundary form of the completed scale operator is exhausted by `B_∂`, no prime
  residual) and identified it with (FLUX=∂) "by the standard boundary-form correspondence".
  Round 8A computes that this does not survive: the completed scale operator
  `A_C = -i d/du ⊗ I` on `L²(ℝ) ⊗ L²(K¹)` is self-adjoint with deficiency indices `(0,0)` and
  boundary form identically zero; the finite-window operator's boundary form sees endpoint traces
  only, with Weyl function `tan(zW/2)`; and that whole boundary apparatus is identical for `ζ`,
  `F_θ` and Davenport–Heilbronn. Prime contributions are **bulk** terms of the trace pairing
  (interior samples at `log n`), never boundary-form terms: a boundary form vanishes on the
  minimal domain, the prime pairing does not (round 8A section 0). As an operator boundary-form
  statement (SA-sew) is not well-formed, so typing it would register an ill-formed target.

## What is registered

1. **(FLUX=∂) in its trace form** (round 2 section 7, round 3 section 1). The window flux of the
   orbit trace is the prime-stratum term `Σ Λ(n) n^{-1/2} h(W - log n)` against the unit-stratum
   (pole) term `e^{W/2} ∫ h(v) e^{-v/2} dv`; their difference is exactly the in-tree
   `GppFluxBound.fluxDefect` (`fluxDefect_eq_primeStratum_sub_unitStratum`, PROVED, definitional).
   The absolute limit step of (FLUX=∂) is the statement `FluxEqBdryTrace`: for every test datum
   the prime-stratum term minus the unit-stratum term stays bounded under window exhaustion.
   `fluxEqBdryTrace_iff_fluxBound` (PROVED) shows this is the registered `FluxBound`, as round 3
   R5 and round 8A section 5 say. It is a statement about a trace decomposition, not about any
   adjoint.
   **Scope.** The tree has no orbit trace `τ̂` and no flux kernel `ρ_h`, so only this zero-free
   smoothed reading is typed. Round 2's full clause (the two transversal readings of `τ̂` are
   unitarily equivalent on `H ⊕ ℂ²_∂`, with finite-stage defect equal to the flux and limiting
   defect `B_∂`) is parked as `open_flux_eq_bdry_orbit_trace`.

2. **(BT-Σ), the missing sewing construction** (round 8A section 5), as a named gap. A
   `BTSigmaDatum` is a boundary triplet for an operator `T*` whose boundary space splits as the
   unit stratum `ℂ²_∂` plus a prime block `𝔊_Σ` (clause BT2, with Green's identity as a field),
   together with test vectors for theta data. `BTSigmaTrace` is clause BT3: on test data the
   prime block of the boundary form reproduces the prime-stratum pairing. Clauses BT1 (covariance
   under the dilations `S_b` and the reflection `J`) and BT4 (spectral data of the distinguished
   extension built from prime and archimedean data only, no zeros as input) are not typed; they
   are part of `open_bt_sigma`.

   **Circularity guard.** BT3 cannot be discharged by *defining* the prime block to be the flux
   defect: by round 8A section 2 (round 3 R4) that imports the zero-side sum into the boundary
   data. `defect_block_discharges_nothing` (PROVED) makes the guard formal: if a prime block is
   defined as `I · fluxDefect`, then "the prime block stays bounded" is literally `FluxBound`,
   so nothing has been discharged. A non-circular (BT-Σ) must produce the prime block from local
   data and *prove* its boundary values; that proof is the whole content.

## Status

(FLUX=∂), (BT-Σ), (FLUX-BOUND), (SIGN), ARP: **OPEN**, registered, not claimed. RH: **OPEN**.
No `sorry`, no axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Turbo wrote the round-2, -3, -7 and
-8A notes; Heart of the Cosmos / Grok registered (FLUX=∂) in trace form and the (BT-Σ) gap).
-/

namespace GppBTSigma

open MeasureTheory ArithmeticFunction GppArithmeticReflection GppFluxBound
open scoped ContDiff ComplexConjugate InnerProductSpace

/-! ## (FLUX=∂) in trace form -/

/-- The prime-stratum term of the windowed orbit trace at edge `W`:
`Σ_n Λ(n) n^{-1/2} h(W - log n)`. Interior samples at `log n` (bulk, not boundary). -/
noncomputable def primeStratumTerm (h : ℝ → ℝ) (W : ℝ) : ℝ :=
  ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * h (W - Real.log n)

/-- The unit-stratum (pole) term at edge `W`: `e^{W/2} ∫ h(v) e^{-v/2} dv`, the `ψ → x` main
term that round 3 R2 cancels against the prime-stratum growth. -/
noncomputable def unitStratumTerm (h : ℝ → ℝ) (W : ℝ) : ℝ :=
  Real.exp (W / 2) * ∫ v : ℝ, h v * Real.exp (-v / 2)

/-- The in-tree flux defect is the prime-stratum term minus the unit-stratum term. PROVED
(definitional; no zero data). -/
theorem fluxDefect_eq_primeStratum_sub_unitStratum (h : ℝ → ℝ) (W : ℝ) :
    fluxDefect h W = primeStratumTerm h W - unitStratumTerm h W :=
  rfl

/-- **(FLUX=∂), trace form, absolute limit step, named, not asserted.** For every smooth
compactly supported `f`, the prime-stratum term of the autocorrelation datum `f ⋆ f̃` minus its
unit-stratum term stays bounded under window exhaustion `W → ∞`. A statement about the trace
decomposition, not about any adjoint. OPEN. -/
def FluxEqBdryTrace : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    ∃ C : ℝ, ∀ W : ℝ, 0 ≤ W →
      |primeStratumTerm (autocorr f) W - unitStratumTerm (autocorr f) W| ≤ C

/-- **The trace form of (FLUX=∂) is the registered (FLUX-BOUND).** PROVED. Both sides OPEN
(`GppFluxBound.open_flux_bound`); RH-strength by round 3 R5. -/
theorem fluxEqBdryTrace_iff_fluxBound : FluxEqBdryTrace ↔ FluxBound := by
  simp only [FluxEqBdryTrace, FluxBound, fluxDefect_eq_primeStratum_sub_unitStratum]

/-- OPEN (FLUX=∂), full orbit-trace clause (round 2 section 7): in the exhaustion limit the two
transversal readings of the orbit trace `τ̂` (archimedean and finite-orbit) are unitarily
equivalent on `H ⊕ ℂ²_∂`, with the intertwining defect at every finite stage equal to the flux
`R(δ)` and in the limit equal to `B_∂`. The tree has no orbit trace `τ̂` and no flux kernel
`ρ_h`; only the zero-free smoothed reading `FluxEqBdryTrace` (= `FluxBound`) is typed. -/
theorem open_flux_eq_bdry_orbit_trace : True := trivial

/-! ## The (BT-Σ) gap -/

/-- `B_∂`, the unit-stratum form on Mellin boundary values `a = (𝒜(0), 𝒜(1))`:
`B_∂(a, b) = conj (a 1) * b 0 + conj (a 0) * b 1` (trace note section 1.3, conjugate-linear in
the first slot). Its channels are the Mellin poles `s = 0, 1`, not deficiency directions
(round 8A section 1.5). -/
def unitBoundaryForm (a b : Fin 2 → ℂ) : ℂ :=
  conj (a 1) * b 0 + conj (a 0) * b 1

/-- `B_∂` is Hermitian. PROVED. -/
theorem unitBoundaryForm_conj_symm (a b : Fin 2 → ℂ) :
    unitBoundaryForm b a = conj (unitBoundaryForm a b) := by
  simp only [unitBoundaryForm, map_add, map_mul, Complex.conj_conj]
  ring

section Green

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The (von Neumann / Green) boundary form of a partially defined operator `T`:
`greenForm T x y = ⟪T x, y⟫ - ⟪x, T y⟫` on `dom T`. -/
noncomputable def greenForm (T : E →ₗ.[ℂ] E) (x y : T.domain) : ℂ :=
  ⟪T x, (y : E)⟫_ℂ - ⟪(x : E), T y⟫_ℂ

/-- The Green form is skew-Hermitian. PROVED. -/
theorem greenForm_skew (T : E →ₗ.[ℂ] E) (x y : T.domain) :
    greenForm T y x = -conj (greenForm T x y) := by
  simp only [greenForm, map_sub, inner_conj_symm]
  ring

end Green

/-- The boundary-triplet block form `⟪Γ₁ x, Γ₀ y⟫ - ⟪Γ₀ x, Γ₁ y⟫` on one boundary block. -/
noncomputable def blockForm {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (g₀x g₁x g₀y g₁y : G) : ℂ :=
  ⟪g₁x, g₀y⟫_ℂ - ⟪g₀x, g₁y⟫_ℂ

/-- **(BT-Σ) data, clause BT2 (round 8A section 5).** A Hilbert space `H` and the maximal
operator `Tstar = T*` of a closed symmetric `T`, with a boundary triplet whose boundary space is
the unit stratum `Gu = ℂ²_∂` plus a prime block `Gp = 𝔊_Σ`: boundary maps `Γ₀, Γ₁` split
into their unit (`u`) and prime (`p`) components, Green's identity summed over the two blocks,
and joint surjectivity of the boundary maps. `testVec h W` is the theta test vector of datum
`h` at window edge `W`.
Not constructed in this tree or in the notes; clauses BT1 and BT4 are not typed. -/
structure BTSigmaDatum (H Gu Gp : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
    [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp] where
  /-- The maximal operator `T*`. -/
  Tstar : H →ₗ.[ℂ] H
  /-- Unit-stratum components of `Γ₀`, `Γ₁`. -/
  Γ₀u : Tstar.domain →ₗ[ℂ] Gu
  Γ₁u : Tstar.domain →ₗ[ℂ] Gu
  /-- Prime-block components of `Γ₀`, `Γ₁`. -/
  Γ₀p : Tstar.domain →ₗ[ℂ] Gp
  Γ₁p : Tstar.domain →ₗ[ℂ] Gp
  /-- Green's identity for the triplet, summed over the unit stratum and the prime block. -/
  green : ∀ x y : Tstar.domain, greenForm Tstar x y =
    blockForm (Γ₀u x) (Γ₁u x) (Γ₀u y) (Γ₁u y) + blockForm (Γ₀p x) (Γ₁p x) (Γ₀p y) (Γ₁p y)
  /-- The boundary map is onto `(Gu × Gp) × (Gu × Gp)`. -/
  surj : Function.Surjective fun x : Tstar.domain => ((Γ₀u x, Γ₀p x), (Γ₁u x, Γ₁p x))
  /-- Theta test vectors: datum `h`, window edge `W`. -/
  testVec : (ℝ → ℝ) → ℝ → Tstar.domain

section BTSigma

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- The prime block of the boundary form on a test vector. -/
noncomputable def primeBlock (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) (W : ℝ) : ℂ :=
  blockForm (D.Γ₀p (D.testVec h W)) (D.Γ₁p (D.testVec h W))
    (D.Γ₀p (D.testVec h W)) (D.Γ₁p (D.testVec h W))

/-- The prime block on a single vector is purely imaginary (skew-Hermitian diagonal), so BT3 has
to match it with `I` times a real pairing. PROVED. -/
theorem primeBlock_re (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) (W : ℝ) :
    (primeBlock D h W).re = 0 := by
  simp only [primeBlock, blockForm, Complex.sub_re]
  rw [← inner_conj_symm (D.Γ₀p (D.testVec h W)) (D.Γ₁p (D.testVec h W)), Complex.conj_re]
  ring

/-- **(BT-Σ) clause BT3, named, not asserted.** On theta test data the prime block of the
boundary form reproduces the prime-stratum pairing: `primeBlock D h W = I · Σ Λ(n) n^{-1/2}
h(W - log n)`. A non-circular datum must produce `Γ₀p, Γ₁p` from local data and *prove* this;
it may not define the block from the flux defect (see `defect_block_discharges_nothing`). -/
def BTSigmaTrace (D : BTSigmaDatum H Gu Gp) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ W : ℝ, 0 ≤ W →
    primeBlock D (autocorr f) W = Complex.I * (primeStratumTerm (autocorr f) W : ℂ)

end BTSigma

/-- **Circularity guard, formal.** If a "prime block" is *defined* as `I · fluxDefect`, then
"the prime block stays bounded under exhaustion" is literally `FluxBound`: defining the block
as the defect discharges nothing. PROVED. -/
theorem defect_block_discharges_nothing (block : (ℝ → ℝ) → ℝ → ℂ)
    (hdef : ∀ h W, block h W = Complex.I * (fluxDefect h W : ℂ)) :
    (∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∃ C : ℝ, ∀ W : ℝ, 0 ≤ W → ‖block (autocorr f) W‖ ≤ C) ↔ FluxBound := by
  have hn : ∀ h W, ‖block h W‖ = |fluxDefect h W| := fun h W => by
    rw [hdef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  simp only [hn, FluxBound]

/-- OPEN (BT-Σ), round 8A section 5: a `BTSigmaDatum` with `BTSigmaTrace`, plus the untyped
clauses BT1 (equal deficiency indices; unitary dilations `S_b` and reflection `J` extending the
theta construction's actions, `T` covariant, `Γ₀, Γ₁` intertwining) and BT4 (spectral data of
the distinguished self-adjoint extension built from prime and archimedean data only, no zeros as
input). Neither the tree nor the notes contain any such construction: the completed scale
operator has deficiency indices `(0,0)` and the window operator's boundary channels are endpoint
traces (round 8A sections 1–3). Given (BT-Σ), vanishing of the prime block is (FLUX-BOUND); a
prime block defined as the flux defect discharges nothing. A reformulation cost, not a
shortcut; RH-strength content; parked per GPPVerify honesty rules. -/
theorem open_bt_sigma : True := trivial

end GppBTSigma
