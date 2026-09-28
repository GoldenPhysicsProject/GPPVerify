import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A metric that is positive on `A − z` makes the parity cross-resolvent positive

Source: Codex, GPPDiscovery2 `codex/discovery-workbench`,
`research/2026-09-28_kms_metric_simple_even_ground.md` (commit `250c98a`), §2.

The Weil-Parity thread reduces the "simple, even finite Weil ground state" step to positivity of
the cross-resolvent `f(z) = ηᵀ (A₊ − z)⁻¹ e₀` for real `z` below the even ground (see
`CrossResolvent.lean`, `StrictParityInterlacing.lean`). Codex's note observes that one metric
would supply that positivity. Its hypotheses are: `G` positive definite, `G A = Aᵀ G`, and
`G e₀ = η`.

**Sharpening (this file).** The identity behind the note needs no symmetry at all. Put
`y = (A − z)⁻¹ e₀` and `η = G e₀`. Then

  `f(z) = ηᵀ y = (G (A − z) y)ᵀ y = yᵀ G (A − z) y`

holds for any `G` (`cross_resolvent_eq_energy`). So `f(z) > 0` follows from positivity of the
single form `x ↦ xᵀ G (A − z) x` (`cross_resolvent_pos_of_energy_pos`). The note's hypotheses
(`G` symmetric positive definite, `G A = Aᵀ G`) are what make that form the `G`-energy of a
`G`-self-adjoint operator. Only through them does its positivity mean "`z` lies below the
`G`-spectrum". They are needed to interpret the hypothesis, not to derive the conclusion.

**Contrapositive** (`no_metric_of_cross_resolvent_nonpos`). If `f(z) ≤ 0`, then **no** matrix `G`
with `G e₀ = η` makes `A − z` `G`-positive: not symmetric ones, not any. This is the exact form of
Codex's earlier negative finding. Sign-changing arithmetic cross-resolvent values in the raw
CCM basis rule out every such metric there.

## Scope

Finite real linear algebra. Whether the Bost–Connes KMS Gram, transported into the even Weil block,
satisfies `G e₀ = η` and makes `A₊ − z` `G`-positive below the ground is the open arithmetic
question the note poses. It is not claimed here. No RH claim.
-/

open Matrix

namespace GppKMSMetricWeyl

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The cross-resolvent is a `G`-energy.** If `G e₀ = η` and `(A − z) y = e₀`, then
`ηᵀ y = yᵀ G (A − z) y`. No symmetry of `G` or `A` is needed. -/
theorem cross_resolvent_eq_energy (A G : Matrix n n ℝ) (z : ℝ) (e₀ η y : n → ℝ)
    (hη : G *ᵥ e₀ = η) (hy : (A - z • 1) *ᵥ y = e₀) :
    η ⬝ᵥ y = y ⬝ᵥ (G *ᵥ ((A - z • 1) *ᵥ y)) := by
  rw [hy, hη, dotProduct_comm]

/-- **Positive `G`-energy gives a positive cross-resolvent.** If `xᵀ G (A − z) x > 0` for every
`x ≠ 0`, `G e₀ = η`, `A − z` is invertible and `e₀ ≠ 0`, then `f(z) = ηᵀ (A − z)⁻¹ e₀ > 0`. -/
theorem cross_resolvent_pos_of_energy_pos (A G : Matrix n n ℝ) (z : ℝ) (e₀ η : n → ℝ)
    (hη : G *ᵥ e₀ = η)
    (hpos : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ ((A - z • 1) *ᵥ x)))
    (hinv : IsUnit (A - z • 1).det) (he₀ : e₀ ≠ 0) :
    0 < η ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ e₀) := by
  have hy : (A - z • 1) *ᵥ ((A - z • 1)⁻¹ *ᵥ e₀) = e₀ := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec]
  have hy0 : (A - z • 1)⁻¹ *ᵥ e₀ ≠ 0 := by
    intro h; rw [h, mulVec_zero] at hy; exact he₀ hy.symm
  rw [cross_resolvent_eq_energy A G z e₀ η _ hη hy]
  exact hpos _ hy0

/-- **Contrapositive.** A nonpositive cross-resolvent value rules out **every** matrix `G` with
`G e₀ = η` for which `A − z` is `G`-positive. -/
theorem no_metric_of_cross_resolvent_nonpos (A : Matrix n n ℝ) (z : ℝ) (e₀ η : n → ℝ)
    (hinv : IsUnit (A - z • 1).det) (he₀ : e₀ ≠ 0)
    (hf : η ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ e₀) ≤ 0) :
    ¬ ∃ G : Matrix n n ℝ, G *ᵥ e₀ = η ∧
        ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ ((A - z • 1) *ᵥ x)) := by
  rintro ⟨G, hη, hpos⟩
  exact absurd hf (not_le.mpr (cross_resolvent_pos_of_energy_pos A G z e₀ η hη hpos hinv he₀))

/-- **Rayleigh form of the hypothesis.** If `z · xᵀ G x < xᵀ G A x` for every `x ≠ 0` (`z` strictly
below every `G`-Rayleigh quotient of `A`), then `xᵀ G (A − z) x > 0`. When `G` is symmetric positive
definite and `G A = Aᵀ G`, this Rayleigh bound is exactly "`z` is below the `G`-spectrum of `A`", which
is the note's formulation. Those conditions interpret the bound and are not needed for this implication. -/
theorem energy_pos_of_rayleigh (A G : Matrix n n ℝ) (z : ℝ)
    (hray : ∀ x : n → ℝ, x ≠ 0 → z * (x ⬝ᵥ (G *ᵥ x)) < x ⬝ᵥ (G *ᵥ (A *ᵥ x)))
    (x : n → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (G *ᵥ ((A - z • 1) *ᵥ x)) := by
  have h := hray x hx
  rw [sub_mulVec, mulVec_sub, dotProduct_sub, smul_mulVec, one_mulVec, mulVec_smul,
    dotProduct_smul, smul_eq_mul]
  linarith

end GppKMSMetricWeyl
