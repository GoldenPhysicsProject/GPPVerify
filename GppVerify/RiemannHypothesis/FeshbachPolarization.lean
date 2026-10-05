import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two-boundary polarization of a signed cross response, and the shifted Euler factor

Source: Codex, `research/codex/2026-10-02_finite_feshbach_rank_two_and_hodge_obstruction.md`,
§§3–4 (the exact algebraic parts).

For vectors `u, v` in a complex inner product space:

* `gram_form`: `‖α u + β v‖² = |α|²‖u‖² + 2 Re(ᾱ β ⟨u, v⟩) + |β|²‖v‖²`, so the `2×2` Gram matrix
  `B*B` of `B(α, β) = α u + β v` is positive semidefinite (`gram_form_nonneg`);
* `abs_inner_sq_le`: its determinant is nonnegative, `|⟨u, v⟩|² ≤ ‖u‖²‖v‖²`;
* `polarization`: `4 Re⟨v, u⟩ = ‖u + v‖² − ‖u − v‖²` — a signed scalar cross response is a polarization
  of two positive channels;
* `shifted_factor`: `(1 − p^{-1/2+θ} z)(1 − p^{-1/2-θ} z) = 1 − 2 cosh(θ log p) p^{-1/2} z + p^{-1} z²`,
  the algebra of the two-species `θ`-control factor `M_{p,θ}` (here `z` stands for `V_{log p}`).

## Checks and scope

All claims check, and the note itself stresses their limit (§4): the Gram completion exists for *any*
real phase, so it cannot distinguish the true zeta from the shifted control. **Not formalized:** the
phase `q̃_L`, the rank-one causal resolvent formula (§2), the Koszul/Hodge-gap obstruction (§5, a
statement that an additive Koszul bound cannot replace the multiplicative Möbius whitening), and the
graded Feshbach map `Γ_L` the note leaves unconstructed. No RH claim.
-/

open scoped InnerProductSpace ComplexConjugate

namespace GppFeshbachPolarization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Expansion of the two-boundary norm. -/
theorem gram_form (u v : E) (α β : ℂ) :
    ‖α • u + β • v‖ ^ 2 =
      ‖α‖ ^ 2 * ‖u‖ ^ 2 + 2 * (conj α * β * ⟪u, v⟫_ℂ).re + ‖β‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, inner_smul_left, inner_smul_right]
  simp only [RCLike.re_to_complex, mul_pow]
  ring_nf

theorem gram_form_nonneg (u v : E) (α β : ℂ) :
    0 ≤ ‖α‖ ^ 2 * ‖u‖ ^ 2 + 2 * (conj α * β * ⟪u, v⟫_ℂ).re + ‖β‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [← gram_form]; positivity

/-- The Gram determinant is nonnegative. -/
theorem abs_inner_sq_le (u v : E) : ‖⟪u, v⟫_ℂ‖ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have := norm_inner_le_norm (𝕜 := ℂ) u v
  have h0 := norm_nonneg ⟪u, v⟫_ℂ
  calc ‖⟪u, v⟫_ℂ‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by gcongr
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring

/-- **Polarization.** -/
theorem polarization (u v : E) :
    4 * (⟪v, u⟫_ℂ).re = ‖u + v‖ ^ 2 - ‖u - v‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  have : (⟪v, u⟫_ℂ).re = (⟪u, v⟫_ℂ).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) u v]; exact Complex.conj_re _
  simp only [RCLike.re_to_complex]
  rw [this]; ring

end GppFeshbachPolarization

namespace GppShiftedFactor

/-- **The two-species factor.** -/
theorem shifted_factor (p θ z : ℝ) (hp : 0 < p) :
    (1 - p ^ (-(1 / 2 : ℝ) + θ) * z) * (1 - p ^ (-(1 / 2 : ℝ) - θ) * z) =
      1 - 2 * Real.cosh (θ * Real.log p) * p ^ (-(1 / 2 : ℝ)) * z + p⁻¹ * z ^ 2 := by
  have e1 : p ^ (-(1 / 2 : ℝ) + θ) = p ^ (-(1 / 2 : ℝ)) * Real.exp (θ * Real.log p) := by
    rw [Real.rpow_add hp]; congr 1; rw [Real.rpow_def_of_pos hp]; congr 1; ring
  have e2 : p ^ (-(1 / 2 : ℝ) - θ) = p ^ (-(1 / 2 : ℝ)) * Real.exp (-(θ * Real.log p)) := by
    rw [sub_eq_add_neg, Real.rpow_add hp]; congr 1; rw [Real.rpow_def_of_pos hp]; congr 1; ring
  have e3 : p ^ (-(1 / 2 : ℝ)) * p ^ (-(1 / 2 : ℝ)) = p⁻¹ := by
    rw [← Real.rpow_add hp]; norm_num [Real.rpow_neg_one]
  have e4 : Real.exp (θ * Real.log p) * Real.exp (-(θ * Real.log p)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [e1, e2, Real.cosh_eq]
  have : (1 - p ^ (-(1 / 2 : ℝ)) * Real.exp (θ * Real.log p) * z) *
      (1 - p ^ (-(1 / 2 : ℝ)) * Real.exp (-(θ * Real.log p)) * z) =
      1 - p ^ (-(1 / 2 : ℝ)) * (Real.exp (θ * Real.log p) + Real.exp (-(θ * Real.log p))) * z +
        (p ^ (-(1 / 2 : ℝ)) * p ^ (-(1 / 2 : ℝ))) * (Real.exp (θ * Real.log p) *
          Real.exp (-(θ * Real.log p))) * z ^ 2 := by ring
  rw [this, e3, e4]
  ring

end GppShiftedFactor
