import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Module.Basic
import GppVerify.RiemannHypothesis.FourComponentRigidity

/-!
# Critical BPY coercivity: the exact algebraic and arithmetic steps

Source: Codex, GPPDiscovery2 `codex/discovery-workbench`,
`research/2026-09-28_critical_bpy_first_chaos_coercivity.md` (commit `363bafa`) and its
checker `DiscoveryLean/CriticalBPYCoercivity.lean` (`980b4dc`).

The note proves that the critical connected BPY synthesis `C_{1/2} e_n = V_n` is bounded
below: `C_{1/2}* C_{1/2} ≥ δ² I`. The argument projects onto the first Laguerre chaos, where
the synthesis becomes the Dirichlet-convolution operator `B = Σ_r b_r S_r` with each `S_r` an
isometry. It then shows `Σ_{r≥2} b_r < b_1`, using
`Σ_{r≥2} b_r / b_1 < (π²/6 − 1)(1 + 63/(16π²)) < 1`. The input
`ξ(9/2)/ξ(5/2) = (21/(4π)) · ζ(9/2)/ζ(5/2)` feeds the `63/(16π²)`.

This file proves the exact, non-probabilistic steps:

* `norm_isometry_sum_ge`: for isometries `U_i`,
  `‖b₀ x + Σ_i b_i U_i x‖ ≥ (|b₀| − Σ_i |b_i|) ‖x‖`. This is the Neumann-series step of §4,
  for finite families.
* `pi_sq_bounds`, `tail_constant_lt_one`: `9 < π² < 10` and
  `(π²/6 − 1)(1 + 63/(16π²)) < 1`. These are Codex's checker, re-proved.
* `Gammaℝ_nine_halves`: `Γ_ℝ(9/2) = (5/(4π)) Γ_ℝ(5/2)`.
* `xi_ratio`: `ξ(9/2) ζ(5/2) = (21/(4π)) ζ(9/2) ξ(5/2)`. This is the note's ratio identity
  in division-free form, derived from Mathlib's completed zeta, not assumed. Checked by hand
  too: `Γ(9/4) = (5/4) Γ(5/4)` and `(63/4)/(15/4) · 5/4 = 21/4`.

## Scope

Not formalized: the BPY Gamma field, the first-chaos coefficients `b_r` and their positivity,
the integral representation of `b_r`, the convexity (Jensen) step, the BPY Mellin identity
`E Q^{s/2} = 2ξ(s)` that turns `E_ν T` into `(3/4) ξ(9/2)/ξ(5/2)`, and the inequality
`ζ(9/2) < ζ(5/2)`. The note makes no RH claim, and none is made here.
-/

namespace GppCriticalBPYCoercivity

open GppFourComponentRigidity

/-- **Neumann lower bound for a sum of isometries.** If every `U i` preserves norms, then
`‖b₀ x + Σ_{i∈F} b_i U_i x‖ ≥ (|b₀| − Σ_{i∈F} |b_i|) ‖x‖`. -/
theorem norm_isometry_sum_ge {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Finset ι) (U : ι → E → E) (hU : ∀ i y, ‖U i y‖ = ‖y‖) (b₀ : ℝ) (b : ι → ℝ) (x : E) :
    (|b₀| - ∑ i ∈ F, |b i|) * ‖x‖ ≤ ‖b₀ • x + ∑ i ∈ F, b i • U i x‖ := by
  have htail : ‖∑ i ∈ F, b i • U i x‖ ≤ (∑ i ∈ F, |b i|) * ‖x‖ := by
    calc ‖∑ i ∈ F, b i • U i x‖ ≤ ∑ i ∈ F, ‖b i • U i x‖ := norm_sum_le _ _
      _ = ∑ i ∈ F, |b i| * ‖x‖ := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [norm_smul, hU, Real.norm_eq_abs]
      _ = (∑ i ∈ F, |b i|) * ‖x‖ := by rw [Finset.sum_mul]
  have hmain : ‖b₀ • x‖ ≤ ‖b₀ • x + ∑ i ∈ F, b i • U i x‖ + ‖∑ i ∈ F, b i • U i x‖ := by
    have := norm_sub_le (b₀ • x + ∑ i ∈ F, b i • U i x) (∑ i ∈ F, b i • U i x)
    rwa [add_sub_cancel_right] at this
  rw [norm_smul, Real.norm_eq_abs] at hmain
  nlinarith

/-- `9 < π² < 10`. -/
theorem pi_sq_bounds : (9 : ℝ) < Real.pi ^ 2 ∧ Real.pi ^ 2 < 10 := by
  have h3 : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have h315 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  constructor <;> nlinarith [Real.pi_pos]

/-- The diagonal-dominance constant: `(π²/6 − 1)(1 + 63/(16π²)) < 1`. -/
theorem tail_constant_lt_one :
    (Real.pi ^ 2 / 6 - 1) * (1 + 63 / (16 * Real.pi ^ 2)) < 1 := by
  obtain ⟨h9, h10⟩ := pi_sq_bounds
  have hp2 : 0 < Real.pi ^ 2 := by positivity
  rw [show (Real.pi ^ 2 / 6 - 1) * (1 + 63 / (16 * Real.pi ^ 2))
      = (16 * (Real.pi ^ 2) ^ 2 - 33 * Real.pi ^ 2 - 378) / (96 * Real.pi ^ 2) by
    field_simp; ring]
  rw [div_lt_one (by positivity)]
  nlinarith

/-- `Γ_ℝ(9/2) = (5/(4π)) Γ_ℝ(5/2)`. -/
theorem Gammaℝ_nine_halves :
    Complex.Gammaℝ (9 / 2) = 5 / (4 * (Real.pi : ℂ)) * Complex.Gammaℝ (5 / 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ : Complex.Gamma (9 / 4) = 5 / 4 * Complex.Gamma (5 / 4) := by
    rw [show (9 / 4 : ℂ) = 5 / 4 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
  have hcpow : (Real.pi : ℂ) ^ (-(9 / 2 : ℂ) / 2) =
      (Real.pi : ℂ) ^ (-(5 / 2 : ℂ) / 2) * (Real.pi : ℂ)⁻¹ := by
    rw [show -(9 / 2 : ℂ) / 2 = -(5 / 2 : ℂ) / 2 + (-1) by norm_num,
      Complex.cpow_add _ _ hpi, Complex.cpow_neg_one]
  rw [Complex.Gammaℝ, Complex.Gammaℝ, hcpow, show (9 / 2 : ℂ) / 2 = 9 / 4 by norm_num,
    show (5 / 2 : ℂ) / 2 = 5 / 4 by norm_num, hΓ]
  field_simp

/-- `Λ(s) = Γ_ℝ(s) ζ(s)` for `Re s > 0`. -/
theorem completed_eq_Gammaℝ_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos hs)]

/-- **The ξ ratio.** `ξ(9/2) ζ(5/2) = (21/(4π)) ζ(9/2) ξ(5/2)`, i.e.
`ξ(9/2)/ξ(5/2) = (21/(4π)) ζ(9/2)/ζ(5/2)`, with `ξ(s) = ½ s(s−1) Λ(s)`. -/
theorem xi_ratio :
    xi (9 / 2) * riemannZeta (5 / 2) =
      21 / (4 * (Real.pi : ℂ)) * riemannZeta (9 / 2) * xi (5 / 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [xi, xi, completed_eq_Gammaℝ_mul (by norm_num), completed_eq_Gammaℝ_mul (by norm_num),
    Gammaℝ_nine_halves]
  field_simp
  ring

end GppCriticalBPYCoercivity
