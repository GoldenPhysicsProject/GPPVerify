import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Laplace representation of the power-law Hankel matrix: positive semidefiniteness

Source: Astra, GPP-bridge `work/2026-10-22_astra_regulator_hankel_eigenvalue_scaling.md` (the limit
kernel `B_ij = π^{N/2} / (|w| (t_i + t_j)^{N/2})` is positive definite via the Laplace
representation `c*Bc = (π^a/(|w|Γ(a))) ∫₀^∞ x^{a-1} |Σ c_i e^{-t_i x}|² dx`). Daniel Toupin / Golden
Physics Project, with AI assistance from Astra (statement) and Claude Code (formalization).

* `laplace_hankel_identity`: for `a > 0`, positive times `t_i` and real weights `c_i`,
  `(Σ_{i,j} c_i c_j (1/(t_i + t_j))^a) · Γ(a) = ∫₀^∞ x^{a-1} (Σ_i c_i e^{-t_i x})² dx`.
* `hankel_psd`: hence `Σ_{i,j} c_i c_j (1/(t_i + t_j))^a ≥ 0`.

**Scope.** Positive semidefiniteness only. The strict positive definiteness for distinct `t_i`
(linear independence of distinct exponentials), the Poisson-summation limit, the eigenvalue scaling
`λ_min(M_ε) ~ ε^{-(N-1)/2} λ_min(B)`, and the numerical constants in the note are not formalized.
No claim about RH.
-/

set_option autoImplicit false

open MeasureTheory Set Real

namespace GppLaplaceHankelPSD

/-- Each term `x^{a-1} e^{-r x}` is integrable on `(0, ∞)`. -/
theorem integrableOn_term {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-(r * x))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r)
    (by linarith) one_pos hr
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

/-- The Laplace representation of the power-law Hankel form. -/
theorem laplace_hankel_identity {ι : Type*} (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 < t i)
    (c : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * (1 / (t i + t j)) ^ a) * Real.Gamma a =
      ∫ x in Ioi (0 : ℝ), x ^ (a - 1) * (∑ i ∈ s, c i * Real.exp (-(t i * x))) ^ 2 := by
  have hexp : ∀ x : ℝ, x ^ (a - 1) * (∑ i ∈ s, c i * Real.exp (-(t i * x))) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (c i * c j) * (x ^ (a - 1) * Real.exp (-((t i + t j) * x))) := by
    intro x
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : Real.exp (-(t i * x)) * Real.exp (-(t j * x)) = Real.exp (-((t i + t j) * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc x ^ (a - 1) * (c i * Real.exp (-(t i * x)) * (c j * Real.exp (-(t j * x))))
        = (c i * c j) * (x ^ (a - 1) * (Real.exp (-(t i * x)) * Real.exp (-(t j * x)))) := by ring
      _ = _ := by rw [this]
  simp_rw [hexp]
  have hint : ∀ i ∈ s, ∀ j ∈ s, IntegrableOn
      (fun x : ℝ => (c i * c j) * (x ^ (a - 1) * Real.exp (-((t i + t j) * x)))) (Ioi 0) :=
    fun i hi j hj => (integrableOn_term ha (add_pos (ht i hi) (ht j hj))).const_mul _
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hint i hi j hj))]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [integral_finsetSum _ (fun j hj => hint i hi j hj), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha (add_pos (ht i hi) (ht j hj))]
  ring

/-- The power-law Hankel form is positive semidefinite. -/
theorem hankel_psd {ι : Type*} (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 < t i)
    (c : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * (1 / (t i + t j)) ^ a := by
  have h := laplace_hankel_identity s t ht c ha
  have hI : 0 ≤ ∫ x in Ioi (0 : ℝ), x ^ (a - 1) * (∑ i ∈ s, c i * Real.exp (-(t i * x))) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (sq_nonneg _))
  rw [← h] at hI
  exact nonneg_of_mul_nonneg_left hI (Real.Gamma_pos_of_pos ha)

end GppLaplaceHankelPSD
