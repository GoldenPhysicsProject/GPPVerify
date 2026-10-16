import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Exact pole cancellation of the PNT continuum kernel

The two pole channels together have kernel `2 cosh ((x-y)/2)`.
Subtracting the PNT continuum kernel `exp (|x-y|/2)` leaves the positive
kernel `exp (-|x-y|/2)`. We give its one-sided half-density Gram representation.

This is a continuum theorem, on arbitrary finite sets without a window bound.
The signed difference between the actual von Mangoldt sum and the continuum
is NOT bounded here. In particular this file does not prove Weil positivity or RH.
-/

namespace GppContinuumPoleCancellation

open Real Set MeasureTheory

theorem pole_sub_continuum (x y : ℝ) :
    2 * cosh ((x - y) / 2) - exp (|x - y| / 2) = exp (-|x - y| / 2) := by
  rw [cosh_eq]
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    rw [neg_div]
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    simp only [neg_neg, neg_div]
    ring

/-- The half-density anchored at `x`, supported to its left. -/
noncomputable def halfDensity (x t : ℝ) : ℝ :=
  if t ≤ x then exp ((t - x) / 2) else 0

theorem halfDensity_product (x y : ℝ) :
    (fun t => halfDensity x t * halfDensity y t) =
      (Iic (min x y)).indicator (fun t => exp (-(x + y) / 2) * exp t) := by
  funext t
  by_cases hx : t ≤ x <;> by_cases hy : t ≤ y
  · simp only [halfDensity, hx, hy, if_true, indicator_of_mem (show t ∈ Iic (min x y) from le_min hx hy)]
    rw [← exp_add, ← exp_add]
    congr 1 <;> ring
  · simp [halfDensity, hx, hy, Set.indicator, le_min_iff]
  · simp [halfDensity, hx, hy, Set.indicator, le_min_iff]
  · simp [halfDensity, hx, hy, Set.indicator, le_min_iff]

theorem integrable_halfDensity_product (x y : ℝ) :
    Integrable (fun t => halfDensity x t * halfDensity y t) := by
  rw [halfDensity_product]
  apply (integrable_indicator_iff measurableSet_Iic).2
  exact (integrableOn_exp_Iic (min x y)).const_mul (exp (-(x + y) / 2))

/-- Exact Gram representation, with the normalization fixed at exponent `1/2`. -/
theorem halfDensity_gram (x y : ℝ) :
    (∫ t, halfDensity x t * halfDensity y t) = exp (-|x - y| / 2) := by
  rw [halfDensity_product, integral_indicator measurableSet_Iic, integral_const_mul,
    integral_exp_Iic, ← exp_add]
  congr 1
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Finite Gram positivity for arbitrary real locations and coefficients. -/
theorem completed_continuum_nonneg {n : ℕ} (x c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      (2 * cosh ((x i - x j) / 2) - exp (|x i - x j| / 2)) := by
  simp_rw [pole_sub_continuum, ← halfDensity_gram]
  have hint : ∀ i j : Fin n, Integrable
      (fun t => c i * c j * (halfDensity (x i) t * halfDensity (x j) t)) :=
    fun i j => (integrable_halfDensity_product (x i) (x j)).const_mul _
  have heq : (∑ i, ∑ j, c i * c j * ∫ t, halfDensity (x i) t * halfDensity (x j) t) =
      ∫ t, (∑ i, c i * halfDensity (x i) t) ^ 2 := by
    simp_rw [← integral_const_mul]
    have hinner : ∀ i : Fin n,
        (∑ j, ∫ t, c i * c j * (halfDensity (x i) t * halfDensity (x j) t)) =
        ∫ t, ∑ j, c i * c j * (halfDensity (x i) t * halfDensity (x j) t) := by
      intro i
      exact (integral_finsetSum _ (fun j _ => hint i j)).symm
    simp_rw [hinner]
    rw [← integral_finsetSum]
    · congr 1
      funext t
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro i _
      exact integrable_finsetSum _ (fun j _ => hint i j)
  rw [heq]
  exact integral_nonneg (fun t => sq_nonneg _)

/-- The same positivity for complex coefficients, retaining both real components. -/
theorem completed_continuum_complex_nonneg {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ ∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j).re *
      (2 * cosh ((x i - x j) / 2) - exp (|x i - x j| / 2)) := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
    add_mul, Finset.sum_add_distrib]
  exact add_nonneg (completed_continuum_nonneg x (fun i => (c i).re))
    (completed_continuum_nonneg x (fun i => (c i).im))

end GppContinuumPoleCancellation

#print axioms GppContinuumPoleCancellation.completed_continuum_nonneg
