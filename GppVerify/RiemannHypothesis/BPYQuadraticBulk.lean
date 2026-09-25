import GppVerify.QuantumGravity.SinhWeierstrassProduct
import GppVerify.QuantumGravity.StefanBoltzmannFamily
import Mathlib.Tactic

/-!
# BPY quadratic bulk from the sinh product

The BPY Gaussian quadratic field has finite Laplace factors of the form

  product_n (1 + lambda^2 / n^2)^(-2).

This file records the zero-independent analytic core: the finite products converge to

  (pi*lambda / sinh(pi*lambda))^2,

the square of the already-formalized Planck spectral weight.  The probabilistic
identification with a sum of shape-two Gamma variables is separate; the infinite-product
identity itself is unconditional and depends only on the certified sinh Weierstrass
product.
-/

namespace GppBPYQuadraticBulk

open Filter Topology
open GppStefanBoltzmann

/-- The finite BPY quadratic bulk product. -/
noncomputable def finiteBulk (lam : ℝ) (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n,
      ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2))⁻¹ ^ 2

/-- The limiting BPY quadratic bulk weight, in the exact reciprocal form produced by
the sinh Weierstrass limit. -/
noncomputable def bulkLimit (lam : ℝ) : ℝ :=
  (Real.sinh (Real.pi * lam) / (Real.pi * lam))⁻¹ ^ 2

/-- Away from the removable origin, the reciprocal sinh form is exactly the square of
the Planck weight already used elsewhere in the project. -/
theorem bulkLimit_eq_planck_sq {lam : ℝ} (hlam : lam ≠ 0) :
    bulkLimit lam = (P lam) ^ 2 := by
  have hpi : Real.pi * lam ≠ 0 := mul_ne_zero Real.pi_ne_zero hlam
  have hsinh : Real.sinh (Real.pi * lam) ≠ 0 :=
    Real.sinh_ne_zero.mpr hpi
  unfold bulkLimit P
  field_simp

/-- For nonzero spectral parameter, the finite positive Gamma-product converges exactly
to the square of the Planck/sinh weight. -/
theorem tendsto_finiteBulk {lam : ℝ} (hlam : lam ≠ 0) :
    Tendsto (finiteBulk lam) atTop (𝓝 (bulkLimit lam)) := by
  have hpi : Real.pi * lam ≠ 0 := mul_ne_zero Real.pi_ne_zero hlam
  have hprod0 := (GppSinhWeierstrass.tendsto_prod_one_add_sq_div lam).div_const
    (Real.pi * lam)
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ∏ j ∈ Finset.range n,
            ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2))
        atTop
        (𝓝 (Real.sinh (Real.pi * lam) / (Real.pi * lam))) := by
    have hcongr : ∀ n : ℕ,
        (Real.pi * lam *
          ∏ j ∈ Finset.range n,
            ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2)) /
            (Real.pi * lam)
        =
          ∏ j ∈ Finset.range n,
            ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2) := by
      intro n
      field_simp
    simp_rw [hcongr] at hprod0
    exact hprod0
  have hlim_pos : 0 < Real.sinh (Real.pi * lam) / (Real.pi * lam) := by
    rcases hlam.lt_or_gt with hneg | hpos
    · have hpineg : Real.pi * lam < 0 := by nlinarith [Real.pi_pos]
      have hsneg : Real.sinh (Real.pi * lam) < 0 := Real.sinh_neg_iff.mpr hpineg
      exact div_pos_of_neg_of_neg hsneg hpineg
    · have hpipos : 0 < Real.pi * lam := by positivity
      have hspos : 0 < Real.sinh (Real.pi * lam) := Real.sinh_pos_iff.mpr hpipos
      exact div_pos hspos hpipos
  have hinv :=
    hprod.inv₀ hlim_pos.ne'
  have hsq := hinv.pow 2
  exact hsq

/-- Every finite BPY bulk product is nonnegative. -/
theorem finiteBulk_nonneg (lam : ℝ) (n : ℕ) :
    0 ≤ finiteBulk lam n := by
  unfold finiteBulk
  positivity

end GppBPYQuadraticBulk
