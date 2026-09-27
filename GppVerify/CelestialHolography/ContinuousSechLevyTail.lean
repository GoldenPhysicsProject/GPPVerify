import GppVerify.CelestialHolography.ContinuousSechLevyKernel

/-!
# Continuous sech Lévy inverse-square tail bounds

The globally certified quadratic estimate

  `|x|^2 * nu_c(x) ≤ c / pi`

already contains an integrable tail majorant.  Away from the origin it implies

  `nu_c(x) ≤ c / (pi * |x|^2)`,

so the compensated kernel satisfies

  `K_c(t,x) ≤ 2c / (pi * |x|^2)`.

This avoids requiring an exponential-tail estimate merely to prove integrability:
the inverse-square majorant is sufficient on `|x| ≥ 1`, while the existing
uniform bound controls a neighbourhood of the origin.
-/

namespace GppContinuousSechLevyTail

open GppContinuousSechLevyKernel

/-- Away from zero, the candidate Lévy density has the inverse-square majorant
already encoded in the global quadratic estimate. -/
theorem levyDensity_le_inv_sq {c x : ℝ} (hc : 0 ≤ c) (hx : x ≠ 0) :
    levyDensity c x ≤ c / (Real.pi * |x| ^ 2) := by
  have hquad := sq_abs_mul_levyDensity_le (c := c) (x := x) hc
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hx2 : 0 < |x| ^ 2 := sq_pos_of_pos hxabs
  have hdiv := (div_le_div_iff_of_pos_right hx2).2 hquad
  calc
    levyDensity c x = (|x| ^ 2 * levyDensity c x) / |x| ^ 2 := by
      field_simp [ne_of_gt hx2]
    _ ≤ (c / Real.pi) / |x| ^ 2 := hdiv
    _ = c / (Real.pi * |x| ^ 2) := by
      field_simp [Real.pi_ne_zero, ne_of_gt hx2]
      <;> ring

/-- The compensated kernel inherits an inverse-square tail majorant away from
zero.  Together with `compensatedLevyKernel_le_uniform`, this gives the natural
piecewise integrable domination for the Lévy exponent. -/
theorem compensatedLevyKernel_le_inv_sq {c t x : ℝ} (hc : 0 ≤ c) (hx : x ≠ 0) :
    compensatedLevyKernel c t x ≤ 2 * c / (Real.pi * |x| ^ 2) := by
  have hkernel := compensatedLevyKernel_le_two_mul_density (c := c) (t := t) (x := x) hc
  have hdensity := levyDensity_le_inv_sq (c := c) (x := x) hc hx
  calc
    compensatedLevyKernel c t x ≤ 2 * levyDensity c x := hkernel
    _ ≤ 2 * (c / (Real.pi * |x| ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hdensity (by norm_num)
    _ = 2 * c / (Real.pi * |x| ^ 2) := by ring

end GppContinuousSechLevyTail

#print axioms GppContinuousSechLevyTail.levyDensity_le_inv_sq
#print axioms GppContinuousSechLevyTail.compensatedLevyKernel_le_inv_sq
