import Mathlib.Tactic

/-!
# External scale invariance of the four-point rational factor

The closed adjacent-MHV rational remainder is proportional to `s/t` times a
scale-invariant helicity phase. This file records the Mandelstam part of the
homogeneity statement exactly.
-/

namespace GppFourPointRationalHomogeneity

/-- The dimensionless Mandelstam ratio is unchanged when both invariants are
scaled by the same nonzero quadratic momentum factor. -/
theorem ratio_scale_invariant
    {s t lam : ℂ} (ht : t ≠ 0) (hlam : lam ≠ 0) :
    (lam ^ 2 * s) / (lam ^ 2 * t) = s / t := by
  field_simp [ht, hlam]
  ring

/-- Real version, convenient for physical Mandelstam invariants. -/
theorem ratio_scale_invariant_real
    {s t lam : ℝ} (ht : t ≠ 0) (hlam : lam ≠ 0) :
    (lam ^ 2 * s) / (lam ^ 2 * t) = s / t := by
  field_simp [ht, hlam]
  ring

/-- Multiplication by an arbitrary fixed helicity factor preserves the scale invariance. -/
theorem rational_factor_scale_invariant
    {s t lam H : ℂ} (ht : t ≠ 0) (hlam : lam ≠ 0) :
    ((lam ^ 2 * s) / (lam ^ 2 * t)) * H = (s / t) * H := by
  rw [ratio_scale_invariant ht hlam]

end GppFourPointRationalHomogeneity

#print axioms GppFourPointRationalHomogeneity.ratio_scale_invariant
#print axioms GppFourPointRationalHomogeneity.rational_factor_scale_invariant
