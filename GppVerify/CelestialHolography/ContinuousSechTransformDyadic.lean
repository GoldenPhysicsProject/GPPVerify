import GppVerify.CelestialHolography.ContinuousSechTransformSemigroup

/-!
# Dyadic divisibility of the continuous sech transform

This file isolates a transform-side infinite-divisibility consequence of the
arbitrary-real chamber semigroup.  It does not assert existence of a spatial
probability measure or identify a Gamma density; those still require the exact
Fourier/Barnes bridge and uniqueness.
-/

namespace GppContinuousSechTransformSemigroup

/-- Every transform member factors exactly into two identical half-parameter
members.  This is the dyadic square-root witness supplied by the continuous
parameter semigroup. -/
theorem continuousChamberTransform_half_square (c t : ℝ) :
    continuousChamberTransform c t =
      continuousChamberTransform (c / 2) t *
        continuousChamberTransform (c / 2) t := by
  rw [← continuousChamberTransform_add]
  congr 2
  ring

/-- Positive chamber parameters have positive half-parameters, and their
transform factors into two identical positive-parameter factors. -/
theorem continuousChamberTransform_half_square_of_pos
    {c : ℝ} (hc : 0 < c) (t : ℝ) :
    0 < c / 2 ∧
      continuousChamberTransform c t =
        continuousChamberTransform (c / 2) t *
          continuousChamberTransform (c / 2) t := by
  constructor
  · positivity
  · exact continuousChamberTransform_half_square c t

/-- Quartering gives an exact four-factor dyadic decomposition. -/
theorem continuousChamberTransform_quarter_fourfold (c t : ℝ) :
    continuousChamberTransform c t =
      (continuousChamberTransform (c / 4) t *
        continuousChamberTransform (c / 4) t) *
      (continuousChamberTransform (c / 4) t *
        continuousChamberTransform (c / 4) t) := by
  rw [continuousChamberTransform_half_square c t]
  rw [continuousChamberTransform_half_square (c / 2) t]
  congr 1 <;> ring_nf

end GppContinuousSechTransformSemigroup

#print axioms GppContinuousSechTransformSemigroup.continuousChamberTransform_half_square
#print axioms GppContinuousSechTransformSemigroup.continuousChamberTransform_half_square_of_pos
#print axioms GppContinuousSechTransformSemigroup.continuousChamberTransform_quarter_fourfold
