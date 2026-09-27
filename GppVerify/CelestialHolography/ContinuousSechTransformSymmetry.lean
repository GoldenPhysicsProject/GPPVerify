import GppVerify.CelestialHolography.ContinuousSechTransformSemigroup

/-!
# Continuous sech transform symmetry

This file adds the reflection property needed when the arbitrary-real chamber
transform is interpreted as a characteristic/Fourier transform.  The result is
purely transform-side: it uses only evenness of `cosh` and does not assert the
existence or uniqueness of a corresponding real-line density.
-/

namespace GppContinuousSechTransformSemigroup

/-- The positive sech base is even in frequency. -/
theorem sechHalf_neg (t : ℝ) : sechHalf (-t) = sechHalf t := by
  unfold sechHalf
  rw [show (-t) / 2 = -(t / 2) by ring]
  rw [Real.cosh_neg]

/-- **Exact reflection symmetry of every arbitrary-real chamber transform.** -/
theorem continuousChamberTransform_neg (c t : ℝ) :
    continuousChamberTransform c (-t) = continuousChamberTransform c t := by
  unfold continuousChamberTransform
  rw [sechHalf_neg]

/-- The zero-parameter member of the transform semigroup is identically one. -/
theorem continuousChamberTransform_zero_param (t : ℝ) :
    continuousChamberTransform 0 t = 1 := by
  unfold continuousChamberTransform
  norm_num

end GppContinuousSechTransformSemigroup

#print axioms GppContinuousSechTransformSemigroup.continuousChamberTransform_neg
#print axioms GppContinuousSechTransformSemigroup.continuousChamberTransform_zero_param
