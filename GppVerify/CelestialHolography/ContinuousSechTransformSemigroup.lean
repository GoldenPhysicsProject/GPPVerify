import Mathlib

/-!
# Continuous sech transform semigroup

This file isolates the exact Fourier-side algebra needed by the arbitrary-real
Gamma-chamber convolution program.  For a real chamber parameter `c`, define

`Phi_c(t) = sech(t/2)^(2c)`

using `Real.rpow`.  Since `cosh` is strictly positive, the base `sech(t/2)` is
strictly positive for every real `t`.  Hence the exponent-addition law gives

`Phi_{c+d}(t) = Phi_c(t) * Phi_d(t)`

for arbitrary real `c,d`; in particular for the probabilistic chamber range
`c,d > 0`.  This is the exact transform-side semigroup identity only.  It does
not by itself identify a real-line density or invoke Fourier uniqueness.
-/

namespace GppContinuousSechTransformSemigroup

/-- Positive real sech base appearing in the continuous chamber transform. -/
noncomputable def sechHalf (t : ℝ) : ℝ := 1 / Real.cosh (t / 2)

/-- Arbitrary-real chamber transform `sech(t/2)^(2c)`. -/
noncomputable def continuousChamberTransform (c t : ℝ) : ℝ :=
  Real.rpow (sechHalf t) (2 * c)

/-- The sech base is strictly positive on the whole real line. -/
theorem sechHalf_pos (t : ℝ) : 0 < sechHalf t := by
  unfold sechHalf
  positivity

/-- Every continuous chamber transform is strictly positive. -/
theorem continuousChamberTransform_pos (c t : ℝ) :
    0 < continuousChamberTransform c t := by
  unfold continuousChamberTransform
  exact Real.rpow_pos_of_pos (sechHalf_pos t) _

/-- The continuous chamber transform is normalized at zero frequency. -/
theorem continuousChamberTransform_zero (c : ℝ) :
    continuousChamberTransform c 0 = 1 := by
  unfold continuousChamberTransform sechHalf
  norm_num

/-- **Exact arbitrary-real transform semigroup.** -/
theorem continuousChamberTransform_add (c d t : ℝ) :
    continuousChamberTransform (c + d) t =
      continuousChamberTransform c t * continuousChamberTransform d t := by
  unfold continuousChamberTransform
  rw [show 2 * (c + d) = 2 * c + 2 * d by ring]
  exact Real.rpow_add (sechHalf_pos t) _ _

/-- Probabilistic chamber specialization: positive parameters are closed under
addition and obey the same exact transform semigroup law. -/
theorem continuousChamberTransform_add_of_pos
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t : ℝ) :
    0 < c + d ∧
      continuousChamberTransform (c + d) t =
        continuousChamberTransform c t * continuousChamberTransform d t := by
  constructor
  · exact add_pos hc hd
  · exact continuousChamberTransform_add c d t

end GppContinuousSechTransformSemigroup

#print axioms GppContinuousSechTransformSemigroup.continuousChamberTransform_add
#print axioms GppContinuousSechTransformSemigroup.continuousChamberTransform_add_of_pos
