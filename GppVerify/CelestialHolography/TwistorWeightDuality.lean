import Mathlib.Tactic

/-!
# Twistor/dual-twistor homogeneity duality

For a four-complex-dimensional non-projective twistor variable, Fourier duality
carries a homogeneous distribution of degree `k` to degree `-k-4`.  This file
formalizes the exact weight arithmetic separately from the analytic theorem that
the Fourier transform exists on the chosen distribution/cohomology class.

Write `n = 2h` for doubled helicity.  The ordinary Penrose-transform weight is

  k = 2h - 2 = n - 2.

The four-dimensional Fourier weight is therefore

  -k - 4 = -n - 2,

which is exactly the ordinary twistor weight associated with opposite helicity
`-h`.  On dual twistor space this is also the standard homogeneity for the same
physical helicity `h`.  Thus the numerical weight shift needed by a googly/helicity
exchange is not an extra assumption: it is the universal dimension-four Fourier
shift.  Identifying the dual-twistor target with the opposite-orientation twistor
geometry is a separate geometric step.
-/

namespace GppTwistorWeightDuality

/-- Twistor homogeneity in terms of doubled helicity `n = 2h`. -/
def twistorWeight (n : ℤ) : ℤ := n - 2

/-- Standard dual-twistor homogeneity for the same doubled helicity. -/
def dualTwistorWeight (n : ℤ) : ℤ := -n - 2

/-- Fourier transform in complex dimension four changes homogeneity `k` to `-k-4`. -/
def fourierWeight (k : ℤ) : ℤ := -k - 4

/-- The dimension-four Fourier weight reflection is an involution. -/
theorem fourierWeight_involutive (k : ℤ) :
    fourierWeight (fourierWeight k) = k := by
  simp [fourierWeight]

/-- Fourier duality sends the ordinary twistor weight to the standard dual-twistor weight. -/
theorem fourierWeight_twistor_eq_dual (n : ℤ) :
    fourierWeight (twistorWeight n) = dualTwistorWeight n := by
  simp [fourierWeight, twistorWeight, dualTwistorWeight]
  ring

/-- The resulting dual-twistor weight is numerically the ordinary twistor weight
of opposite helicity. -/
theorem dualWeight_eq_oppositeHelicityWeight (n : ℤ) :
    dualTwistorWeight n = twistorWeight (-n) := by
  simp [dualTwistorWeight, twistorWeight]
  ring

/-- Combined form: four-dimensional Fourier duality implements the exact
homogeneity shift required by helicity reversal. -/
theorem fourierWeight_is_helicityFlip (n : ℤ) :
    fourierWeight (twistorWeight n) = twistorWeight (-n) := by
  rw [fourierWeight_twistor_eq_dual, dualWeight_eq_oppositeHelicityWeight]

/-- The scalar weight `-2` is the unique fixed point of `k -> -k-4` over integers. -/
theorem fourierWeight_fixed_iff (k : ℤ) :
    fourierWeight k = k ↔ k = -2 := by
  simp [fourierWeight]
  omega

/-- Correspondingly zero helicity is fixed by the weight duality. -/
theorem scalar_weight_fixed : fourierWeight (twistorWeight 0) = twistorWeight 0 := by
  norm_num [fourierWeight, twistorWeight]

/-- Photon weights: `h=+1` (`n=2`) has twistor weight 0 and Fourier-dual weight -4. -/
theorem photon_weight_pair :
    twistorWeight 2 = 0 ∧ fourierWeight (twistorWeight 2) = -4 := by
  norm_num [twistorWeight, fourierWeight]

/-- Graviton weights: `h=+2` (`n=4`) has twistor weight +2 and Fourier-dual weight -6. -/
theorem graviton_weight_pair :
    twistorWeight 4 = 2 ∧ fourierWeight (twistorWeight 4) = -6 := by
  norm_num [twistorWeight, fourierWeight]

end GppTwistorWeightDuality
