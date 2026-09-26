import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorWeightDuality

/-!
# Canonical-bundle shift behind twistor helicity duality

For projective twistor space `CP^3`, the canonical bundle is `O(-4)`.  Serre
duality therefore pairs line-bundle degree `k` with degree `-k-4`.  The same
integer reflection appears in the four-complex-dimensional non-projective
Fourier transform.  This file formalizes the exact degree/helicity arithmetic;
it does not formalize Serre duality itself.
-/

namespace GppTwistorCanonicalShift

open GppTwistorWeightDuality

def projectiveTwistorDim : ℤ := 3
def canonicalDegree : ℤ := -(projectiveTwistorDim + 1)

theorem canonicalDegree_eq_neg_four : canonicalDegree = -4 := by
  norm_num [canonicalDegree, projectiveTwistorDim]

def serreWeight (k : ℤ) : ℤ := canonicalDegree - k

theorem serreWeight_eq_fourierWeight (k : ℤ) :
    serreWeight k = fourierWeight k := by
  simp [serreWeight, canonicalDegree, projectiveTwistorDim, fourierWeight]
  ring

theorem serreWeight_involutive (k : ℤ) :
    serreWeight (serreWeight k) = k := by
  rw [serreWeight_eq_fourierWeight, serreWeight_eq_fourierWeight]
  exact fourierWeight_involutive k

theorem serreWeight_is_helicityFlip (n : ℤ) :
    serreWeight (twistorWeight n) = twistorWeight (-n) := by
  rw [serreWeight_eq_fourierWeight]
  exact fourierWeight_is_helicityFlip n

theorem serreWeight_fixed_iff (k : ℤ) :
    serreWeight k = k ↔ k = -2 := by
  rw [serreWeight_eq_fourierWeight]
  exact fourierWeight_fixed_iff k

theorem gauge_weight_pair : serreWeight 0 = -4 ∧ serreWeight (-4) = 0 := by
  norm_num [serreWeight, canonicalDegree, projectiveTwistorDim]

theorem graviton_weight_pair : serreWeight 2 = -6 ∧ serreWeight (-6) = 2 := by
  norm_num [serreWeight, canonicalDegree, projectiveTwistorDim]

end GppTwistorCanonicalShift
