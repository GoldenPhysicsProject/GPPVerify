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

/-- Complex dimension of projective twistor space `CP^3`. -/
def projectiveTwistorDim : ℤ := 3

/-- Canonical degree of `CP^3`: `-(dim+1)=-4`. -/
def canonicalDegree : ℤ := -(projectiveTwistorDim + 1)

theorem canonicalDegree_eq_neg_four : canonicalDegree = -4 := by
  norm_num [canonicalDegree, projectiveTwistorDim]

/-- Degree reflection induced by the canonical `O(-4)` shift. -/
def serreWeight (k : ℤ) : ℤ := canonicalDegree - k

/-- On `CP^3`, the canonical reflection is exactly `k -> -k-4`. -/
theorem serreWeight_eq_fourierWeight (k : ℤ) :
    serreWeight k = fourierWeight k := by
  norm_num [serreWeight, canonicalDegree, projectiveTwistorDim, fourierWeight]

/-- The canonical degree reflection is involutive. -/
theorem serreWeight_involutive (k : ℤ) :
    serreWeight (serreWeight k) = k := by
  rw [serreWeight_eq_fourierWeight, serreWeight_eq_fourierWeight]
  exact fourierWeight_involutive k

/-- Applied to twistor helicity weight, the canonical reflection gives opposite helicity. -/
theorem serreWeight_is_helicityFlip (n : ℤ) :
    serreWeight (twistorWeight n) = twistorWeight (-n) := by
  rw [serreWeight_eq_fourierWeight]
  exact fourierWeight_is_helicityFlip n

/-- The unique self-dual degree under the canonical reflection is `-2`. -/
theorem serreWeight_fixed_iff (k : ℤ) :
    serreWeight k = k ↔ k = -2 := by
  rw [serreWeight_eq_fourierWeight]
  exact fourierWeight_fixed_iff k

/-- Gauge-field helicity pair: `O(0)` and `O(-4)` are canonical dual degrees. -/
theorem gauge_weight_pair : serreWeight 0 = -4 ∧ serreWeight (-4) = 0 := by
  norm_num [serreWeight, canonicalDegree, projectiveTwistorDim]

/-- Graviton helicity pair: `O(2)` and `O(-6)` are canonical dual degrees. -/
theorem graviton_weight_pair : serreWeight 2 = -6 ∧ serreWeight (-6) = 2 := by
  norm_num [serreWeight, canonicalDegree, projectiveTwistorDim]

end GppTwistorCanonicalShift
