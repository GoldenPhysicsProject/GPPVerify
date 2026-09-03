import Mathlib.Tactic
import GppVerify.CelestialHolography.SplitSignatureHodgeGrassmannian
import GppVerify.CelestialHolography.TwistorCanonicalShift

/-!
# Ambient four-dimensional duality spine

This file isolates an exact piece of the proposed googly geometry which does not depend
on a twistor action.

For a four-dimensional ambient twistor vector space, the same alternating 4-form
`epsilon` has two standard descendants:

* on `Λ²`, wedge product followed by `epsilon` gives the Klein/Pluecker pairing;
* on projective twistor space `P(V) = CP^3`, contraction of `epsilon` with the Euler
  vector gives the weight-4 projective volume form, hence canonical degree `-4`.

The geometric identification of these two descendants is standard exterior algebra;
here we formalize the coordinate/arithmetic consequences used by the GPP googly
programme.  We deliberately do not claim that this alone constructs the analytic
Penrose/Fourier intertwiner.
-/

namespace GppAmbientFourDualitySpine

open GppGrassmannianGooglyDecomposition
open GppSplitSignatureHodgeGrassmannian
open GppTwistorCanonicalShift

/-- Ambient twistor-vector-space dimension. -/
def ambientRank : ℤ := 4

/-- Projectivization lowers dimension by one. -/
def projectiveRank : ℤ := ambientRank - 1

/-- Middle exterior degree in ambient dimension four. -/
def middleExteriorDegree : ℤ := ambientRank / 2

/-- The canonical degree of `P(C^4)=CP^3` is minus the ambient rank. -/
def canonicalDegreeFromAmbient : ℤ := -ambientRank

theorem projectiveRank_eq_three : projectiveRank = 3 := by
  norm_num [projectiveRank, ambientRank]

theorem middleExteriorDegree_eq_two : middleExteriorDegree = 2 := by
  norm_num [middleExteriorDegree, ambientRank]

theorem canonicalDegreeFromAmbient_eq_neg_four : canonicalDegreeFromAmbient = -4 := by
  norm_num [canonicalDegreeFromAmbient, ambientRank]

theorem canonicalDegree_agrees_with_twistor :
    canonicalDegreeFromAmbient = canonicalDegree := by
  norm_num [canonicalDegreeFromAmbient, ambientRank,
    canonicalDegree, projectiveTwistorDim]

/-- Polarization of the Klein quadratic form.  In an oriented basis this is the
coordinate form of the pairing obtained from `alpha ∧ beta ∈ Λ⁴ V` and a chosen
volume form. -/
def epsilonPair (p q : P6) : ℝ :=
  p.p01 * q.p23 + p.p23 * q.p01
  - p.p02 * q.p13 - p.p13 * q.p02
  + p.p03 * q.p12 + p.p12 * q.p03

/-- The epsilon pairing is symmetric because degree-two forms commute under wedge. -/
theorem epsilonPair_symm (p q : P6) : epsilonPair p q = epsilonPair q p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  simp [epsilonPair]
  ring

/-- On the diagonal, the epsilon pairing is twice the Klein quadratic form. -/
theorem epsilonPair_self (p : P6) : epsilonPair p p = 2 * kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [epsilonPair, kleinQ]
  ring

/-- The split Hodge complement preserves the epsilon/Klein pairing. -/
theorem epsilonPair_splitStar (p q : P6) :
    epsilonPair (splitStar p) (splitStar q) = epsilonPair p q := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  simp [epsilonPair, splitStar]
  ring

/-- Canonical/Serre weight reflection derived from the ambient rank. -/
def ambientDualWeight (k : ℤ) : ℤ := canonicalDegreeFromAmbient - k

theorem ambientDualWeight_eq_fourierWeight (k : ℤ) :
    ambientDualWeight k = fourierWeight k := by
  norm_num [ambientDualWeight, canonicalDegreeFromAmbient, ambientRank, fourierWeight]

/-- The ambient-rank duality is involutive. -/
theorem ambientDualWeight_involutive (k : ℤ) :
    ambientDualWeight (ambientDualWeight k) = k := by
  simp [ambientDualWeight]

/-- The same rank-four duality exchanges the two graviton homogeneities. -/
theorem ambient_graviton_pair :
    ambientDualWeight 2 = -6 ∧ ambientDualWeight (-6) = 2 := by
  norm_num [ambientDualWeight, canonicalDegreeFromAmbient, ambientRank]

/-- Likewise for the two gauge-field homogeneities. -/
theorem ambient_gauge_pair :
    ambientDualWeight 0 = -4 ∧ ambientDualWeight (-4) = 0 := by
  norm_num [ambientDualWeight, canonicalDegreeFromAmbient, ambientRank]

/-- Under the standard Penrose weight convention `k = n - 2` for doubled helicity
`n=2h`, ambient duality reverses helicity. -/
theorem ambientDualWeight_is_helicityFlip (n : ℤ) :
    ambientDualWeight (twistorWeight n) = twistorWeight (-n) := by
  rw [ambientDualWeight_eq_fourierWeight]
  exact fourierWeight_is_helicityFlip n

end GppAmbientFourDualitySpine
