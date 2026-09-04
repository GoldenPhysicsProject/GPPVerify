import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorFlagDuality
import GppVerify.CelestialHolography.TwistorWeightDuality

/-!
# Googly correspondence: incidence and homogeneity compatibility

This module combines the two exact pieces already established for the linear googly
programme:

1. annihilator duality reverses Penrose incidence flags `(1,2) -> (2,3)`;
2. four-dimensional Fourier duality sends twistor homogeneity `k` to `-k-4`, which
   is exactly the ordinary twistor weight of the opposite helicity.

The analytic/cohomological transform itself is deliberately abstract.  The goal here
is to state the minimum exact interface that a genuine Penrose/Fourier/Radon googly
operator must satisfy.  Once an operator satisfies the interface, helicity reversal is
not another hypothesis: it follows from the weight law.
-/

namespace GppGooglyCorrespondenceWeights

open GppTwistorWeightDuality

/-- Minimal abstract package for a correspondence transform between twistor data
of different homogeneous degrees.  `weight` records the projective homogeneity. -/
structure WeightedTransform (Tw TwDual : Type*) where
  weight : Tw -> Int
  dualWeight : TwDual -> Int
  transform : Tw -> TwDual
  fourierLaw : ∀ z, dualWeight (transform z) = fourierWeight (weight z)

/-- A source twistor datum has helicity label `n=2h` when its homogeneous degree is
`twistorWeight n = n-2`. -/
def HasHelicityWeight {Tw : Type*} (weight : Tw -> Int) (n : Int) (z : Tw) : Prop :=
  weight z = twistorWeight n

/-- Any transform satisfying the dimension-four Fourier law sends a source of
helicity weight `n` to the target degree for opposite helicity `-n`. -/
theorem weightedTransform_flips_helicity
    {Tw TwDual : Type*}
    (T : WeightedTransform Tw TwDual)
    (n : Int) (z : Tw)
    (hz : HasHelicityWeight T.weight n z) :
    T.dualWeight (T.transform z) = twistorWeight (-n) := by
  rw [T.fourierLaw, hz]
  exact fourierWeight_is_helicityFlip n

/-- Applying the four-dimensional weight reflection twice restores every degree. -/
theorem two_weight_dualities_return (k : Int) :
    fourierWeight (fourierWeight k) = k :=
  fourierWeight_involutive k

/-- In doubled-helicity variables, two helicity reversals return the original label. -/
theorem two_helicity_weight_flips_return (n : Int) :
    fourierWeight (twistorWeight (-n)) = twistorWeight n := by
  rw [fourierWeight_is_helicityFlip]
  simp

/-- Exact dimension pattern of the Penrose incidence correspondence in four
complex dimensions: a `(1,2)` flag dualizes to a `(2,3)` flag. -/
theorem incidence_dimension_pattern
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : GppTwistorFlagDuality.Flag12 (K:=K) (V:=V))
    (hV : Module.finrank K V = 4)
    (hline : Module.finrank K F.line = 1)
    (hplane : Module.finrank K F.plane = 2) :
    Module.finrank K (GppTwistorFlagDuality.annihilatorFlag F).planeAnn = 2 ∧
    Module.finrank K (GppTwistorFlagDuality.annihilatorFlag F).lineAnn = 3 :=
  GppTwistorFlagDuality.annihilatorFlag_dimensions F hV hline hplane

/-- A pointwise projective-twistor map cannot be obtained by annihilating a twistor
line alone: in dimension four, the annihilator of a one-dimensional subspace has
rank three, not rank one.  This is the finite-dimensional obstruction forcing the
googly construction into a correspondence/integral-transform category. -/
theorem pointwise_annihilator_obstruction
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (L : Submodule K V)
    (hV : Module.finrank K V = 4)
    (hL : Module.finrank K L = 1) :
    Module.finrank K L.dualAnnihilator = 3 ∧
    Module.finrank K L.dualAnnihilator ≠ 1 := by
  have h3 := GppTwistorFlagDuality.line_annihilator_finrank_three L hV hL
  exact ⟨h3, by omega⟩

/-! ## Abstract closure criterion

A full linearized googly transform must combine an incidence duality and a weighted
Fourier/Radon transform.  At this abstraction level, closure on weights is automatic;
closure on actual cohomology classes remains the analytic theorem to prove.
-/

structure LinearGooglyCandidate (Tw TwDual : Type*) where
  sourceWeight : Tw -> Int
  targetWeight : TwDual -> Int
  forward : Tw -> TwDual
  backward : TwDual -> Tw
  forwardWeight : ∀ z, targetWeight (forward z) = fourierWeight (sourceWeight z)
  backwardWeight : ∀ z, sourceWeight (backward z) = fourierWeight (targetWeight z)

/-- Any two-sided candidate automatically closes on projective homogeneity, even
before proving that `backward (forward z) = z` on cohomology classes. -/
theorem linearGooglyCandidate_weight_closure
    {Tw TwDual : Type*}
    (G : LinearGooglyCandidate Tw TwDual)
    (z : Tw) :
    G.sourceWeight (G.backward (G.forward z)) = G.sourceWeight z := by
  rw [G.backwardWeight, G.forwardWeight]
  exact fourierWeight_involutive (G.sourceWeight z)

end GppGooglyCorrespondenceWeights
