import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorWeightDuality

/-!
# Ordinary- versus dual-twistor helicity conventions

The rank-four degree reflection `k ↦ -k - 4` is an exact integer identity, but its
physical interpretation depends on whether the projective twistor side is kept fixed or
exchanged.

For a massless state of doubled helicity `n = 2h`, the standard split-signature
half-Fourier conventions used by Mason--Skinner are

* dual twistor space: degree `n - 2 = 2h - 2`;
* ordinary twistor space: degree `-n - 2 = -2h - 2`.

The full four-dimensional Fourier transform exchanges these two representations of the
same momentum-space helicity state.  By contrast, the same numerical reflection read as
a canonical/Serre degree reflection while staying on one fixed twistor side pairs the
bundle degree of helicity `h` with the degree assigned there to helicity `-h`.

Thus there are two exact but different statements:

1. cross-side Fourier: `PT* ↔ PT`, same physical helicity;
2. same-side canonical reflection: fixed `PT` (or fixed `PT*`), opposite-helicity degree.

Dropping the twistor-side tag conflates them.  This file formalizes that convention
distinction.  It does not formalize the analytic Fourier/Penrose transform, Serre duality
as a cohomological functor, or an orientation-reversal theorem.
-/

namespace GppTwistorRepresentationConvention

open GppTwistorWeightDuality

/-- Standard dual-twistor degree for doubled helicity `n = 2h`. -/
def dualTwistorPhysicalWeight (n : ℤ) : ℤ := n - 2

/-- Standard ordinary-twistor degree for doubled helicity `n = 2h`. -/
def ordinaryTwistorPhysicalWeight (n : ℤ) : ℤ := -n - 2

/-- Compatibility with the legacy arithmetic name `twistorWeight`. -/
theorem dual_weight_eq_legacy_twistorWeight (n : ℤ) :
    dualTwistorPhysicalWeight n = twistorWeight n := by
  rfl

/-- Compatibility with the legacy arithmetic name `dualTwistorWeight`. -/
theorem ordinary_weight_eq_legacy_dualTwistorWeight (n : ℤ) :
    ordinaryTwistorPhysicalWeight n = dualTwistorWeight n := by
  rfl

/-- Full rank-four Fourier reflection sends the dual-twistor representative of
helicity `n/2` to the ordinary-twistor representative of the same helicity. -/
theorem fourier_dual_to_ordinary_same_helicity (n : ℤ) :
    fourierWeight (dualTwistorPhysicalWeight n) =
      ordinaryTwistorPhysicalWeight n := by
  unfold fourierWeight dualTwistorPhysicalWeight ordinaryTwistorPhysicalWeight
  omega

/-- The inverse Fourier reflection sends the ordinary-twistor representative back to
the dual-twistor representative with the same helicity label. -/
theorem fourier_ordinary_to_dual_same_helicity (n : ℤ) :
    fourierWeight (ordinaryTwistorPhysicalWeight n) =
      dualTwistorPhysicalWeight n := by
  unfold fourierWeight dualTwistorPhysicalWeight ordinaryTwistorPhysicalWeight
  omega

/-- The identical integer reflection, when the dual-twistor convention is held fixed,
lands on the degree assigned on that same side to the opposite helicity.  This is the
degree arithmetic underlying a same-side canonical/Serre pairing, not the cross-side
Fourier interpretation. -/
theorem same_side_dual_reflection_has_opposite_helicity_degree (n : ℤ) :
    fourierWeight (dualTwistorPhysicalWeight n) =
      dualTwistorPhysicalWeight (-n) := by
  unfold fourierWeight dualTwistorPhysicalWeight
  omega

/-- Likewise on ordinary twistor space, keeping the side fixed turns the same degree
reflection into the opposite-helicity degree. -/
theorem same_side_ordinary_reflection_has_opposite_helicity_degree (n : ℤ) :
    fourierWeight (ordinaryTwistorPhysicalWeight n) =
      ordinaryTwistorPhysicalWeight (-n) := by
  unfold fourierWeight ordinaryTwistorPhysicalWeight
  omega

/-- The central convention identity: one reflected integer is simultaneously the
same-helicity degree on the opposite twistor side and the opposite-helicity degree on
the original side.  The two targets are physically different tagged representations
even though their bare integer degrees agree. -/
theorem reflected_degree_has_two_tagged_interpretations (n : ℤ) :
    fourierWeight (dualTwistorPhysicalWeight n) = ordinaryTwistorPhysicalWeight n ∧
    fourierWeight (dualTwistorPhysicalWeight n) = dualTwistorPhysicalWeight (-n) := by
  exact ⟨fourier_dual_to_ordinary_same_helicity n,
    same_side_dual_reflection_has_opposite_helicity_degree n⟩

/-- Numerical convention trap: an ordinary-twistor degree for helicity `n/2` equals
the dual-twistor degree assigned to helicity `-n/2`.  The equality of integers does not
identify the physical helicities because the twistor side has changed. -/
theorem ordinary_weight_looks_opposite_in_dual_convention (n : ℤ) :
    ordinaryTwistorPhysicalWeight n = dualTwistorPhysicalWeight (-n) := by
  unfold ordinaryTwistorPhysicalWeight dualTwistorPhysicalWeight
  omega

/-- The converse numerical convention identity. -/
theorem dual_weight_looks_opposite_in_ordinary_convention (n : ℤ) :
    dualTwistorPhysicalWeight n = ordinaryTwistorPhysicalWeight (-n) := by
  unfold ordinaryTwistorPhysicalWeight dualTwistorPhysicalWeight
  omega

/-- The two Fourier-related degrees form a same-helicity pair once their twistor
chirality is retained as part of the representation label. -/
theorem same_helicity_fourier_pair (n : ℤ) :
    fourierWeight (dualTwistorPhysicalWeight n) = ordinaryTwistorPhysicalWeight n ∧
    fourierWeight (ordinaryTwistorPhysicalWeight n) = dualTwistorPhysicalWeight n := by
  exact ⟨fourier_dual_to_ordinary_same_helicity n,
    fourier_ordinary_to_dual_same_helicity n⟩

/-- Graviton example: helicity `h = +2` has degree `+2` on dual twistor space and
`-6` on ordinary twistor space; cross-side Fourier exchanges them without changing the
helicity label. -/
theorem positive_graviton_same_state_weights :
    dualTwistorPhysicalWeight 4 = 2 ∧
    ordinaryTwistorPhysicalWeight 4 = -6 ∧
    fourierWeight (dualTwistorPhysicalWeight 4) = -6 := by
  norm_num [dualTwistorPhysicalWeight, ordinaryTwistorPhysicalWeight, fourierWeight]

/-- For `h = -2` the same numerical pair is reversed across the two twistor chiralities.
This demonstrates why the bare pair `2 ↔ -6` does not by itself determine a physical
helicity flip. -/
theorem negative_graviton_same_state_weights :
    dualTwistorPhysicalWeight (-4) = -6 ∧
    ordinaryTwistorPhysicalWeight (-4) = 2 ∧
    fourierWeight (dualTwistorPhysicalWeight (-4)) = 2 := by
  norm_num [dualTwistorPhysicalWeight, ordinaryTwistorPhysicalWeight, fourierWeight]

/-- Same-side graviton reading: on a fixed dual-twistor convention, the degree reflection
`2 -> -6` is exactly the degree change from `h=+2` to `h=-2`. -/
theorem positive_to_negative_graviton_same_side_degree :
    fourierWeight (dualTwistorPhysicalWeight 4) = dualTwistorPhysicalWeight (-4) := by
  exact same_side_dual_reflection_has_opposite_helicity_degree 4

end GppTwistorRepresentationConvention
