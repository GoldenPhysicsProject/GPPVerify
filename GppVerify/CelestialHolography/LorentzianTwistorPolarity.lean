import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# Lorentzian twistor polarity

On Lorentzian twistor space the conformal group `SU(2,2)` preserves a Hermitian
form of signature `(2,2)`.  After a choice of diagonal basis this gives the
anti-linear polarity

  (z0,z1,z2,z3) |-> (conj z0, conj z1, -conj z2, -conj z3),

which identifies a twistor with a dual twistor on the Lorentzian real structure.
This file isolates the exact finite-dimensional algebra.  It does NOT claim that
this anti-holomorphic polarity alone is the googly transform on Penrose cohomology.
-/

namespace GppLorentzianTwistorPolarity

abbrev C4 := ℂ × ℂ × ℂ × ℂ

/-- Scalar multiplication on the explicit four-coordinate model. -/
def csmul (a : ℂ) (z : C4) : C4 :=
  (a*z.1, a*z.2.1, a*z.2.2.1, a*z.2.2.2)

/-- `SU(2,2)`-adapted anti-linear polarity in a diagonal `(2,2)` basis. -/
def polarity (z : C4) : C4 :=
  (starRingEnd ℂ z.1,
   starRingEnd ℂ z.2.1,
   - starRingEnd ℂ z.2.2.1,
   - starRingEnd ℂ z.2.2.2)

/-- The polarity is anti-linear in the scalar: `P(a z) = conj(a) P(z)`. -/
theorem polarity_csmul (a : ℂ) (z : C4) :
    polarity (csmul a z) = csmul (starRingEnd ℂ a) (polarity z) := by
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [polarity, csmul]

/-- The chosen polarity squares to the identity on the non-projective twistor space. -/
theorem polarity_involutive (z : C4) : polarity (polarity z) = z := by
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [polarity]

/-- Hence the polarity is injective. -/
theorem polarity_injective : Function.Injective polarity := by
  intro x y h
  have h' := congrArg polarity h
  simpa [polarity_involutive] using h'

/-- It is also surjective, with itself as inverse. -/
theorem polarity_surjective : Function.Surjective polarity := by
  intro z
  exact ⟨polarity z, polarity_involutive z⟩

/-- Projective compatibility: nonzero scalar rescaling is sent to conjugate
rescaling.  Thus the anti-linear polarity descends to projective twistor space. -/
theorem polarity_projective_compatibility (a : ℂ) (z : C4) :
    polarity (csmul a z) = csmul (starRingEnd ℂ a) (polarity z) :=
  polarity_csmul a z

/-- The diagonal signature signs square away, which is the finite-coordinate
reason the Lorentzian twistor polarity is order two rather than order four. -/
theorem polarity_four (z : C4) :
    polarity (polarity (polarity (polarity z))) = z := by
  rw [polarity_involutive, polarity_involutive]

end GppLorentzianTwistorPolarity
