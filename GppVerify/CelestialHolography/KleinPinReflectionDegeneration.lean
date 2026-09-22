import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbientFourDualitySpine
import GppVerify.CelestialHolography.EinsteinInfinityTwistorFamily

/-!
# Non-null Klein reflection and its flat degeneration

The epsilon pairing on `Λ²V` is the split `(3,3)` conformal/Klein bilinear form.  For a
non-null vector `q` the ordinary orthogonal reflection in the hyperplane `q^perp` is

  r_q(p) = p - (B(p,q)/Q(q)) q,

because `B(q,q)=2 Q(q)`.

This file proves directly in the six Plucker coordinates that `r_q`

* sends `q` to `-q`;
* fixes `q^perp` pointwise;
* is involutive;
* preserves the Klein quadratic form.

For the cosmological infinity-twistor family

  I_Lambda=(Lambda,0,0,0,0,1),

with `Lambda != 0`, the reflection acts only in the `(p01,p23)` hyperbolic plane:

  p01 |-> -Lambda p23,
  p23 |-> -p01/Lambda,

while fixing the other four Plucker coordinates.  The determinant of this active 2x2
block is exactly `-1`, so the corresponding six-dimensional linear reflection lies in
the disconnected orthogonal component rather than the identity component.

Standard Clifford/Pin theory says a non-null Clifford vector lifts precisely this
orthogonal reflection, and odd Clifford multiplication exchanges the two half-spinor
modules.  That group-theoretic identification is an external theorem; internally we
have independently proved the vector-side reflection here and the spinor-side
`V <-> V*` Clifford isomorphism in `EinsteinInfinityTwistorFamily`.

At `Lambda=0`, `Q(I_0)=0`: the reflection formula is no longer defined, while the
spinor-side Clifford map degenerates to the exact nilpotent flat-infinity complex.
This is the algebraic rank-drop at the heart of the asymptotically-flat googly problem.
-/

namespace GppKleinPinReflectionDegeneration

open GppGrassmannianGooglyDecomposition
open GppAmbientFourDualitySpine
open GppEinsteinInfinityTwistorFamily

/-- Coordinate scalar multiplication on the six-dimensional Klein module. -/
def scaleP6 (a : ℝ) (p : P6) : P6 :=
  ⟨a*p.p01, a*p.p02, a*p.p03, a*p.p12, a*p.p13, a*p.p23⟩

/-- Coordinate subtraction on the Klein module. -/
def subP6 (p q : P6) : P6 :=
  ⟨p.p01-q.p01, p.p02-q.p02, p.p03-q.p03,
   p.p12-q.p12, p.p13-q.p13, p.p23-q.p23⟩

/-- Orthogonal reflection in a non-null Klein vector.  The definition is total as a
coordinate function; geometric theorems below assume `Q(q) != 0`. -/
def kleinReflection (q p : P6) : P6 :=
  subP6 p (scaleP6 (epsilonPair p q / kleinQ q) q)

/-- Negation on the Klein coordinate module. -/
def negP6 (p : P6) : P6 := scaleP6 (-1) p

/-- Reflection sends its non-null normal to its negative. -/
theorem kleinReflection_normal
    (q : P6) (hq : kleinQ q ≠ 0) :
    kleinReflection q q = negP6 q := by
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  apply P6.ext <;>
    simp [kleinReflection, subP6, scaleP6, negP6,
      epsilonPair, kleinQ] <;>
    field_simp [hq] <;> ring

/-- Every vector orthogonal to the reflection normal is fixed pointwise. -/
theorem kleinReflection_fixes_orthogonal
    (q p : P6) (hpq : epsilonPair p q = 0) :
    kleinReflection q p = p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  apply P6.ext <;>
    simp [kleinReflection, subP6, scaleP6, hpq]

/-- Reflection reverses the bilinear component along its non-null normal. -/
theorem epsilonPair_reflection_normal
    (q p : P6) (hq : kleinQ q ≠ 0) :
    epsilonPair (kleinReflection q p) q = - epsilonPair p q := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  simp [kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hq ⊢
  field_simp [hq]
  ring

/-- The non-null Klein reflection is involutive. -/
theorem kleinReflection_involutive
    (q p : P6) (hq : kleinQ q ≠ 0) :
    kleinReflection q (kleinReflection q p) = p := by
  have hpair := epsilonPair_reflection_normal q p hq
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  apply P6.ext <;>
    simp [kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hq hpair ⊢ <;>
    field_simp [hq] <;> ring

/-- The reflection preserves the Klein quadratic form. -/
theorem kleinQ_kleinReflection
    (q p : P6) (hq : kleinQ q ≠ 0) :
    kleinQ (kleinReflection q p) = kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  simp [kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hq ⊢
  field_simp [hq]
  ring

/-- Pairing with `I_Lambda` is the hyperbolic combination `p01 + Lambda*p23`. -/
theorem epsilonPair_infinityTwistor (Lambda : ℝ) (p : P6) :
    epsilonPair p (infinityTwistor Lambda) = p.p01 + Lambda*p.p23 := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [epsilonPair, infinityTwistor]
  ring

/-- Explicit coordinates of the nonzero-cosmological-parameter reflection. -/
theorem infinityTwistor_reflection_coordinates
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) (p : P6) :
    kleinReflection (infinityTwistor Lambda) p =
      ⟨-Lambda*p.p23, p.p02, p.p03, p.p12, p.p13, -p.p01/Lambda⟩ := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  apply P6.ext <;>
    simp [kleinReflection, subP6, scaleP6, epsilonPair,
      infinityTwistor, kleinQ] <;>
    field_simp [hLambda] <;> ring

/-- The active `(p01,p23)` block of the infinity-twistor reflection has determinant -1. -/
theorem infinityTwistor_reflection_activeBlock_det
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) :
    (0:ℝ)*0 - (-Lambda)*(-1/Lambda) = -1 := by
  field_simp [hLambda]

/-- The infinity-twistor reflection sends `I_Lambda` itself to `-I_Lambda`. -/
theorem infinityTwistor_reflection_normal
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) :
    kleinReflection (infinityTwistor Lambda) (infinityTwistor Lambda) =
      negP6 (infinityTwistor Lambda) := by
  apply kleinReflection_normal
  rw [kleinQ_infinityTwistor]
  exact hLambda

/-- The nonzero-Lambda vector-side reflection and spinor-side chiral bridge coexist:
reflection preserves the Klein norm while the Clifford map is bijective.  This theorem
packages only internally proved consequences, not the external Pin-lift identification. -/
theorem nonzeroLambda_reflection_and_chiral_bridge
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) :
    (∀ p : P6,
      kleinQ (kleinReflection (infinityTwistor Lambda) p) = kleinQ p) ∧
    Function.Bijective
      (GppKleinSpinorIncidence.cPlus (infinityTwistor Lambda)) := by
  constructor
  · intro p
    exact kleinQ_kleinReflection (infinityTwistor Lambda) p (by
      rw [kleinQ_infinityTwistor]
      exact hLambda)
  · exact cPlus_infinityTwistor_bijective Lambda hLambda

/-- At the flat member the reflection normal is null, so the hypothesis required for the
ordinary orthogonal-reflection construction fails exactly. -/
theorem flat_infinity_is_reflection_singular :
    kleinQ (infinityTwistor 0) = 0 := by
  rw [kleinQ_infinityTwistor]

end GppKleinPinReflectionDegeneration
