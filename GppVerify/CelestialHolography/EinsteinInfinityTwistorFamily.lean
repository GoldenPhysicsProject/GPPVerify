import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinNullInfinityBoundary

/-!
# Cosmological infinity-twistor Clifford family

The standard four-dimensional infinity twistor may be normalized so that its two
spinor blocks have relative coefficient `Lambda` and obey

  I_{AC} I^{BC} = Lambda delta_A^B.

In the Plucker/Klein coordinates used by GPPVerify, the corresponding one-parameter
algebraic model is

  I_Lambda = (Lambda,0,0,0,0,1).

Its Klein quadratic norm is exactly `Lambda`.  The already-proved epsilon-Clifford
relation therefore specializes to

  cMinus(I_Lambda) o cPlus(I_Lambda) = -Lambda id,
  cPlus(I_Lambda)  o cMinus(I_Lambda) = -Lambda id.

Thus for `Lambda != 0` the two chiral twistor modules are explicitly isomorphic, with
inverse supplied by the opposite Clifford map scaled by `-1/Lambda`.  At `Lambda = 0`
this family is exactly the flat infinity point and the isomorphism degenerates to the
nilpotent exact complex formalized in `FlatInfinityChiralComplex`.

This file is finite-dimensional coordinate algebra.  The identification of this family
with the curved parallel scale tractor / local infinity twistor is an external geometric
input, not formalized here.
-/

namespace GppEinsteinInfinityTwistorFamily

open GppGrassmannianGooglyDecomposition
open GppTwistorAnnihilatorIncidence
open GppKleinSpinorIncidence
open GppKleinNullInfinityBoundary

/-- Algebraic infinity-twistor family with Klein norm equal to the cosmological parameter. -/
def infinityTwistor (Lambda : ℝ) : P6 := ⟨Lambda,0,0,0,0,1⟩

/-- The Klein norm of the cosmological infinity twistor is exactly `Lambda`. -/
theorem kleinQ_infinityTwistor (Lambda : ℝ) :
    kleinQ (infinityTwistor Lambda) = Lambda := by
  simp [kleinQ, infinityTwistor]

/-- The flat member of the family is exactly the previously defined null infinity point. -/
theorem infinityTwistor_zero : infinityTwistor 0 = infinityPoint := by
  rfl

/-- Scaling composition on the four-dimensional chiral module. -/
theorem scale4_comp (a b : ℝ) (x : V4) :
    scale4 a (scale4 b x) = scale4 (a*b) x := by
  rcases x with ⟨x0,x1,x2,x3⟩
  apply Prod.ext
  · simp [scale4]
    ring
  · apply Prod.ext
    · simp [scale4]
      ring
    · apply Prod.ext <;> simp [scale4] <;> ring

/-- Unit scaling is the identity. -/
theorem scale4_one (x : V4) : scale4 1 x = x := by
  rcases x with ⟨x0,x1,x2,x3⟩
  rfl

/-- The plus Clifford map is homogeneous in its spinor argument. -/
theorem cPlus_scale (p : P6) (a : ℝ) (x : V4) :
    cPlus p (scale4 a x) = scale4 a (cPlus p x) := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases x with ⟨x0,x1,x2,x3⟩
  apply Prod.ext
  · simp [cPlus, scale4]
    ring
  · apply Prod.ext
    · simp [cPlus, scale4]
      ring
    · apply Prod.ext <;> simp [cPlus, scale4] <;> ring

/-- The minus Clifford map is homogeneous in its spinor argument. -/
theorem cMinus_scale (p : P6) (a : ℝ) (x : V4) :
    cMinus p (scale4 a x) = scale4 a (cMinus p x) := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases x with ⟨x0,x1,x2,x3⟩
  apply Prod.ext
  · simp [cMinus, scale4]
    ring
  · apply Prod.ext
    · simp [cMinus, scale4]
      ring
    · apply Prod.ext <;> simp [cMinus, scale4] <;> ring

/-- Cosmological Clifford square on the ordinary-twistor chirality. -/
theorem cMinus_cPlus_infinityTwistor (Lambda : ℝ) (z : V4) :
    cMinus (infinityTwistor Lambda) (cPlus (infinityTwistor Lambda) z) =
      scale4 (-Lambda) z := by
  rw [cMinus_cPlus, kleinQ_infinityTwistor]

/-- Cosmological Clifford square on the dual-twistor chirality. -/
theorem cPlus_cMinus_infinityTwistor (Lambda : ℝ) (alpha : V4) :
    cPlus (infinityTwistor Lambda) (cMinus (infinityTwistor Lambda) alpha) =
      scale4 (-Lambda) alpha := by
  rw [cPlus_cMinus, kleinQ_infinityTwistor]

/-- For nonzero cosmological parameter, scaled `cMinus` is a left inverse of `cPlus`. -/
theorem scaled_cMinus_leftInverse_cPlus
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) (z : V4) :
    scale4 (-1/Lambda)
      (cMinus (infinityTwistor Lambda) (cPlus (infinityTwistor Lambda) z)) = z := by
  rw [cMinus_cPlus_infinityTwistor, scale4_comp]
  have hscale : (-1/Lambda) * (-Lambda) = 1 := by
    field_simp [hLambda]
  rw [hscale, scale4_one]

/-- For nonzero cosmological parameter, the same scaled map is also a right inverse. -/
theorem scaled_cMinus_rightInverse_cPlus
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) (alpha : V4) :
    cPlus (infinityTwistor Lambda)
      (scale4 (-1/Lambda) (cMinus (infinityTwistor Lambda) alpha)) = alpha := by
  rw [cPlus_scale, cPlus_cMinus_infinityTwistor, scale4_comp]
  have hscale : (-1/Lambda) * (-Lambda) = 1 := by
    field_simp [hLambda]
  rw [hscale, scale4_one]

/-- Hence the plus chiral bridge is injective whenever `Lambda != 0`. -/
theorem cPlus_infinityTwistor_injective
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) :
    Function.Injective (cPlus (infinityTwistor Lambda)) := by
  intro x y hxy
  calc
    x = scale4 (-1/Lambda)
        (cMinus (infinityTwistor Lambda) (cPlus (infinityTwistor Lambda) x)) :=
      (scaled_cMinus_leftInverse_cPlus Lambda hLambda x).symm
    _ = scale4 (-1/Lambda)
        (cMinus (infinityTwistor Lambda) (cPlus (infinityTwistor Lambda) y)) := by
      rw [hxy]
    _ = y := scaled_cMinus_leftInverse_cPlus Lambda hLambda y

/-- And it is surjective, with the displayed scaled opposite-chirality preimage. -/
theorem cPlus_infinityTwistor_surjective
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) :
    Function.Surjective (cPlus (infinityTwistor Lambda)) := by
  intro alpha
  refine ⟨scale4 (-1/Lambda) (cMinus (infinityTwistor Lambda) alpha), ?_⟩
  exact scaled_cMinus_rightInverse_cPlus Lambda hLambda alpha

/-- Nonzero `Lambda` therefore gives an honest chiral isomorphism at the vector-space level. -/
theorem cPlus_infinityTwistor_bijective
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) :
    Function.Bijective (cPlus (infinityTwistor Lambda)) :=
  ⟨cPlus_infinityTwistor_injective Lambda hLambda,
   cPlus_infinityTwistor_surjective Lambda hLambda⟩

/-- At `Lambda=0` the cosmological square degenerates to zero. -/
theorem flat_limit_cMinus_cPlus_zero (z : V4) :
    cMinus (infinityTwistor 0) (cPlus (infinityTwistor 0) z) = (0,0,0,0) := by
  rw [infinityTwistor_zero, cMinus_cPlus,
      GppKleinNullInfinityBoundary.infinityPoint_is_null]
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [scale4]

end GppEinsteinInfinityTwistorFamily
