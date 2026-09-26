import GppVerify.RiemannHypothesis.GoldenMobiusAudit
import Mathlib.Tactic

/-!
# Suzuki Weyl boundary word and the golden return map

This file separates three scalar coordinates which must not be conflated in the
Riemann-hypothesis boundary program.

* `suzukiRatio = A/B` is the homogeneous deficiency/projective coordinate.
  Spectral reflection `z ↦ -z` swaps `A` and `B`, hence reciprocates this ratio.
* The normalized physical Suzuki Weyl function is
  `m = -i (A-B)/(A+B)`.  Spectral reflection changes its sign.
* The opposite `0/π` self-adjoint boundary condition is represented by the
  canonical Herglotz automorphism `m ↦ -1/m`.
* Scalar unit Krein feedback is `m ↦ m/(1+m)`; its reciprocal coordinate
  `y = 1/m` is translated by one.

The important correction is that reflection alone is not the golden reciprocal
operation in the physical Weyl coordinate.  The composite

  spectral reflection -> opposite-boundary duality

sends `m ↦ 1/m`.  Therefore, in the *same* reciprocal Weyl coordinate
`y=1/m`, it is exactly `y ↦ 1/y`.  Unit Krein feedback is exactly
`y ↦ y+1`.  Their composite is therefore the golden Möbius map
`y ↦ 1+1/y`.

Equivalently, in the scaled response `x=2m`, the two operations are the
projective pole duality `x ↦ 4/x` and the odd Sherman--Morrison update
`x ↦ 2x/(x+2)`.

This is an exact scalar boundary-word theorem.  It does **not** yet prove that
the completed arithmetic pole channel acts on Suzuki's finite Weyl function by
this unit Krein feedback.  That operator identification is the remaining bridge,
and no RH proof is claimed here.

The file also records a useful no-go.  The tempting projective response `2B/A`
cannot itself be Suzuki's normalized Herglotz/Weyl function: `A(i)=0`, so that
raw projective response degenerates at the normalization point, whereas the
normalized Weyl function equals `i` when the opposite boundary coordinate is
nonzero.
-/

namespace GppGoldenMobius

open GppWeilParity

noncomputable section

/-- The finite Suzuki Weyl coordinate associated with the 0/pi extension pair:
    `m = -i W_pi/W_0 = -i (A-B)/(A+B)`. -/
def physicalWeyl (I : ℂ → ℂ) (z : ℂ) : ℂ :=
  -Complex.I * (suzukiA I z - suzukiB I z) /
    (suzukiA I z + suzukiB I z)

/-- Spectral reflection makes the physical Weyl coordinate odd. -/
theorem physicalWeyl_neg (I : ℂ → ℂ) (z : ℂ) :
    physicalWeyl I (-z) = -physicalWeyl I z := by
  unfold physicalWeyl
  rw [suzukiA_neg_eq_neg_suzukiB, suzukiB_neg_eq_neg_suzukiA]
  ring

/-- The canonical opposite-boundary Weyl coordinate is the negative reciprocal. -/
def weylBoundaryDual (m : ℂ) : ℂ := -1 / m

/-- Reflection followed by opposite-boundary duality is reciprocal inversion. -/
def reflectDual (m : ℂ) : ℂ :=
  weylBoundaryDual (weylReflection m)

theorem reflectDual_eq_inv (m : ℂ) :
    reflectDual m = 1 / m := by
  simp [reflectDual, weylBoundaryDual, weylReflection]

/-- Standard scalar unit Krein rank-one feedback. -/
def kreinFeedback (m : ℂ) : ℂ := m / (1 + m)

/-- The physical reciprocal-Weyl coordinate. -/
def reciprocalWeylCoord (m : ℂ) : ℂ := 1 / m

/-- The scaled physical response used by the parity Sherman--Morrison formulas. -/
def scaledWeylResponse (m : ℂ) : ℂ := 2 * m

/--
In the reciprocal Weyl coordinate `y=1/m`, reflection followed by canonical
opposite-boundary duality is exactly reciprocal inversion `y ↦ 1/y`.
-/
theorem reciprocalWeyl_reflectDual_eq_inv (m : ℂ) :
    reciprocalWeylCoord (reflectDual m) =
      1 / reciprocalWeylCoord m := by
  simp [reciprocalWeylCoord, reflectDual_eq_inv]

/-- Reciprocal response linearizes unit Krein feedback to translation by +1. -/
theorem reciprocal_kreinFeedback
    {m : ℂ} (hm : m ≠ 0) (hm1 : 1 + m ≠ 0) :
    reciprocalWeylCoord (kreinFeedback m) =
      reciprocalWeylCoord m + 1 := by
  unfold reciprocalWeylCoord kreinFeedback
  field_simp [hm, hm1]
  ring

/--
The corrected physical boundary word is golden in one and the same coordinate:
reflection, opposite-boundary duality, and unit Krein feedback give
`y ↦ 1 + 1/y` on `y=1/m`.
-/
theorem reciprocalWeyl_golden_return
    {m : ℂ} (hm : m ≠ 0) (hfeed : 1 + 1 / m ≠ 0) :
    reciprocalWeylCoord (kreinFeedback (reflectDual m)) =
      goldenMapC (reciprocalWeylCoord m) := by
  rw [reflectDual_eq_inv]
  rw [reciprocal_kreinFeedback
    (m := 1 / m) (div_ne_zero one_ne_zero hm) hfeed]
  simp [reciprocalWeylCoord, goldenMapC, add_comm]

/--
In the scaled response `x=2m`, reflection plus opposite-boundary duality is
exactly the previously isolated pole-duality map `x ↦ 4/x`.
-/
theorem scaledWeyl_reflectDual_eq_poleDual (m : ℂ) :
    scaledWeylResponse (reflectDual m) =
      poleDualC (scaledWeylResponse m) := by
  by_cases hm : m = 0
  · simp [hm, scaledWeylResponse, reflectDual, weylBoundaryDual,
      weylReflection, poleDualC]
  · rw [reflectDual_eq_inv]
    unfold scaledWeylResponse poleDualC
    field_simp [hm]
    ring

/--
In the same scaled response `x=2m`, unit Krein feedback is exactly the odd
Sherman--Morrison transformation `x ↦ 2x/(x+2)`.
-/
theorem scaledWeyl_kreinFeedback_eq_oddSchur (m : ℂ) :
    scaledWeylResponse (kreinFeedback m) =
      oddSchurC (scaledWeylResponse m) := by
  by_cases hden : 1 + m = 0
  · have hm : m = -1 := by
      linear_combination hden
    simp [hm, scaledWeylResponse, kreinFeedback, oddSchurC]
  · unfold scaledWeylResponse kreinFeedback oddSchurC
    have hden2 : 2 * m + 2 ≠ 0 := by
      intro h
      have hfac : (2 : ℂ) * (1 + m) = 0 := by
        calc
          (2 : ℂ) * (1 + m) = 2 * m + 2 := by ring
          _ = 0 := h
      have hm1 : 1 + m = 0 :=
        (mul_eq_zero.mp hfac).resolve_left (by norm_num)
      exact hden hm1
    field_simp [hden, hden2]
    ring

/-! ## Signed pole coupling and the parity-duality defect -/

/-- Raw scalar response under a signed rank-one coupling of strength `alpha`. -/
def rawRankOneFeedback (alpha x : ℝ) : ℝ := x / (1 + alpha * x)

/-- The completed even pole coefficient `+1/2` is exactly the odd Schur map. -/
theorem halfDensity_evenPole_eq_oddSchur (x : ℝ) :
    rawRankOneFeedback (1 / 2 : ℝ) x = oddSchur x := by
  unfold rawRankOneFeedback oddSchur
  by_cases h : x + 2 = 0
  · have hx : x = -2 := by linarith
    simp [hx]
  · field_simp [h]
    ring

/-- The completed odd pole coefficient `-1/2` is exactly the even Schur map. -/
theorem halfDensity_oddPole_eq_evenSchur (x : ℝ) :
    rawRankOneFeedback (-1 / 2 : ℝ) x = evenSchur x := by
  unfold rawRankOneFeedback evenSchur
  by_cases h : x - 2 = 0
  · have hx : x = 2 := by linarith
    simp [hx]
  · field_simp [h]
    ring

/-- Coupling-normalized reciprocal response turns every signed rank-one feedback
    into a unit translation. -/
theorem reciprocal_signed_rankOne_feedback
    {alpha x : ℝ} (ha : alpha ≠ 0) (hx : x ≠ 0)
    (hden : 1 + alpha * x ≠ 0) :
    1 / (alpha * rawRankOneFeedback alpha x) =
      1 / (alpha * x) + 1 := by
  unfold rawRankOneFeedback
  field_simp [ha, hx, hden]
  ring

/-- The involution exchanging the two half-density threshold cones. -/
def parityDualResponse (x : ℝ) : ℝ := -4 / x

/-- The exact algebraic defect from the candidate even/odd duality surface
    `x_even * x_odd = -4`, expressed by the two threshold defects. -/
theorem parity_duality_defect_identity (xEven xOdd : ℝ) :
    xEven * xOdd + 4 =
      2 * (xEven + 2) - 2 * (xOdd - 2) +
        (xEven + 2) * (xOdd - 2) := by
  ring

/-- The candidate parity duality exchanges the two threshold points exactly. -/
theorem parityDualResponse_neg_two :
    parityDualResponse (-2) = 2 := by
  norm_num [parityDualResponse]

theorem parityDualResponse_two :
    parityDualResponse 2 = -2 := by
  norm_num [parityDualResponse]

/-- The deficiency coordinate `A` has its forced normalization zero at `z=i`. -/
theorem suzukiA_at_I_eq_zero (I : ℂ → ℂ) :
    suzukiA I Complex.I = 0 := by
  simp [suzukiA]

/-- Consequently the raw projective ratio `A/B` vanishes at `z=i`. -/
theorem suzukiRatio_at_I_eq_zero (I : ℂ → ℂ) :
    suzukiRatio I Complex.I = 0 := by
  unfold suzukiRatio
  rw [suzukiA_at_I_eq_zero]
  simp

/--
Hence the algebraic projective response `2/(A/B)`, interpreted in Lean's total
field convention, degenerates to zero at the Suzuki normalization point.
-/
theorem responseFromRatio_at_I_eq_zero (I : ℂ → ℂ) :
    responseFromRatio (suzukiRatio I Complex.I) = 0 := by
  rw [suzukiRatio_at_I_eq_zero]
  simp [responseFromRatio]

/-- If `B(i)` is nonzero, the physical Suzuki Weyl coordinate is normalized by
    `m(i)=i`. -/
theorem physicalWeyl_at_I
    (I : ℂ → ℂ) (hB : suzukiB I Complex.I ≠ 0) :
    physicalWeyl I Complex.I = Complex.I := by
  unfold physicalWeyl
  rw [suzukiA_at_I_eq_zero]
  field_simp [hB]
  ring

/-- The raw response `2B/A` and the normalized physical Weyl function are therefore
    provably different at the canonical normalization point whenever `B(i) ≠ 0`. -/
theorem responseFromRatio_ne_physicalWeyl_at_I
    (I : ℂ → ℂ) (hB : suzukiB I Complex.I ≠ 0) :
    responseFromRatio (suzukiRatio I Complex.I) ≠ physicalWeyl I Complex.I := by
  rw [responseFromRatio_at_I_eq_zero, physicalWeyl_at_I I hB]
  exact Ne.symm Complex.I_ne_zero

end

end GppGoldenMobius
