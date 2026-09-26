import Mathlib.Tactic

/-!
# Golden Möbius audit

This file tests, exactly and without numerical fitting, whether the Möbius transformations
already present in the RH boundary program contain the golden-ratio dynamics

  x ↦ 1 + 1/x.

The answer is nuanced:

* the critical Cayley shadow map is x ↦ 1 - 1/x, so the golden map is obtained by
  precomposing it with the sign involution x ↦ -x;
* the even/odd Sherman--Morrison rank-one transforms become translations by ∓1 after
  the reciprocal coordinate y = 2/x;
* if that translation is combined with the reciprocal involution y ↦ 1/y, the resulting
  map is exactly y ↦ 1 + 1/y.

This is an algebraic structural observation only. No identification of the reciprocal
involution with the concrete arithmetic boundary transfer is asserted here.
-/

namespace GppGoldenMobius

noncomputable section

noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

def cayleyShadow (x : ℝ) : ℝ := 1 - 1 / x

def goldenMap (x : ℝ) : ℝ := 1 + 1 / x

/-- The sign-twisted critical Cayley shadow is exactly the golden Möbius map. -/
theorem goldenMap_eq_cayleyShadow_neg (x : ℝ) :
    goldenMap x = cayleyShadow (-x) := by
  simp [goldenMap, cayleyShadow]

/-- The golden ratio satisfies its defining quadratic equation. -/
theorem goldenRatio_sq :
    goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  dsimp [goldenRatio]
  nlinarith

theorem goldenRatio_pos : 0 < goldenRatio := by
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  dsimp [goldenRatio]
  positivity

/-- Any nonzero solution of x²=x+1 is a fixed point of the golden map. -/
theorem goldenMap_fixed_of_quadratic
    {x : ℝ} (hx : x ≠ 0) (hquad : x ^ 2 = x + 1) :
    goldenMap x = x := by
  unfold goldenMap
  field_simp [hx]
  nlinarith

theorem goldenRatio_fixed :
    goldenMap goldenRatio = goldenRatio := by
  apply goldenMap_fixed_of_quadratic
  · exact ne_of_gt goldenRatio_pos
  · exact goldenRatio_sq

/-- In contrast, the untwisted Cayley-shadow map has no real nonzero fixed point. -/
theorem cayleyShadow_no_real_fixed
    {x : ℝ} (hx : x ≠ 0) :
    cayleyShadow x ≠ x := by
  intro h
  unfold cayleyShadow at h
  field_simp [hx] at h
  have hs : 0 ≤ (x - (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
  nlinarith

/-- Odd rank-one Sherman--Morrison transform. -/
def oddSchur (x : ℝ) : ℝ := 2 * x / (x + 2)

/-- Even rank-one Sherman--Morrison transform. -/
def evenSchur (x : ℝ) : ℝ := -2 * x / (x - 2)

/-- Reciprocal projective coordinate in which the Schur transforms linearize. -/
def reciprocalCoord (x : ℝ) : ℝ := 2 / x

/-- The odd rank-one update is translation by +1 in y=2/x. -/
theorem reciprocalCoord_oddSchur
    {x : ℝ} (hx : x ≠ 0) :
    reciprocalCoord (oddSchur x) = reciprocalCoord x + 1 := by
  unfold reciprocalCoord oddSchur
  field_simp [hx]
  ring

/-- The even rank-one update is translation by -1 in y=2/x. -/
theorem reciprocalCoord_evenSchur
    {x : ℝ} (hx : x ≠ 0) :
    reciprocalCoord (evenSchur x) = reciprocalCoord x - 1 := by
  unfold reciprocalCoord evenSchur
  field_simp [hx]
  ring

/-- The two Sherman--Morrison Möbius transformations are mutual inverses away from poles. -/
theorem oddSchur_evenSchur
    {x : ℝ} (hx : x ≠ 2) :
    oddSchur (evenSchur x) = x := by
  unfold oddSchur evenSchur
  field_simp [hx]
  ring

/-- The reciprocal involution in the y-coordinate corresponds to x ↦ 4/x. -/
def poleDual (x : ℝ) : ℝ := 4 / x

theorem reciprocalCoord_poleDual
    {x : ℝ} (hx : x ≠ 0) :
    reciprocalCoord (poleDual x) = 1 / reciprocalCoord x := by
  unfold reciprocalCoord poleDual
  field_simp [hx]
  ring

/--
Translation by +1 after reciprocal duality is the golden map.

This is the exact modular-looking algebraic pattern T ∘ R, but the theorem deliberately
does not claim that poleDual is the arithmetic reflection of the completed RH system.
-/
theorem schur_duality_golden
    {x : ℝ} (hx : x ≠ 0) :
    reciprocalCoord (oddSchur (poleDual x))
      = goldenMap (reciprocalCoord x) := by
  unfold reciprocalCoord oddSchur poleDual goldenMap
  field_simp [hx]
  ring

end

end GppGoldenMobius
