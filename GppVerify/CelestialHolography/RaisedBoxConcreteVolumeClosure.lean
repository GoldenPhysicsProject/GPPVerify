import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Concrete raised-box simplex volume closure

This file closes the normalization gap between the actual real affine-simplex
volume used by `simplexMoment` and the auxiliary complex Beta/Gamma reduction.
The concrete nested interval integral is evaluated directly.

On Mathlib 4.33 the linear and quadratic interval integrals are instantiated
explicitly from the top-level theorem `integral_pow`; avoiding a bare rewrite
keeps the proof robust to namespace/elaboration changes.
-/

namespace GppRaisedBoxConcreteVolumeClosure

open scoped Interval
open GppRaisedBoxConcreteMoment

/-- The actual real affine three-simplex used by the raised-box moment has
volume exactly `1/6`. -/
theorem simplexVolume_eq_one_sixth :
    simplexVolume = (1 / 6 : ℝ) := by
  unfold simplexVolume
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have hinner : ∀ x1 : ℝ,
      (∫ x2 in (0 : ℝ)..(1 - x1), (1 - x1 - x2 : ℝ)) =
        (1 - x1) ^ 2 / 2 := by
    intro x1
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    rw [intervalIntegral.integral_const]
    have hid :
        (∫ x2 : ℝ in (0 : ℝ)..(1 - x1), x2) = (1 - x1) ^ 2 / 2 := by
      simpa using
        (integral_pow (a := (0 : ℝ)) (b := 1 - x1) (n := 1))
    rw [hid]
    ring
  rw [show (∫ x1 in (0 : ℝ)..1, ∫ x2 in (0 : ℝ)..(1 - x1), (1 - x1 - x2 : ℝ)) =
      ∫ x1 in (0 : ℝ)..1, (1 - x1) ^ 2 / 2 by
        apply intervalIntegral.integral_congr
        intro x1 _
        exact hinner x1]
  have hpoly : ∀ x : ℝ,
      (1 - x) ^ 2 / 2 = (1 / 2 : ℝ) - x + x ^ 2 / 2 := by
    intro x
    ring
  apply Eq.trans (intervalIntegral.integral_congr (fun x _ => hpoly x))
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    rw [intervalIntegral.integral_const]
    have hid : (∫ x : ℝ in (0 : ℝ)..1, x) = (1 / 2 : ℝ) := by
      simpa using
        (integral_pow (a := (0 : ℝ)) (b := (1 : ℝ)) (n := 1))
    rw [hid]
    rw [intervalIntegral.integral_div]
    have hsq : (∫ x : ℝ in (0 : ℝ)..1, x ^ 2) = (1 / 3 : ℝ) := by
      simpa using
        (integral_pow (a := (0 : ℝ)) (b := (1 : ℝ)) (n := 2))
    rw [hsq]
    norm_num
  · exact intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_id
  · exact (intervalIntegral.intervalIntegrable_pow 2).div_const 2

/-- Consequently the concrete raised-box moment at zero regulator is exactly
`1/6`. -/
theorem simplexMoment_zero_eq_one_sixth (S T : ℝ) :
    simplexMoment 0 S T = (1 / 6 : ℝ) := by
  rw [simplexMoment_zero]
  exact simplexVolume_eq_one_sixth

end GppRaisedBoxConcreteVolumeClosure

#print axioms GppRaisedBoxConcreteVolumeClosure.simplexVolume_eq_one_sixth
#print axioms GppRaisedBoxConcreteVolumeClosure.simplexMoment_zero_eq_one_sixth
