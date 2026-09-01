import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Concrete raised-box simplex volume closure

This file closes the normalization gap between the actual real affine-simplex
volume used by `simplexMoment` and the auxiliary complex Beta/Gamma reduction.
The concrete nested interval integral is evaluated directly.
-/

namespace GppRaisedBoxConcreteVolumeClosure

open scoped Interval
open GppRaisedBoxConcreteMoment

/-- The actual real affine three-simplex used by the raised-box moment has
volume exactly `1/6`. -/
theorem simplexVolume_eq_one_sixth :
    simplexVolume = (1 / 6 : ℝ) := by
  unfold simplexVolume
  simp only [intervalIntegral.integral_const]
  have hinner : ∀ x1 : ℝ,
      (∫ x2 in (0 : ℝ)..(1 - x1), (1 - x1 - x2 : ℝ)) =
        (1 - x1) ^ 2 / 2 := by
    intro x1
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    rw [intervalIntegral.integral_const]
    have hid :
        (∫ x2 : ℝ in (0 : ℝ)..(1 - x1), x2) = (1 - x1) ^ 2 / 2 := by
      simpa using
        (intervalIntegral.integral_pow (a := (0 : ℝ)) (b := 1 - x1) (n := 1))
    rw [hid]
    ring
  simp_rw [hinner]
  have hpoly : ∀ x : ℝ,
      (1 - x) ^ 2 / 2 = (1 / 2 : ℝ) - x + x ^ 2 / 2 := by
    intro x
    ring
  simp_rw [hpoly]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    rw [intervalIntegral.integral_const]
    have hid : (∫ x : ℝ in (0 : ℝ)..1, x) = (1 / 2 : ℝ) := by
      simpa using
        (intervalIntegral.integral_pow (a := (0 : ℝ)) (b := (1 : ℝ)) (n := 1))
    rw [hid]
    rw [intervalIntegral.integral_div]
    rw [intervalIntegral.integral_pow]
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
