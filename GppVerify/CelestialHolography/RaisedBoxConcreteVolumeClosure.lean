import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Concrete raised-box simplex volume closure

This file closes the normalization gap between the actual real affine-simplex
volume used by `simplexMoment` and the auxiliary complex Beta/Gamma reduction.
The concrete nested interval integral is evaluated directly from the pinned
Mathlib polynomial integral theorem `integral_pow`.
-/

namespace GppRaisedBoxConcreteVolumeClosure

open scoped Interval
open GppRaisedBoxConcreteMoment

/-- The actual real affine three-simplex used by the raised-box moment has
volume exactly `1/6`. -/
theorem simplexVolume_eq_one_sixth :
    simplexVolume = (1 / 6 : ℝ) := by
  have hinner : ∀ x1 : ℝ,
      (∫ x2 in (0 : ℝ)..(1 - x1), (1 - x1 - x2)) =
        (1 - x1) ^ 2 / 2 := by
    intro x1
    have hconst :
        (∫ _x2 in (0 : ℝ)..(1 - x1), (1 - x1 : ℝ)) =
          (1 - x1) * (1 - x1) := by
      simp
      ring
    have hid :
        (∫ x2 in (0 : ℝ)..(1 - x1), x2) =
          (1 - x1) ^ 2 / 2 := by
      rw [show (fun x2 : ℝ => x2) = (fun x2 : ℝ => x2 ^ (1 : ℕ)) by
        funext x2
        simp]
      rw [integral_pow]
      ring
    calc
      (∫ x2 in (0 : ℝ)..(1 - x1), (1 - x1 - x2)) =
          (∫ x2 in (0 : ℝ)..(1 - x1), (1 - x1 : ℝ)) -
            (∫ x2 in (0 : ℝ)..(1 - x1), x2) := by
              rw [intervalIntegral.integral_sub
                (intervalIntegral.intervalIntegrable_const (1 - x1))
                intervalIntegral.intervalIntegrable_id]
      _ = (1 - x1) ^ 2 / 2 := by
        rw [hconst, hid]
        ring
  have hx3 : ∀ x1 x2 : ℝ,
      (∫ _x3 in (0 : ℝ)..(1 - x1 - x2), (1 : ℝ)) = 1 - x1 - x2 := by
    intro x1 x2
    simp
  unfold simplexVolume
  simp_rw [hx3]
  simp_rw [hinner]
  have hpoly : ∀ x1 : ℝ,
      (1 - x1) ^ 2 / 2 = 1 / 2 - x1 + x1 ^ 2 / 2 := by
    intro x1
    ring
  simp_rw [hpoly]
  have h0 : (∫ _x1 in (0 : ℝ)..1, (1 / 2 : ℝ)) = 1 / 2 := by
    norm_num
  have h1 : (∫ x1 in (0 : ℝ)..1, x1) = 1 / 2 := by
    rw [show (fun x1 : ℝ => x1) = (fun x1 : ℝ => x1 ^ (1 : ℕ)) by
      funext x1
      simp]
    rw [integral_pow]
    norm_num
  have h2 : (∫ x1 in (0 : ℝ)..1, x1 ^ 2 / 2) = 1 / 6 := by
    rw [intervalIntegral.integral_div]
    rw [integral_pow]
    norm_num
  calc
    (∫ x1 in (0 : ℝ)..1, (1 / 2 - x1 + x1 ^ 2 / 2)) =
        (∫ _x1 in (0 : ℝ)..1, (1 / 2 : ℝ)) -
          (∫ x1 in (0 : ℝ)..1, x1) +
            (∫ x1 in (0 : ℝ)..1, x1 ^ 2 / 2) := by
              rw [intervalIntegral.integral_add
                ((intervalIntegral.intervalIntegrable_const (1 / 2 : ℝ)).sub
                  intervalIntegral.intervalIntegrable_id)
                ((intervalIntegral.intervalIntegrable_pow 2).div_const 2),
                intervalIntegral.integral_sub
                  (intervalIntegral.intervalIntegrable_const (1 / 2 : ℝ))
                  intervalIntegral.intervalIntegrable_id]
    _ = (1 / 6 : ℝ) := by
      rw [h0, h1, h2]
      norm_num

/-- Consequently the concrete raised-box moment at zero regulator is exactly
`1/6`. -/
theorem simplexMoment_zero_eq_one_sixth (S T : ℝ) :
    simplexMoment 0 S T = (1 / 6 : ℝ) := by
  rw [simplexMoment_zero]
  exact simplexVolume_eq_one_sixth

end GppRaisedBoxConcreteVolumeClosure

#print axioms GppRaisedBoxConcreteVolumeClosure.simplexVolume_eq_one_sixth
#print axioms GppRaisedBoxConcreteVolumeClosure.simplexMoment_zero_eq_one_sixth