import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
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
  norm_num
  ring_nf

/-- Consequently the concrete raised-box moment at zero regulator is exactly
`1/6`. -/
theorem simplexMoment_zero_eq_one_sixth (S T : ℝ) :
    simplexMoment 0 S T = (1 / 6 : ℝ) := by
  rw [simplexMoment_zero]
  exact simplexVolume_eq_one_sixth

end GppRaisedBoxConcreteVolumeClosure

#print axioms GppRaisedBoxConcreteVolumeClosure.simplexVolume_eq_one_sixth
#print axioms GppRaisedBoxConcreteVolumeClosure.simplexMoment_zero_eq_one_sixth
