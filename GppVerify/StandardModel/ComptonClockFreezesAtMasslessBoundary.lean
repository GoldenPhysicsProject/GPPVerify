import Mathlib.Tactic
import GppVerify.StandardModel.MassScaleClockBridge

/-!
# The intrinsic Compton clock freezes as the generated mass scale tends to zero

For a massive mode the reduced Compton time is

    tau_C = hbar/(m c^2).

Thus arbitrarily close to `m=0` its intrinsic rest-clock period can exceed any prescribed
finite duration.  Exactly at `m=0` the reciprocal formula is not a finite clock at all; the
massive rest-frame notion has disappeared.

This gives a precise, non-mystical reading of the project's "eternal instant" language: as
the mass order parameter approaches the symmetric boundary, intrinsic massive clocks stop
providing a finite tick scale.  This is NOT a statement that an external conformal
coordinate takes infinite time to reach the boundary.
-/

namespace GppComptonClockFreezesAtMasslessBoundary

open GppMassScaleClockBridge

/-- For any desired finite clock period `T>0`, there is a positive mass whose Compton time
    is exactly `2T`, hence exceeds `T`. -/
theorem arbitrarily_slow_compton_clock
    (c hbar T : ℝ) (hc : 0 < c) (hh : 0 < hbar) (hT : 0 < T) :
    ∃ m : ℝ, 0 < m ∧ comptonTime m c hbar > T := by
  let m : ℝ := hbar / (2*T*c^2)
  have hden : 0 < 2*T*c^2 := by positivity
  have hm : 0 < m := div_pos hh hden
  refine ⟨m, hm, ?_⟩
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hT0 : T ≠ 0 := ne_of_gt hT
  have hh0 : hbar ≠ 0 := ne_of_gt hh
  have heq : comptonTime m c hbar = 2*T := by
    simp [m, comptonTime]
    field_simp [hc0, hT0, hh0]
    ring
  rw [heq]
  linarith

/-- Equivalently, no finite upper bound can constrain all positive-mass Compton periods. -/
theorem no_uniform_finite_upper_bound_on_compton_time
    (c hbar B : ℝ) (hc : 0 < c) (hh : 0 < hbar) :
    ∃ m : ℝ, 0 < m ∧ comptonTime m c hbar > B := by
  by_cases hB : 0 < B
  · exact arbitrarily_slow_compton_clock c hbar B hc hh hB
  · refine ⟨1, by norm_num, ?_⟩
    have hct : 0 < comptonTime 1 c hbar := by
      simp [comptonTime]
      positivity
    linarith

/-- The Compton frequency itself vanishes at zero mass. -/
theorem zero_mass_zero_compton_frequency (c hbar : ℝ) :
    GppOrientationMassTime.comptonFrequency 0 c hbar = 0 := by
  simp [GppOrientationMassTime.comptonFrequency]

end GppComptonClockFreezesAtMasslessBoundary
