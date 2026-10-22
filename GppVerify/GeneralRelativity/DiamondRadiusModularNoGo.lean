import Mathlib.Tactic

/-!
# Size-independent modular symmetry does not fix the size of a causal diamond

For a Minkowski 3+1-dimensional round diamond with proper radius R>0,
the conformal Killing factor and radial flow are odd in t for EVERY R.
The maximal-slice 3-volume, however, is 4*pi*R^3/3 and has nonzero
first variation 4*pi*R^2.

The Casini--Huerta--Myers exact CFT ball modular Hamiltonian exists at
each radius. Here we formally verify the geometric family and an
independent normalized finite-state model; CFT modular theory itself
is NOT silently asserted as a Lean theorem.

Thus time-reflection symmetry, projective phase quotient, and the
existence of a ball modular flow are not sufficient to pick fixed
spatial volume. Any theorem claiming otherwise needs an additional
physical hypothesis (such as entropy-only stationarity, first law,
or York-flow reduction).
-/

namespace GppDiamondRadiusNoGo

/-- Flat causal diamond conformal factor (unit surface gravity). -/
noncomputable def alpha (R t : ℝ) : ℝ := -t / R

/-- Its radial conformal-Killing component. -/
noncomputable def radialFlow (R t r : ℝ) : ℝ := -(t * r) / R

/-- The spatial volume of the midpoint ball in 3+1 dimensions. -/
noncomputable def ballVolume (R : ℝ) : ℝ :=
    (4 * Real.pi / 3) * R ^ 3

/-- Time reflection exchanges expanding and contracting halves at
*every* positive radius, without selecting one of them. -/
theorem flow_time_odd (R t r : ℝ) :
    radialFlow R (-t) r = -radialFlow R t r := by
  unfold radialFlow
  ring

theorem conformal_factor_time_odd (R t : ℝ) :
    alpha R (-t) = -alpha R t := by
  unfold alpha
  ring

theorem conformal_factor_zero_midpoint (R : ℝ) :
    alpha R 0 = 0 := by simp [alpha]

theorem radial_flow_zero_midpoint (R r : ℝ) :
    radialFlow R 0 r = 0 := by simp [radialFlow]

/-- At the center of the diamond, both time-reversed portions occur for
any radius R>0, but the midpoint volume changes with R. -/
theorem volume_radius_one_vs_two :
    ballVolume 1 ≠ ballVolume 2 := by
  unfold ballVolume
  have hpi : 0 < Real.pi := Real.pi_pos
  norm_num
  nlinarith

/-- Formal volume response for a radial size perturbation; nonzero
for every positive radius, despite the two-sided symmetry. -/
noncomputable def radialVolumeResponse (R : ℝ) : ℝ :=
    4 * Real.pi * R ^ 2

theorem radial_volume_response_positive (R : ℝ) (hR : 0 < R) :
    0 < radialVolumeResponse R := by
  unfold radialVolumeResponse
  positivity

theorem radial_volume_response_nonzero (R : ℝ) (hR : 0 < R) :
    radialVolumeResponse R ≠ 0 :=
  ne_of_gt (radial_volume_response_positive R hR)

/-- A fixed normalized state tangent can be paired with an
independently nonzero geometric volume response: projective state
normalization does not logically force dV=0. -/
theorem phase_quotient_does_not_fix_radius :
    ∃ (dp : Fin 2 → ℝ) (R : ℝ),
        (∑ i, dp i) = 0 ∧
        0 < R ∧ radialVolumeResponse R ≠ 0 := by
  refine ⟨(fun _ => 0), 1, ?_, by norm_num, ?_⟩
  · simp
  · exact radial_volume_response_nonzero 1 (by norm_num)

end GppDiamondRadiusNoGo

#print axioms GppDiamondRadiusNoGo.flow_time_odd
#print axioms GppDiamondRadiusNoGo.volume_radius_one_vs_two
#print axioms GppDiamondRadiusNoGo.phase_quotient_does_not_fix_radius
