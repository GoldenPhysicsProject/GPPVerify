import Mathlib.Tactic

/-!
# Flat-ball explicit boundary compensation for the linearized ADM scalar constraint

On the flat n-dimensional ball B_R, the unit-normalized causal-diamond
lapse is N(x)=(R²-|x|²)/(2R). Its lapse Hessian satisfies
∂_i∂_j N = -δ_ij/R, ΔN=-n/R. For the homogeneous perturbation
γ_ij = 2ε δ_ij on the fixed coordinate ball, δR=0.

Green's identity for the smeared linearized scalar curvature reads
  ∫_B N(∂_i∂_j γ_ij - Δ tr γ)
    = ∫_B γ_ij(∂_i∂_j N - δ_ij ΔN)
      + ∮_{∂B} [N(n_i∂_jγ_ij-n_i∂_i trγ)
        - n_j(∂_iN)γ_ij + (n_i∂_iN) trγ].

At ∂B, N=0 and ∂_iN=-n_i. The boundary integrand becomes
γ_nn - trγ = 2ε(1-n). The interior integrand is constant
2ε*n*(n-1)/R, so the two terms cancel exactly since
Area(∂B) = n*Vol(B)/R.

The module proves the *scalar coefficient equalities* once the known
Euclidean ball area-volume relation is given; it does not formalize
the multidimensional divergence theorem or the Einstein--Hilbert
boundary charge from first principles. That geometry is a separate
continuum Lean formalization target.

This explicit cancellation shows why a bulk constraint cannot
be equated with the full boundary-sensitive York Hamiltonian.
-/

namespace GppDiamondExplicitBoundary

/-- Homogeneous perturbation γ_ij=2ε δ_ij and lapse Hessian:
interior scalar curvature variation pairing after integration by parts. -/
noncomputable def interiorWork (n R V eps : ℝ) : ℝ :=
  (2 * eps * n * (n - 1) / R) * V

/-- N|boundary=0, ∂_nN=-1; surface integrand = γ_nn - tr γ. -/
noncomputable def boundaryWork (n A eps : ℝ) : ℝ :=
  (2 * eps * (1 - n)) * A

/-- Proper volume response of the homogeneous conformal spatial metric. -/
noncomputable def volumeResponse (n V eps : ℝ) : ℝ :=
  n * eps * V

/-- Full cancellation of the boundary piece against the bulk York profile.
Requires only the exact ball geometric relation A=nV/R. -/
theorem homogeneous_ball_bulk_surface_cancel
    (n R V A eps : ℝ) (hR : R ≠ 0)
    (hAV : A = n * V / R) :
    interiorWork n R V eps + boundaryWork n A eps = 0 := by
  simp only [interiorWork, boundaryWork, hAV]
  field_simp
  ring

/-- Bulk York work is proportional to the proper-volume first variation. -/
theorem homogeneous_ball_bulk_is_volume_work
    (n R V eps : ℝ) (hR : R ≠ 0) :
    interiorWork n R V eps =
      (2 * (n-1) / R) * volumeResponse n V eps := by
  simp only [interiorWork, volumeResponse]
  ring

/-- On the constrained family, the boundary charge is opposite
the pure-trace interior York volume response. -/
theorem homogeneous_ball_surface_is_minus_york_work
    (n R V A eps : ℝ) (hR : R ≠ 0)
    (hAV : A = n * V / R) :
    boundaryWork n A eps =
      -((2 * (n-1) / R) * volumeResponse n V eps) := by
  have hb := homogeneous_ball_bulk_surface_cancel n R V A eps hR hAV
  rw [homogeneous_ball_bulk_is_volume_work n R V eps hR] at hb
  linarith

/-- For a three-dimensional ball the geometric area/volume relation
follows from the explicit Euclidean sphere formulas. -/
noncomputable def sphereArea (R : ℝ) : ℝ := 4 * Real.pi * R^2
noncomputable def ballVolume (R : ℝ) : ℝ := (4 * Real.pi / 3) * R^3

theorem sphere_area_eq_three_vol_over_radius
    (R : ℝ) (hR : R ≠ 0) :
    sphereArea R = 3 * ballVolume R / R := by
  simp only [sphereArea, ballVolume]
  field_simp
  ring

/-- In 3+1 dimensions the bulk coefficient is (4/R) dV,
and the boundary counterterm cancels it for an explicitly
constraint-preserving homogeneous metric rescaling. -/
theorem physical_three_ball_cancellation
    (R eps : ℝ) (hR : R ≠ 0) :
    interiorWork 3 R (ballVolume R) eps +
      boundaryWork 3 (sphereArea R) eps = 0 := by
  exact homogeneous_ball_bulk_surface_cancel
    3 R (ballVolume R) (sphereArea R) eps hR
    (sphere_area_eq_three_vol_over_radius R hR)

theorem physical_three_ball_york_coefficient
    (R eps : ℝ) (hR : R ≠ 0) :
    interiorWork 3 R (ballVolume R) eps =
      (4 / R) * volumeResponse 3 (ballVolume R) eps := by
  convert homogeneous_ball_bulk_is_volume_work
     3 R (ballVolume R) eps hR using 1 <;> ring

/-- Even though the full scalar-curvature pairing vanishes, the
proper-volume response is nonzero for any nonzero eps and radius.
This is a concrete obstruction to confusing the bulk constraint
with a condition δV=0. -/
theorem physical_three_ball_volume_response_nonzero
    (R eps : ℝ) (hR : R ≠ 0) (heps : eps ≠ 0) :
    volumeResponse 3 (ballVolume R) eps ≠ 0 := by
  simp only [volumeResponse, ballVolume]
  apply mul_ne_zero
  · apply mul_ne_zero
    · norm_num
    · exact heps
  · apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact Real.pi_ne_zero
    · exact pow_ne_zero 3 hR

end GppDiamondExplicitBoundary

#print axioms GppDiamondExplicitBoundary.homogeneous_ball_bulk_surface_cancel
#print axioms GppDiamondExplicitBoundary.homogeneous_ball_surface_is_minus_york_work
#print axioms GppDiamondExplicitBoundary.physical_three_ball_cancellation
#print axioms GppDiamondExplicitBoundary.physical_three_ball_volume_response_nonzero
