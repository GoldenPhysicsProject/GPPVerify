import Mathlib.Tactic

/-!
# Weighted small-diamond curvature residual and local tomography

For a flat n-ball of radius R, N_R=(R²-r²)/(2R).
Normalized N_R-weighted expectation of r² is n R²/(n+4).
The normalizing mass is R V/(n+2).

If the weighted Einstein-constraint residual has radial jet
E(r)=a+b r² and its weighted integral vanishes for two distinct
positive radii, then a=b=0. This gives a concrete local-recovery
calculation in addition to the already formalized Green first-law
and exact off-shell residual.

A continuous general residual can be reconstructed by the approximate
identity as R→0; that analytic statement is proved in the manuscript,
not formalized here as a Lebesgue differentiation theorem.

The radial polynomial is a local test. It is not a proof of
Einstein's field equations from quantum mechanics on arbitrary
spacetime backgrounds.
-/

namespace GppDiamondWeightedLocalization

/-- The total lapse measure ∫_B N_R dV, where V denotes the
Euclidean n-ball volume. -/
noncomputable def lapseMass (n R V : ℝ) : ℝ :=
  R * V / (n + 2)

/-- Ratio ∫_B N_R r² dV / ∫_B N_R dV. -/
noncomputable def weightedRadialSecondMoment (n R : ℝ) : ℝ :=
  (n / (n + 4)) * R^2

/-- Two radial moments integrated against the CKV lapse, with
V the Euclidean volume of the ball. -/
noncomputable def radialSecondLapseMoment (n R V : ℝ) : ℝ :=
  n * R^3 * V / ((n+2)*(n+4))

/-- Exact weighted radial moment ratio, if denominators and
normalizing mass are nonzero. -/
theorem weighted_second_moment_exact
    (n R V : ℝ) (hn2 : n+2 ≠ 0) (hn4 : n+4 ≠ 0)
    (hRV : R*V ≠ 0) :
    radialSecondLapseMoment n R V =
      lapseMass n R V * weightedRadialSecondMoment n R := by
  unfold radialSecondLapseMoment lapseMass weightedRadialSecondMoment
  field_simp
  ring

/-- The normalized weighted residual in the radial quadratic sector. -/
noncomputable def normalizedResidual (n R a b : ℝ) : ℝ :=
  a + weightedRadialSecondMoment n R * b

/-- Independent radii recover both the constant and the quadratic
coefficients of a weighted linearized constraint residual. -/
theorem two_radii_detect_constant_and_quadratic
    (c a b R S : ℝ) (hc : c ≠ 0) (hDistinct : R^2 ≠ S^2)
    (hR : a + c * R^2 * b = 0)
    (hS : a + c * S^2 * b = 0) :
    a = 0 ∧ b = 0 := by
  have hm : (c*(R^2-S^2))*b = 0 := by
    nlinarith [hR, hS]
  have hcb : c*(R^2-S^2) ≠ 0 := mul_ne_zero hc (sub_ne_zero.mpr hDistinct)
  have hb : b = 0 := (mul_eq_zero.mp hm).resolve_left hcb
  constructor
  · simpa [hb] using hR
  · exact hb

/-- The particular CKV-lapse weighted residual is sufficient to
recover a radial polynomial residual from two ball sizes. -/
theorem flat_diamond_two_radii_constraint_reconstruction
    (n a b R S : ℝ) (hn : n ≠ 0)
    (hn4 : n+4 ≠ 0) (hDistinct : R^2 ≠ S^2)
    (hR : normalizedResidual n R a b = 0)
    (hS : normalizedResidual n S a b = 0) :
    a = 0 ∧ b = 0 := by
  apply two_radii_detect_constant_and_quadratic
    (n/(n+4)) a b R S (div_ne_zero hn hn4) hDistinct
  · simpa only [normalizedResidual, weightedRadialSecondMoment] using hR
  · simpa only [normalizedResidual, weightedRadialSecondMoment] using hS

end GppDiamondWeightedLocalization

#print axioms GppDiamondWeightedLocalization.weighted_second_moment_exact
#print axioms GppDiamondWeightedLocalization.two_radii_detect_constant_and_quadratic
#print axioms GppDiamondWeightedLocalization.flat_diamond_two_radii_constraint_reconstruction
