import Mathlib.Tactic
import GppVerify.CelestialHolography.ReflectionSpinGoldenFork

/-!
# Two canonical completions of reciprocity: `i` and `phi`

The projective reciprocal involution

  J(z) = 1/z

admits two structurally different completions already present in the null-ray geometry.

Elliptic/spin completion:

  R J(z) = -1/z,

where `R(z)=-z` is the orientation/sign reflection.  Its fixed-point equation is

  z = -1/z  <=>  z^2 = -1,

so over `C` the fixed points are `+i,-i`.  Its linear lift is the Weyl quarter-turn
`[[0,-1],[1,0]]`, whose square is `-I`: projective order two, spinor order four.

Hyperbolic/golden completion:

  N_1 J(z) = 1 + 1/z,

where `N_1` is the primitive unit shear.  Its positive real fixed point is `phi`, and its
orientation-preserving square has trace three.

Thus `i` and `phi` arise from the SAME reciprocity operation completed in two different
ways: sign reflection versus primitive translation.  This does not make phi automatically
physical; the global geometry still has to select an integral primitive shear.
-/

namespace GppReciprocityEllipticHyperbolicFixedPoints

open GppReflectionSpinGoldenFork

/-- Elliptic projective completion of reciprocity. -/
def ellipticMobius (z : ℂ) : ℂ := -1/z

/-- Its fixed-point equation is exactly `z^2=-1` away from zero. -/
theorem elliptic_fixed_iff_sq_neg_one {z : ℂ} (hz : z ≠ 0) :
    ellipticMobius z = z ↔ z^2 = -1 := by
  unfold ellipticMobius
  constructor
  · intro h
    field_simp [hz] at h
    nlinarith
  · intro h
    field_simp [hz]
    nlinarith

/-- `+i` is an elliptic fixed point. -/
theorem I_is_elliptic_fixed : ellipticMobius Complex.I = Complex.I := by
  simp [ellipticMobius, Complex.inv_I]

/-- `-i` is the opposite elliptic fixed point. -/
theorem negI_is_elliptic_fixed : ellipticMobius (-Complex.I) = -Complex.I := by
  simp [ellipticMobius, Complex.inv_I]

/-- The elliptic projective map is involutive away from zero. -/
theorem ellipticMobius_involution (z : ℂ) (hz : z ≠ 0) :
    ellipticMobius (ellipticMobius z) = z := by
  simp [ellipticMobius, hz]

/-- Its linear lift nevertheless has the spinorial central sign after two applications. -/
theorem linear_elliptic_lift_sq_central (u : GppEinsteinNullRaySL2Geometry.RayState) :
    GppEinsteinNullRaySL2Geometry.act2 GppEinsteinNullRaySL2Geometry.rayWeyl
      (GppEinsteinNullRaySL2Geometry.act2 GppEinsteinNullRaySL2Geometry.rayWeyl u) =
      GppFlatNullWeylFiberGeometry.scaleSpinor (-1) u := by
  exact GppEinsteinNullRaySL2Geometry.rayWeyl_sq_central_sign u

/-- The hyperbolic completion retains the already-proved golden positive fixed point. -/
theorem hyperbolic_positive_fixed_is_phi {z : ℝ} (hz : 0 < z) :
    z = 1 + 1/z ↔ z = Real.goldenRatio := by
  exact hyperbolic_completion_positive_fixed_iff_phi hz

end GppReciprocityEllipticHyperbolicFixedPoints
