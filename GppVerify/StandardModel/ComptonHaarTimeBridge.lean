import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GppVerify.StandardModel.OrientationMassTime

/-!
# Compton proper-time coordinate as a logarithmic Haar coordinate

A nonzero mass supplies the reduced Compton angular frequency

    omega_C = m c^2 / hbar.

This gives a canonical dimensionless additive coordinate along an already oriented
proper-time line,

    theta = omega_C tau.

Exponentiating the *unwrapped signed coordinate* produces

    rho = exp(theta) in R_+^x.

Then

    tau -> -tau  gives  rho -> rho^{-1}.

This is an exact coordinate-reflection statement.  It must be distinguished from reversing
the ORIENTATION of the worldline while keeping a positive elapsed magnitude fixed.  The
latter is represented elsewhere by a separate Z2 sign `t` in the decomposition

    R^x ~= Z2 x R_+^x,

and does not by itself invert the positive magnitude coordinate.  In particular, physical
worldline/time orientation and Haar/Mellin inversion are not identified merely because a
signed logarithmic coordinate changes sign.

The differential interpretation `d rho/rho = d theta = omega_C d tau` remains useful: mass
turns proper-time displacement into a dimensionless multiplicative scale.  Haar invariance
alone does not select the mass.
-/

namespace GppComptonHaarTimeBridge

open GppOrientationMassTime

/-- Dimensionless unwrapped Compton phase coordinate. -/
def comptonLogCoordinate (m c hbar tau : ℝ) : ℝ :=
  comptonFrequency m c hbar * tau

/-- Positive multiplicative lift of the signed Compton proper-time coordinate. -/
def comptonHaarScale (m c hbar tau : ℝ) : ℝ :=
  Real.exp (comptonLogCoordinate m c hbar tau)

/-- The multiplicative coordinate is always positive. -/
theorem comptonHaarScale_pos (m c hbar tau : ℝ) :
    0 < comptonHaarScale m c hbar tau := by
  exact Real.exp_pos _

/-- Its logarithm is exactly the dimensionless Compton proper-time coordinate. -/
theorem log_comptonHaarScale (m c hbar tau : ℝ) :
    Real.log (comptonHaarScale m c hbar tau) =
      comptonLogCoordinate m c hbar tau := by
  simp [comptonHaarScale]

/-- Reflection of the signed proper-time coordinate becomes multiplicative inversion. -/
theorem tau_coordinate_reflection_eq_HaarInversion (m c hbar tau : ℝ) :
    comptonHaarScale m c hbar (-tau) =
      (comptonHaarScale m c hbar tau)⁻¹ := by
  simp [comptonHaarScale, comptonLogCoordinate, Real.exp_neg]

/-- Backward-compatible theorem name.  Read this as signed-coordinate reflection, not as a
proof that physical Wigner/worldline orientation reversal equals Haar inversion. -/
theorem timeReverse_eq_HaarInversion (m c hbar tau : ℝ) :
    comptonHaarScale m c hbar (-tau) =
      (comptonHaarScale m c hbar tau)⁻¹ :=
  tau_coordinate_reflection_eq_HaarInversion m c hbar tau

/-- The two reflected coordinate values multiply to one. -/
theorem timeReverse_pair_product_one (m c hbar tau : ℝ) :
    comptonHaarScale m c hbar tau *
      comptonHaarScale m c hbar (-tau) = 1 := by
  rw [tau_coordinate_reflection_eq_HaarInversion]
  exact mul_inv_cancel₀ (ne_of_gt (comptonHaarScale_pos m c hbar tau))

/-- The coordinate origin maps to the Haar identity. -/
theorem comptonHaarScale_zero_time (m c hbar : ℝ) :
    comptonHaarScale m c hbar 0 = 1 := by
  simp [comptonHaarScale, comptonLogCoordinate]

/-- In the massless limit the intrinsic Compton chart collapses to the Haar identity:
there is no nontrivial rest-mass clock. -/
theorem massless_comptonHaarScale (c hbar tau : ℝ) :
    comptonHaarScale 0 c hbar tau = 1 := by
  simp [comptonHaarScale, comptonLogCoordinate, comptonFrequency]

/-- Reflection negates the logarithmic coordinate exactly. -/
theorem timeReverse_logCoordinate (m c hbar tau : ℝ) :
    comptonLogCoordinate m c hbar (-tau) =
      - comptonLogCoordinate m c hbar tau := by
  simp [comptonLogCoordinate]

/-- The multiplicative coordinate is a homomorphism from additive proper-time displacement
to positive multiplication. -/
theorem comptonHaarScale_add (m c hbar tau sigma : ℝ) :
    comptonHaarScale m c hbar (tau + sigma) =
      comptonHaarScale m c hbar tau * comptonHaarScale m c hbar sigma := by
  simp [comptonHaarScale, comptonLogCoordinate, mul_add, Real.exp_add]

/-- If the Compton frequency is nonzero, the signed proper-time coordinate is recovered from
the Haar logarithm. -/
theorem recover_properTime_from_Haar_log
    (m c hbar tau : ℝ)
    (hw : comptonFrequency m c hbar ≠ 0) :
    Real.log (comptonHaarScale m c hbar tau) /
        comptonFrequency m c hbar = tau := by
  rw [log_comptonHaarScale]
  simp [comptonLogCoordinate, hw]

end GppComptonHaarTimeBridge
