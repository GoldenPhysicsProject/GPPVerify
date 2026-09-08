import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GppVerify.StandardModel.OrientationMassTime

/-!
# Compton proper time as a logarithmic Haar coordinate

A nonzero mass supplies the reduced Compton angular frequency

    omega_C = m c^2 / hbar.

This gives a canonical dimensionless additive proper-time coordinate

    theta = omega_C tau.

Exponentiating the *unwrapped* coordinate produces a positive multiplicative coordinate

    rho = exp(theta) in R_+^x.

Then the elementary but structurally useful identities are exact:

    log rho = theta,
    tau -> -tau   iff   rho -> rho^{-1},
    d rho / rho = d theta = omega_C d tau   (differential interpretation).

The Lean theorems below formalize the pointwise algebraic part.  Thus, once a mass scale is
present, reversal of proper-time orientation is represented by inversion on the positive
multiplicative line, the same involution underlying multiplicative Haar measure `d rho/rho`.

Important scope: `rho` is an exponential lift of the unwrapped Compton phase coordinate,
not the periodic quantum phase `exp(-i theta)` itself.  Haar invariance alone does not
select the mass `m`; the theorem states what becomes canonical *after* a nonzero mass scale
has been supplied.
-/

namespace GppComptonHaarTimeBridge

open GppOrientationMassTime

/-- Dimensionless unwrapped Compton phase coordinate. -/
def comptonLogCoordinate (m c hbar tau : ℝ) : ℝ :=
  comptonFrequency m c hbar * tau

/-- Positive multiplicative lift of Compton proper time. -/
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

/-- Proper-time reversal becomes multiplicative inversion. -/
theorem timeReverse_eq_HaarInversion (m c hbar tau : ℝ) :
    comptonHaarScale m c hbar (-tau) =
      (comptonHaarScale m c hbar tau)⁻¹ := by
  simp [comptonHaarScale, comptonLogCoordinate, Real.exp_neg]

/-- The forward and reversed multiplicative coordinates multiply to one. -/
theorem timeReverse_pair_product_one (m c hbar tau : ℝ) :
    comptonHaarScale m c hbar tau *
      comptonHaarScale m c hbar (-tau) = 1 := by
  rw [timeReverse_eq_HaarInversion]
  exact mul_inv_cancel₀ (ne_of_gt (comptonHaarScale_pos m c hbar tau))

/-- The time origin maps to the Haar identity. -/
theorem comptonHaarScale_zero_time (m c hbar : ℝ) :
    comptonHaarScale m c hbar 0 = 1 := by
  simp [comptonHaarScale, comptonLogCoordinate]

/-- In the massless limit the intrinsic Compton chart collapses to the Haar identity:
there is no nontrivial rest-mass clock. -/
theorem massless_comptonHaarScale (c hbar tau : ℝ) :
    comptonHaarScale 0 c hbar tau = 1 := by
  simp [comptonHaarScale, comptonLogCoordinate, comptonFrequency]

/-- Reversal negates the logarithmic coordinate exactly. -/
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

/-- If the Compton frequency is nonzero, proper time can be recovered uniquely from the
Haar logarithmic coordinate. -/
theorem recover_properTime_from_Haar_log
    (m c hbar tau : ℝ)
    (hw : comptonFrequency m c hbar ≠ 0) :
    Real.log (comptonHaarScale m c hbar tau) /
        comptonFrequency m c hbar = tau := by
  rw [log_comptonHaarScale]
  simp [comptonLogCoordinate, hw]

end GppComptonHaarTimeBridge
