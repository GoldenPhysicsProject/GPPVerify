import GppVerify.RiemannHypothesis.SechSquaredIntegral
import Mathlib.Tactic

/-!
# Kinematic spectral Fourier partner: exact weight-shift ODE

The focused kinematic-block calculation uses the normalized Fourier partner

  pHat(x) = 1 / (4 cosh(x/2)^2)

of the celestial spectral weight.  Equivalently

  pHat(x) = (1/4) (1 - tanh(x/2)^2).

This file certifies the elementary first-order equation

  (1/2) sinh(x) pHat'(x) = pHat(x) - pHat(0).

In particular the left side is negative away from the origin, resolving the
sign typo in the prose direct-check of the focused source while preserving the
stated differential equation itself.
-/

namespace GppKinematicWeightShiftODE

open GppSechIntegral

/-- Elementary real form of the normalized Fourier partner. -/
noncomputable def pHat (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (1 - Real.tanh (x / 2) ^ 2)

@[simp] theorem pHat_zero : pHat 0 = (1 / 4 : ℝ) := by
  simp [pHat]

/-- The tanh form is exactly the usual `sech^2` expression. -/
theorem pHat_eq_inv_cosh_sq (x : ℝ) :
    pHat x = 1 / (4 * Real.cosh (x / 2) ^ 2) := by
  unfold pHat
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
  field_simp [hc]
  exact Real.cosh_sq_sub_sinh_sq (x / 2)

/-- Exact derivative of the normalized Fourier partner. -/
theorem hasDerivAt_pHat (x : ℝ) :
    HasDerivAt pHat
      (-(Real.tanh (x / 2)) / (4 * Real.cosh (x / 2) ^ 2)) x := by
  have hinner : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have ht : HasDerivAt
      (fun y : ℝ => Real.tanh (y / 2))
      ((1 / Real.cosh (x / 2) ^ 2) * (1 / 2 : ℝ)) x := by
    refine ((hasDerivAt_tanh (x / 2)).comp x hinner).congr_deriv ?_
    simp
  have hs := ht.pow 2
  have hsub := (hasDerivAt_const x (1 : ℝ)).sub hs
  have h := (hasDerivAt_const x (1 / 4 : ℝ)).mul hsub
  change HasDerivAt
    (fun y : ℝ => (1 / 4 : ℝ) * (1 - Real.tanh (y / 2) ^ 2))
    (-(Real.tanh (x / 2)) / (4 * Real.cosh (x / 2) ^ 2)) x
  refine h.congr_deriv ?_
  norm_num <;> ring

/-- **Weight-shift differential equation.**  The normalized Fourier partner
satisfies `(1/2) sinh(x) pHat'(x) = pHat(x) - pHat(0)` for every real `x`. -/
theorem weightShift_ode (x : ℝ) :
    (1 / 2 : ℝ) * Real.sinh x * deriv pHat x = pHat x - pHat 0 := by
  rw [(hasDerivAt_pHat x).deriv]
  simp only [pHat_zero]
  unfold pHat
  have hrhs :
      (1 / 4 : ℝ) * (1 - Real.tanh (x / 2) ^ 2) - 1 / 4 =
        -(1 / 4 : ℝ) * Real.tanh (x / 2) ^ 2 := by
    ring
  rw [hrhs]
  have hsinh :
      Real.sinh x =
        2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    rw [show x = x / 2 + x / 2 by ring, Real.sinh_add]
    ring
  rw [hsinh, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
  field_simp [hc]

end GppKinematicWeightShiftODE

#print axioms GppKinematicWeightShiftODE.pHat_eq_inv_cosh_sq
#print axioms GppKinematicWeightShiftODE.hasDerivAt_pHat
#print axioms GppKinematicWeightShiftODE.weightShift_ode
