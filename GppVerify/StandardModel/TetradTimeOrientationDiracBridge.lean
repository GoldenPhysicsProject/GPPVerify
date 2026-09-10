import Mathlib.Tactic
import GppVerify.StandardModel.RelativePhaseDiracEnergy

/-!
# Timelike tetrad orientation induces the signed rest-Dirac phase

A Lorentz metric is quadratic in a tetrad, so the sign of one oriented tetrad leg is
invisible to the corresponding metric component.  A first-order Dirac operator is linear in
the tetrad/inverse-tetrad orientation and can see that sign.

This file isolates the rest-frame finite core.  Let `nu` be a signed timelike-frame/lapse
orientation parameter.  The metric coefficient depends on `nu^2`, while the signed rest
Dirac generator is

    B(nu,m) = nu*m*beta.

Consequently

    metric(-nu) = metric(nu),
    B(-nu,m) = -B(nu,m),
    B(nu,m)^2 = (nu*m)^2 I.

Thus the same bosonic metric data admit two fermion-sensitive tetrad lifts, and the two
first-order phase orientations have the same quadratic energy scale.  At `nu=0` the two
lifts meet, the normal metric coefficient degenerates, and the signed rest generator
vanishes.

This gives a concrete candidate for the project's microscopic temporal arrow: orientation
of the timelike tetrad/causal lift, which then induces the sign of the first-order Dirac
frequency.  It is NOT the thermodynamic arrow.  Extending this rest-frame statement to a
curved spin bundle requires an actual tetrad Dirac operator and spin connection.
-/

namespace GppTetradTimeOrientationDiracBridge

open GppRelativePhaseDiracEnergy

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Prototype timelike metric coefficient seen by bosons. -/
def timeMetricCoeff (nu : ℝ) : ℝ := -(nu^2)

/-- Signed rest-frame first-order Dirac generator. -/
def orientedRestGenerator (nu m : ℝ) : M2C :=
  ((nu*m : ℝ) : ℂ) • betaRest

/-- Bosonic metric data are blind to reversal of the timelike tetrad lift. -/
theorem metric_blind_to_time_orientation (nu : ℝ) :
    timeMetricCoeff (-nu) = timeMetricCoeff nu := by
  simp [timeMetricCoeff]

/-- The fermionic first-order generator is odd under that reversal. -/
theorem dirac_generator_sees_time_orientation (nu m : ℝ) :
    orientedRestGenerator (-nu) m = - orientedRestGenerator nu m := by
  ext i j
  simp [orientedRestGenerator]

/-- Squaring the first-order generator removes the orientation sign. -/
theorem orientedRestGenerator_sq (nu m : ℝ) :
    orientedRestGenerator nu m * orientedRestGenerator nu m =
      (((nu*m)^2 : ℝ) : ℂ) • (1 : M2C) := by
  unfold orientedRestGenerator
  rw [smul_mul, mul_smul, smul_smul, betaRest_sq_eq_one]
  norm_num
  ring

/-- Opposite tetrad lifts have exactly the same squared Dirac generator. -/
theorem opposite_lifts_same_quadratic_energy (nu m : ℝ) :
    orientedRestGenerator (-nu) m * orientedRestGenerator (-nu) m =
    orientedRestGenerator nu m * orientedRestGenerator nu m := by
  rw [orientedRestGenerator_sq, orientedRestGenerator_sq]
  simp

/-- At the branch locus the timelike metric coefficient degenerates. -/
theorem branch_metric_degenerate : timeMetricCoeff 0 = 0 := by
  norm_num [timeMetricCoeff]

/-- At the same locus the signed rest generator vanishes. -/
theorem branch_dirac_generator_zero (m : ℝ) :
    orientedRestGenerator 0 m = 0 := by
  simp [orientedRestGenerator]

/-- Equal metric coefficients determine the signed tetrad lift only up to sign. -/
theorem same_metric_two_lifts (nu rho : ℝ)
    (h : timeMetricCoeff nu = timeMetricCoeff rho) :
    nu = rho ∨ nu = -rho := by
  have hs : nu^2 = rho^2 := by
    simpa [timeMetricCoeff] using neg_inj.mp h
  have hfac : (nu-rho)*(nu+rho)=0 := by
    nlinarith [hs]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · left; linarith
  · right; linarith

/-- Away from zero, the two opposite tetrad lifts are distinct but metrically identical. -/
theorem nonzero_opposite_lifts_distinct_same_metric
    (nu : ℝ) (hnu : nu ≠ 0) :
    -nu ≠ nu ∧ timeMetricCoeff (-nu) = timeMetricCoeff nu := by
  constructor
  · intro h
    apply hnu
    linarith
  · exact metric_blind_to_time_orientation nu

/-- Canonical unit lifts have the same metric and opposite signed Dirac generators. -/
theorem unit_lift_package (m : ℝ) :
    timeMetricCoeff 1 = timeMetricCoeff (-1) ∧
    orientedRestGenerator (-1) m = -orientedRestGenerator 1 m ∧
    orientedRestGenerator 1 m * orientedRestGenerator 1 m =
      ((m^2 : ℝ) : ℂ) • (1 : M2C) := by
  refine ⟨by norm_num [timeMetricCoeff],
    dirac_generator_sees_time_orientation 1 m, ?_⟩
  simpa using orientedRestGenerator_sq 1 m

end GppTetradTimeOrientationDiracBridge
