import Mathlib.Tactic

/-!
# Transverse normal-plane connection and conditional zitter scales

Finite algebraic core of the moving-frame reduction used in
Daniel Toupin, "Which Way Is Forward?", v16.

For an oriented transverse two-plane with connection coefficient Omega,
the covariant coordinate differentials are modeled by

  Dy1 = dy1 + Omega*y2
  Dy2 = dy2 - Omega*y1.

The canonical one-form then contains the exact minimal-coupling term

  k_a Dy^a = k_a dy^a - J_perp Omega,

where J_perp = y1*k2 - y2*k1.

The second part records the purely algebraic scale relations used in the
conditional constant-radius null-lift theorem.  It does NOT prove that a
physical electron follows a classical hidden orbit, nor does it derive the
dynamical selection of a constant-radius trajectory.
-/

namespace GppTransverseNormalConnection

/-- Generator of oriented rotations in the transverse two-plane. -/
def transverseAngularMomentum
    (y1 y2 k1 k2 : ℝ) : ℝ :=
  y1 * k2 - y2 * k1

/-- Canonical one-form coefficient in a moving transverse frame. -/
def movingCanonical
    (y1 y2 k1 k2 dy1 dy2 Omega : ℝ) : ℝ :=
  k1 * (dy1 + Omega * y2) +
  k2 * (dy2 - Omega * y1)

/-- Canonical one-form coefficient in a fixed transverse frame. -/
def bareCanonical
    (k1 k2 dy1 dy2 : ℝ) : ℝ :=
  k1 * dy1 + k2 * dy2

/-- Exact parent minimal-coupling identity. -/
theorem movingCanonical_eq_minimalCoupling
    (y1 y2 k1 k2 dy1 dy2 Omega : ℝ) :
    movingCanonical y1 y2 k1 k2 dy1 dy2 Omega =
      bareCanonical k1 k2 dy1 dy2 -
        transverseAngularMomentum y1 y2 k1 k2 * Omega := by
  simp [movingCanonical, bareCanonical, transverseAngularMomentum]
  ring

/-- The gauge-covariant angular differential dtheta - Omega is unchanged when
both the coordinate angle and the moving frame are shifted by dalpha. -/
theorem angular_difference_gauge_invariant
    (dtheta Omega dalpha : ℝ) :
    (dtheta + dalpha) - (Omega + dalpha) = dtheta - Omega := by
  ring

/-- Quantized transverse angular momentum written as X = 2 J_perp / hbar:
the equation J_perp = hbar*X/2 is exactly equivalent after clearing the
normalization. -/
theorem angular_momentum_charge_relation
    (J hbar X : ℝ)
    (h : J = hbar * X / 2) :
    2 * J = hbar * X := by
  linarith

/-- Lowest spinorial angular weight together with |k|=mc fixes the
multiplicative form of the zitter radius relation. -/
theorem lowest_spinor_radius_product
    (r m c hbar : ℝ)
    (hJ : r * (m * c) = hbar / 2) :
    2 * m * c * r = hbar := by
  nlinarith

/-- Combining the lowest-spinor radius relation with tangential speed c gives
the multiplicative zitter-frequency relation hbar*omega = 2*m*c^2. -/
theorem lowest_spinor_frequency_product
    (r m c hbar omega : ℝ)
    (hJ : r * (m * c) = hbar / 2)
    (hvel : r * omega = c) :
    hbar * omega = 2 * m * c^2 := by
  linear_combination (2 * m * c) * hvel - (2 * omega) * hJ

/-- If omega_Z = 2 omega_C, the spinorial half-angle evolves at omega_C. -/
theorem half_angle_compton_rate
    (omegaZ omegaC : ℝ)
    (h : omegaZ = 2 * omegaC) :
    omegaZ / 2 = omegaC := by
  linarith

end GppTransverseNormalConnection
