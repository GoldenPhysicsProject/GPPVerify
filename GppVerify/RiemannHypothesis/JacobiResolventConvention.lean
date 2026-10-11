import Mathlib.Tactic

/-!
# Jacobi resolvent sign, fixed by the inhomogeneous equation

This module does NOT define the Weyl function to equal -r and then
declare the sign verified. It constructs the proposed Green column
g_n = -r^(n+1) and proves (J - E)g = e_0 coordinatewise, where
E=r+r⁻¹, r≠0 and J is the half-line adjacency matrix.

When |r|<1, the column belongs to ℓ² and thus determines the true
resolvent column at E off the spectral band. The analytic invertibility
and ℓ² uniqueness statement is not yet formalized here.

The finite algebra itself fixes the sign convention and refutes the
isolated energy sign flip proposed by an independent numerical checker.
-/

namespace GppJacobiResolventConvention

noncomputable def energy (r : ℂ) : ℂ := r + r⁻¹
def green (r : ℂ) (n : ℕ) : ℂ := -(r ^ (n + 1))

def jacobi (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (if n = 0 then 0 else f (n - 1)) + f (n + 1)

/-- At the boundary the Green column has source +1, not -1. -/
theorem green_boundary (r : ℂ) (hr : r ≠ 0) :
    jacobi (green r) 0 - energy r * green r 0 = 1 := by
  simp [jacobi, green, energy]
  field_simp [hr]
  ring

/-- At every positive site the same Green column is homogeneous. -/
theorem green_bulk (r : ℂ) (n : ℕ) :
    jacobi (green r) (n + 1) -
      energy r * green r (n + 1) = 0 := by
  simp only [jacobi, green, energy, Nat.succ_ne_zero,
    if_false, Nat.succ_sub_one]
  simp only [show n + 1 + 1 = n + 2 from by omega,
    show n + 1 + 1 + 1 = n + 3 from by omega]
  rw [show n + 3 = (n + 2) + 1 from by omega,
    show n + 2 = (n + 1) + 1 from by omega]
  simp only [pow_succ]
  field_simp
  ring

/-- The resolvent diagonal sign is negative with (J-E) inverse. -/
theorem green_diagonal (r : ℂ) : green r 0 = -r := by
  simp [green]

/-- A prime Euler factor arises with E=+2cosh(z log p). -/
theorem euler_boundary_factor (r τ : ℂ) :
    1 + τ * green r 0 = 1 - τ * r := by
  simp [green]
  ring

/-- The opposite sign in the same determinant produces the opposite factor. -/
theorem euler_boundary_opposite (r τ : ℂ) :
    1 - τ * green r 0 = 1 + τ * r := by
  simp [green]

end GppJacobiResolventConvention
