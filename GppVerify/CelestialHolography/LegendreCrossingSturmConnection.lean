import Mathlib.Tactic

/-!
# Legendre four-point periods as a crossing-covariant Sturm projective connection

Four marked points on `P^1` may be placed at `0,1,z,infinity`.  The canonical double
cover branched at those four points is the Legendre elliptic curve

    y^2 = x (x-1) (x-z).

Its periods satisfy the Gauss hypergeometric/Picard--Fuchs equation

    z(1-z) y'' + (1-2z) y' - (1/4) y = 0.

Removing the first-derivative term by the standard Liouville gauge

    psi = sqrt(z(1-z)) y

puts the equation in normal Sturm form

    psi'' + U(z) psi = 0,

with

    U(z) = (z^2-z+1) / (4 z^2 (1-z)^2).

The remarkable elementary fact formalized below is that this rational projective
connection is covariant under the generators of the full anharmonic/crossing action.
For a Mobius coordinate change `z=f(w)`, a Sturm projective connection transforms with
weight two (the Schwarzian term vanishes for Mobius maps):

    U_new(w) = f'(w)^2 U(f(w)).

For the crossing generators

    f(w)=1-w,          f'(w)^2=1,
    g(w)=1/w,          g'(w)^2=1/w^4,

one gets exactly the same `U(w)`.

This supplies a concrete rank-two crossing-covariant Sturm system on four-point moduli,
whose external Gauss--Manin interpretation carries an integral symplectic lattice.  Lean
below proves only the rational identities.  It does NOT identify this moduli-space Sturm
system with the null-ray Einstein/sky/NSF Sturm bundle; establishing such an intertwiner
is the central global bridge still required by the GPP program.
-/

namespace GppLegendreCrossingSturmConnection

/-- Normal-form Legendre/Picard--Fuchs Sturm potential. -/
noncomputable def legendrePotential (z : ℝ) : ℝ :=
  (z^2-z+1) / (4*z^2*(1-z)^2)

/-- The numerator is invariant under the crossing reflection `z -> 1-z`. -/
theorem legendre_numerator_one_sub (z : ℝ) :
    (1-z)^2 - (1-z) + 1 = z^2-z+1 := by
  ring

/-- First crossing covariance: `z -> 1-z` leaves the Sturm potential exactly fixed. -/
theorem legendrePotential_one_sub (z : ℝ) :
    legendrePotential (1-z) = legendrePotential z := by
  unfold legendrePotential
  congr 1 <;> ring

/-- Second crossing covariance: under inversion, the projective-connection weight
`(d(1/z)/dz)^2 = z^{-4}` exactly compensates the transformed rational potential. -/
theorem legendrePotential_inv_covariant
    (z : ℝ) (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (1/z^4) * legendrePotential (1/z) = legendrePotential z := by
  unfold legendrePotential
  field_simp [hz, hz1]
  ring

/-- The other standard crossing generator `z -> z/(z-1)` is likewise covariant with
its squared derivative factor `(z-1)^{-4}`. -/
theorem legendrePotential_frac_covariant
    (z : ℝ) (hz1 : z ≠ 1) (hz : z ≠ 0) :
    (1/(z-1)^4) * legendrePotential (z/(z-1)) = legendrePotential z := by
  unfold legendrePotential
  field_simp [hz, hz1]
  ring

/-- Reflection followed by inversion gives `z -> 1/(1-z)`; its derivative-squared
factor is `(1-z)^{-4}` and again the same projective connection results. -/
theorem legendrePotential_one_over_one_sub_covariant
    (z : ℝ) (hz1 : z ≠ 1) (hz : z ≠ 0) :
    (1/(1-z)^4) * legendrePotential (1/(1-z)) = legendrePotential z := by
  unfold legendrePotential
  field_simp [hz, hz1]
  ring

/-- Away from both finite cusps, clearing the `z=0` double pole leaves the equal
normalized coefficient `1/4`.  Both exclusions are required because Lean's division is
totalized, so the corresponding formula is false at `z=0` itself. -/
theorem cusp_zero_normalized
    (z : ℝ) (hz : z ≠ 0) (hz1 : z ≠ 1) :
    z^2 * legendrePotential z = (z^2-z+1) / (4*(1-z)^2) := by
  unfold legendrePotential
  field_simp [hz, hz1]
  ring

/-- The `z=1` cusp has the same normalized coefficient by crossing reflection; again the
rational identity is stated on the common domain away from both finite cusps. -/
theorem cusp_one_normalized
    (z : ℝ) (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (1-z)^2 * legendrePotential z = (z^2-z+1) / (4*z^2) := by
  unfold legendrePotential
  field_simp [hz, hz1]
  ring

end GppLegendreCrossingSturmConnection
