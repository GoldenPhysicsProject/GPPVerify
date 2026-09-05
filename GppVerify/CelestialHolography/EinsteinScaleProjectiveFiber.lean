import Mathlib.Tactic
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry

/-!
# Projective basis geometry of a rank-two Einstein-scale fibre

Along a null geodesic the almost-Einstein scale equation is a second-order linear ODE,
so its local solution space is two-dimensional.  Choosing a basis `(sigma1,sigma2)` and
working where `sigma2 != 0` gives the projective coordinate

  tau = sigma1 / sigma2.

Changing the solution basis by an `SL(2)` matrix

  [[a,b],[c,d]]

sends this ratio to the Möbius transform

  tau |-> (a*tau+b)/(c*tau+d).

This is the finite-dimensional algebra behind the statement that the rank-two solution
bundle determines only a projective family of affine parameters.  Differential-geometric
input external to this file identifies, for a nonvanishing almost-Einstein scale sigma,
the ratio obtained by reduction of order with an affine parameter of the Einstein metric
`g_E = sigma^{-2} g`, since null affine parameters transform by `d tau = sigma^{-2} ds`.

No ODE existence, differentiation, or conformal-rescaling theorem is formalized here.
-/

namespace GppEinsteinScaleProjectiveFiber

open GppGrassmannianGooglyDecomposition
open GppEinsteinNullRaySL2Geometry

/-- Linear change of a two-component solution basis/value pair. -/
def basisChange (M : M2) (u : RayState) : RayState := act2 M u

/-- Affine projective coordinate on the patch where the second component is nonzero. -/
def projectiveRatio (u : RayState) : ℝ := u.1 / u.2

/-- Fractional-linear action attached to a 2x2 matrix. -/
def mobius (M : M2) (t : ℝ) : ℝ :=
  (M.1*t + M.2.1) / (M.2.2.1*t + M.2.2.2)

/-- Main basis-change theorem: the ratio of a transformed two-vector is the Möbius
transform of its original ratio whenever the relevant denominators are nonzero. -/
theorem projectiveRatio_basisChange
    (M : M2) (u : RayState)
    (hu : u.2 ≠ 0)
    (hden : M.2.2.1 * projectiveRatio u + M.2.2.2 ≠ 0) :
    projectiveRatio (basisChange M u) = mobius M (projectiveRatio u) := by
  rcases M with ⟨a,b,c,d⟩
  rcases u with ⟨x,y⟩
  simp [basisChange, act2, projectiveRatio, mobius] at hu hden ⊢
  have hout : c*x + d*y ≠ 0 := by
    intro hxy
    apply hden
    field_simp [hu]
    exact hxy
  field_simp [hu, hden, hout]
  ring

/-- An `SL(2)` basis change preserves the Wronskian/symplectic form, so the same basis
changes that act projectively by Möbius maps preserve the natural two-solution volume. -/
theorem sl2_basisChange_preserves_omega
    (M : M2) (hM : det2 M = 1) (u v : RayState) :
    omega (basisChange M u) (basisChange M v) = omega u v := by
  exact omega_preserved_of_det_one M hM u v

/-- The standard Weyl basis change acts by projective inversion on the patch where both
coordinates are nonzero. -/
theorem rayWeyl_projective_inversion
    (u : RayState) (hu1 : u.1 ≠ 0) (hu2 : u.2 ≠ 0) :
    projectiveRatio (basisChange rayWeyl u) = -1 / projectiveRatio u := by
  rcases u with ⟨x,y⟩
  simp [basisChange, act2, rayWeyl, projectiveRatio] at hu1 hu2 ⊢
  field_simp [hu1, hu2]

/-- Lower-unipotent change of the solution state gives the corresponding fractional
linear action in the chosen ratio chart. -/
theorem rayUnipotent_projective_action
    (a : ℝ) (u : RayState) (hu : u.2 ≠ 0)
    (hden : a * projectiveRatio u + 1 ≠ 0) :
    projectiveRatio (basisChange (rayUnipotent a) u) =
      projectiveRatio u / (a * projectiveRatio u + 1) := by
  rw [projectiveRatio_basisChange (rayUnipotent a) u hu]
  · simp [mobius, rayUnipotent]
  · simpa [rayUnipotent] using hden

/-- A determinant-one change of solution basis therefore simultaneously preserves the
Wronskian and acts projectively on the solution ratio. -/
theorem sl2_projective_fibre_package
    (M : M2) (hM : det2 M = 1) (u v : RayState)
    (hu : u.2 ≠ 0)
    (hden : M.2.2.1 * projectiveRatio u + M.2.2.2 ≠ 0) :
    omega (basisChange M u) (basisChange M v) = omega u v ∧
    projectiveRatio (basisChange M u) = mobius M (projectiveRatio u) := by
  exact ⟨sl2_basisChange_preserves_omega M hM u v,
    projectiveRatio_basisChange M u hu hden⟩

end GppEinsteinScaleProjectiveFiber
