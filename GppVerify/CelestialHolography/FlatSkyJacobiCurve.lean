import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatInfinityCelestialFactorization

/-!
# Flat sky Jacobi curve in the light-ray contact hyperplane

For a fixed flat null geodesic, a transverse Jacobi field has the form

  J(s) = a + s b,

with two-component transverse data `a,b`.  Its initial-data space is therefore four
dimensional.  It carries the standard Wronskian symplectic form

  omega((a,b),(c,d)) = a.d - b.c.

For each point/parameter `s` on the ray, the tangent space to the sky through that point
is represented by the Jacobi fields which vanish there:

  L_s = {(-s v, v) : v in R^2}.

This file proves directly that each `L_s` is a two-dimensional isotropic plane (hence the
flat model of a Lagrangian sky tangent), that the vanishing condition characterizes it
exactly, and that the family is transported by the flat Jacobi flow.  The 2025
Bautista--Ibort--Lafuente Jacobi-curve theorem identifies the curved analogue
`T_gamma S(gamma(s))` as a Jacobi curve in the Lagrangian Grassmannian of the contact
hyperplane.  That differential-geometric theorem is external to this coordinate model.
-/

namespace GppFlatSkyJacobiCurve

open GppFlatInfinityCelestialFactorization

abbrev SkyState := Spinor2 × Spinor2

/-- Euclidean pairing on the two-dimensional screen coordinate carrier. -/
def dot2 (x y : Spinor2) : ℝ := x.1*y.1 + x.2*y.2

/-- Wronskian/symplectic form on transverse Jacobi initial data `(value, derivative)`. -/
def skyOmega (u v : SkyState) : ℝ :=
  dot2 u.1 v.2 - dot2 u.2 v.1

/-- Value at affine parameter `s` of the flat Jacobi field with initial data `(a,b)`. -/
def jacobiValue (u : SkyState) (s : ℝ) : Spinor2 :=
  (u.1.1 + s*u.2.1, u.1.2 + s*u.2.2)

/-- Standard parametrization of the sky-tangent plane at the point `s` of the ray. -/
def skyState (s : ℝ) (v : Spinor2) : SkyState :=
  ((-s*v.1,-s*v.2),v)

/-- Every vector in the displayed sky plane is a Jacobi field vanishing at `s`. -/
theorem skyState_vanishes_at_its_point (s : ℝ) (v : Spinor2) :
    jacobiValue (skyState s v) s = (0,0) := by
  rcases v with ⟨v0,v1⟩
  simp [jacobiValue, skyState]
  constructor <;> ring

/-- Conversely, every flat Jacobi field which vanishes at `s` has exactly the displayed
sky-plane form. -/
theorem jacobi_vanishing_parameterizes_sky
    (u : SkyState) (s : ℝ) (h : jacobiValue u s = (0,0)) :
    u = skyState s u.2 := by
  rcases u with ⟨⟨a0,a1⟩,⟨b0,b1⟩⟩
  have h0 : a0 + s*b0 = 0 := by
    exact congrArg (fun x : Spinor2 => x.1) h
  have h1 : a1 + s*b1 = 0 := by
    exact congrArg (fun x : Spinor2 => x.2) h
  apply Prod.ext
  · apply Prod.ext <;> simp [skyState] <;> linarith
  · rfl

/-- Exact membership criterion for the flat sky tangent plane. -/
theorem jacobi_vanishes_iff_in_sky_plane (u : SkyState) (s : ℝ) :
    jacobiValue u s = (0,0) ↔ ∃ v : Spinor2, u = skyState s v := by
  constructor
  · intro h
    exact ⟨u.2, jacobi_vanishing_parameterizes_sky u s h⟩
  · rintro ⟨v,rfl⟩
    exact skyState_vanishes_at_its_point s v

/-- Each sky tangent plane is isotropic for the Wronskian symplectic form. -/
theorem sky_plane_isotropic (s : ℝ) (v w : Spinor2) :
    skyOmega (skyState s v) (skyState s w) = 0 := by
  rcases v with ⟨v0,v1⟩
  rcases w with ⟨w0,w1⟩
  simp [skyOmega, skyState, dot2]
  ring

/-- The two screen parameters embed injectively into each sky plane. -/
theorem skyState_injective (s : ℝ) : Function.Injective (skyState s) := by
  intro v w h
  exact congrArg Prod.snd h

/-- Distinct affine parameters give distinct parametrized sky planes. -/
theorem sky_planes_separate_parameters
    (s t : ℝ)
    (h : ∀ v : Spinor2, skyState s v = skyState t v) :
    s = t := by
  have hv := h (1,0)
  have h0 := congrArg (fun u : SkyState => u.1.1) hv
  simp [skyState] at h0
  linarith

/-- Flat Jacobi flow: advance the value by `r` times the derivative. -/
def flatJacobiFlow (r : ℝ) (u : SkyState) : SkyState :=
  ((u.1.1 + r*u.2.1, u.1.2 + r*u.2.2),u.2)

/-- The flat Jacobi flow preserves the Wronskian symplectic form. -/
theorem flatJacobiFlow_preserves_omega (r : ℝ) (u v : SkyState) :
    skyOmega (flatJacobiFlow r u) (flatJacobiFlow r v) = skyOmega u v := by
  rcases u with ⟨⟨a0,a1⟩,⟨b0,b1⟩⟩
  rcases v with ⟨⟨c0,c1⟩,⟨d0,d1⟩⟩
  simp [skyOmega, flatJacobiFlow, dot2]
  ring

/-- Flowing the sky plane forward by `r` shifts its zero from `s` to `s-r`. -/
theorem flatJacobiFlow_skyState (r s : ℝ) (v : Spinor2) :
    flatJacobiFlow r (skyState s v) = skyState (s-r) v := by
  rcases v with ⟨v0,v1⟩
  apply Prod.ext
  · apply Prod.ext <;> simp [flatJacobiFlow, skyState] <;> ring
  · rfl

/-- The flat sky curve is therefore an orbit of symplectic Jacobi transport. -/
theorem flat_sky_curve_transport (r s : ℝ) :
    ∀ v : Spinor2,
      flatJacobiFlow r (skyState s v) = skyState (s-r) v := by
  intro v
  exact flatJacobiFlow_skyState r s v

end GppFlatSkyJacobiCurve
