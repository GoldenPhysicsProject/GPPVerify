import Mathlib.Tactic
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry

/-!
# The rank-one SL(2) spine: Cartan scale, Haar inversion, Weyl Z4, and root weight two

The null-ray/Sturm carrier already contains a canonical `SL(2,R)` structure.  This file
makes its rank-one Lie-theoretic skeleton explicit.

Use the Cartan action

    a(b) : (x,p) -> (b^{-1} x, b p),

and the Weyl representative

    w : (x,p) -> (-p,x).

Then

    w^2 = -1,

so `w` has vector-level order four but projective order two.  More importantly,

    w a(b) w^{-1} = a(b^{-1}).

Thus the same Weyl element that carries the spinorial central sign acts on the positive
Cartan scale by multiplicative inversion, exactly the involution underlying Haar/Mellin
reflection.  The lower unipotent root subgroup

    n(t) = [[1,0],[t,1]]

obeys

    a(b) n(t) a(b)^{-1} = n(b^2 t),

so the root coordinate has Cartan weight two.

These are exact finite `SL(2)` identities.  The analytic statement that normalized
principal-series induction introduces the Weyl-vector/half-density shift is external
representation theory, but this module isolates the precise group action to which it
applies.
-/

namespace GppRankOneWeylHaarSpine

open GppEinsteinNullRaySL2Geometry
open GppGrassmannianGooglyDecomposition
open GppFlatNullWeylFiberGeometry

/-- Cartan scaling `diag(b^{-1},b)` on the null-ray state. -/
def cartanAct (b : ℝ) (u : RayState) : RayState :=
  (b⁻¹*u.1, b*u.2)

/-- Inverse Weyl action.  Since `w^2=-1`, this is `-w`. -/
def weylInvAct (u : RayState) : RayState := (u.2,-u.1)

/-- The displayed inverse really inverts the Weyl action. -/
theorem weyl_weylInv (u : RayState) :
    act2 rayWeyl (weylInvAct u) = u := by
  rcases u with ⟨x,p⟩
  rfl

/-- And in the other order. -/
theorem weylInv_weyl (u : RayState) :
    weylInvAct (act2 rayWeyl u) = u := by
  rcases u with ⟨x,p⟩
  rfl

/-- Main Weyl/Cartan relation: conjugation by the order-four representative inverts the
multiplicative scale. -/
theorem weyl_conjugates_Cartan_to_inverse
    (b : ℝ) (hb : b ≠ 0) (u : RayState) :
    act2 rayWeyl (cartanAct b (weylInvAct u)) = cartanAct b⁻¹ u := by
  rcases u with ⟨x,p⟩
  simp [cartanAct, weylInvAct, act2, rayWeyl, hb]

/-- Cartan scaling preserves the Wronskian for nonzero scale. -/
theorem cartan_preserves_omega
    (b : ℝ) (hb : b ≠ 0) (u v : RayState) :
    omega (cartanAct b u) (cartanAct b v) = omega u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [omega, cartanAct, hb]
  field_simp [hb]
  ring

/-- The lower-unipotent root action in state coordinates. -/
def lowerRootAct (t : ℝ) (u : RayState) : RayState :=
  act2 (rayUnipotent t) u

/-- Cartan conjugation scales the lower-root parameter by `b^2`. -/
theorem Cartan_conjugates_root_weight_two
    (b t : ℝ) (hb : b ≠ 0) (u : RayState) :
    cartanAct b (lowerRootAct t (cartanAct b⁻¹ u)) =
      lowerRootAct (b^2*t) u := by
  rcases u with ⟨x,p⟩
  simp [cartanAct, lowerRootAct, act2, rayUnipotent, hb]
  field_simp [hb]
  ring

/-- The Weyl representative simultaneously exhibits the central spinorial sign. -/
theorem Weyl_Z4_and_Haar_inversion_package
    (b : ℝ) (hb : b ≠ 0) (u : RayState) :
    act2 rayWeyl (act2 rayWeyl u) = scaleSpinor (-1) u ∧
    act2 rayWeyl (cartanAct b (weylInvAct u)) = cartanAct b⁻¹ u := by
  exact ⟨rayWeyl_sq_central_sign u,
    weyl_conjugates_Cartan_to_inverse b hb u⟩

end GppRankOneWeylHaarSpine
