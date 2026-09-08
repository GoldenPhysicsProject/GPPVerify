import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry
import GppVerify.StandardModel.GrassmannianDiracIntertwiner

/-!
# Null-ray Weyl quarter-turn, Grassmannian elliptic sector, and the Dirac two-state cycle

Three rank-two/order-four structures have appeared independently in the current program:

1. the null-ray Einstein/Sturm carrier has the standard Weyl representative

      w(x,p)=(-p,x),

   with `w^2=-1` and projective order two;

2. the universal Grassmannian tangent operator `L` has an elliptic two-plane spanned by
   `eSigma3,eSigma1`, on which `L^2=-1`;

3. the two-state rest-Dirac quarter-cycle is

      Uq=-i sigma1,

   with `Uq^2=-1`, `Uq^4=1`.

This file proves that these are not merely three abstract copies of `Z4`.  On the natural
elliptic embedding

    E(x,p)=x eSigma3 + p eSigma1,

one has exactly

    L E = E w.

After the fixed phase change

    B(x,p)=(i x,p),

one also has

    Uq B = B w.

Finally the already-defined Grassmannian quotient `Phi` restricts to

    Phi E = 2 B.

Thus the triangle commutes exactly:

        Grassmannian elliptic sector --L--> Grassmannian elliptic sector
                 | Phi                         | Phi
                 v                             v
             Dirac C^2 ------------Uq------> Dirac C^2

and both are phase-equivalent to the same null-ray Weyl quarter-turn.

This is a genuine algebraic bridge from the massless/null-ray projective geometry to the
massive two-state Dirac carrier.  It still does NOT identify this quarter-turn with a full
physical Spin(3,1) spatial rotation, nor does it by itself derive the spin-statistics
connection.  What it does prove is that the central deck sign `-1` and order-four lift are
the same finite representation-theoretic structure across all three carriers.
-/

namespace GppNullRayDiracWeylBridge

open GppEinsteinNullRaySL2Geometry
open GppGrassmannianComplexDifferential
open GppGrassmannianDiracIntertwiner

/-- Complex two-state phase embedding of a real null-ray state. -/
def rayToDirac (u : RayState) : Fin 2 → ℂ :=
  ![Complex.I * (u.1 : ℂ), (u.2 : ℂ)]

/-- Embed the null-ray state into the Grassmannian elliptic two-plane. -/
def rayToGrassmannianElliptic (u : RayState) : Fin 4 → ℂ :=
  fun j => (u.1 : ℂ) * eSigma3 j + (u.2 : ℂ) * eSigma1 j

/-- The null-ray Weyl action is `(-p,x)` in components. -/
theorem rayWeyl_apply (x p : ℝ) :
    act2 rayWeyl (x,p) = (-p,x) := by
  simp [act2, rayWeyl]

/-- The Grassmannian elliptic sector carries exactly the same Weyl quarter-turn. -/
theorem L_rayToGrassmannianElliptic (u : RayState) :
    L *ᵥ rayToGrassmannianElliptic u =
      rayToGrassmannianElliptic (act2 rayWeyl u) := by
  rcases u with ⟨x,p⟩
  ext i
  fin_cases i <;>
    simp [rayToGrassmannianElliptic, act2, rayWeyl, L,
      eSigma3, eSigma1, Matrix.mulVec, Fin.sum_univ_four] <;>
    ring

/-- After one fixed phase choice, the Dirac quarter-cycle is exactly the same Weyl action. -/
theorem Uq_rayToDirac (u : RayState) :
    Uq *ᵥ rayToDirac u = rayToDirac (act2 rayWeyl u) := by
  rcases u with ⟨x,p⟩
  ext i
  fin_cases i <;>
    simp [rayToDirac, act2, rayWeyl, Uq,
      Matrix.mulVec, Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring

/-- The Grassmannian quotient restricted to the elliptic ray plane is exactly twice the
phase embedding into the Dirac carrier. -/
theorem Phi_rayToGrassmannianElliptic (u : RayState) :
    Phi *ᵥ rayToGrassmannianElliptic u = 2 • rayToDirac u := by
  rcases u with ⟨x,p⟩
  ext i
  fin_cases i <;>
    simp [rayToGrassmannianElliptic, rayToDirac, Phi,
      eSigma3, eSigma1, Matrix.mulVec, Fin.sum_univ_four] <;>
    ring

/-- The complete triangle commutes on every null-ray state. -/
theorem nullRay_grassmannian_dirac_triangle (u : RayState) :
    Phi *ᵥ (L *ᵥ rayToGrassmannianElliptic u) =
      Uq *ᵥ (Phi *ᵥ rayToGrassmannianElliptic u) := by
  rw [← Matrix.mulVec_mulVec, Phi_mul_L_eq_Uq_mul_Phi, Matrix.mulVec_mulVec]

/-- Two null-ray Weyl turns give the central sign `-1`, transported into the Dirac carrier. -/
theorem two_weyl_turns_become_dirac_central_sign (u : RayState) :
    rayToDirac (act2 rayWeyl (act2 rayWeyl u)) =
      - rayToDirac u := by
  rcases u with ⟨x,p⟩
  ext i
  fin_cases i <;>
    simp [rayToDirac, act2, rayWeyl] <;>
    ring

/-- Four null-ray Weyl turns close exactly after transport to the Dirac carrier. -/
theorem four_weyl_turns_close_in_dirac (u : RayState) :
    rayToDirac
      (act2 rayWeyl (act2 rayWeyl (act2 rayWeyl (act2 rayWeyl u)))) =
      rayToDirac u := by
  rcases u with ⟨x,p⟩
  ext i
  fin_cases i <;>
    simp [rayToDirac, act2, rayWeyl]

end GppNullRayDiracWeylBridge
