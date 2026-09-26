import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.CelestialHolography.AmbitwistorBicomplexOrientation
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry
import GppVerify.StandardModel.ContactDiracHadamardBridge

/-!
# Contact exchange and chirality generate the Weyl Z4 as a Clifford product

The flat ambitwistor contact screen has two canonical involutions:

* factor exchange `E(X,Y)=(Y,X)`;
* para-complex chirality `K(X,Y)=(X,-Y)`.

After complexifying each real contact half to one complex coordinate, these are exactly

    E = sigma1,
    K = sigma3.

They square to `+1` and anticommute.  Therefore their product is a complex structure:

    (E K)^2 = -1.

More strongly,

    E K = [[0,-1],[1,0]],

which is exactly the rank-one Weyl representative already used on the null-ray/Sturm
carrier.  Thus the order-four Weyl/spinorial carrier is not obtained by adjoining an
arbitrary second reflection: its two reflections are the *canonical contact-factor exchange*
and the *canonical contact chirality involution*.

This is an exact finite bridge between ambitwistor contact geometry and the project's
rank-one `SL(2)` Weyl geometry.  It does not yet identify `E` or `K` separately with
physical C, P, or T; that is a later discrete-symmetry dictionary problem.
-/

namespace GppContactCliffordWeylBridge

open GppAmbitwistorContactNeutralCone
open GppContactDiracHadamardBridge
open GppEinsteinNullRaySL2Geometry

/-- Matrix of canonical contact-factor exchange after complexification. -/
def exchangeMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,1;
     1,0]

/-- Matrix of canonical contact chirality/para-complex sign. -/
def chiralityMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1,0;
     0,-1]

/-- Their product. -/
def contactWeylMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  exchangeMatrix * chiralityMatrix

/-- Factor exchange is an involution. -/
theorem exchangeMatrix_sq_one :
    exchangeMatrix * exchangeMatrix = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exchangeMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Contact chirality is an involution. -/
theorem chiralityMatrix_sq_one :
    chiralityMatrix * chiralityMatrix = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralityMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The two canonical contact involutions anticommute. -/
theorem exchange_chirality_anticommute :
    exchangeMatrix * chiralityMatrix = -(chiralityMatrix * exchangeMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exchangeMatrix, chiralityMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Their Clifford product is exactly the real Weyl quarter-turn matrix. -/
theorem contactWeylMatrix_explicit :
    contactWeylMatrix =
      !![(0:ℂ),-1;
         1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [contactWeylMatrix, exchangeMatrix, chiralityMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Consequently the product squares to the central sign. -/
theorem contactWeylMatrix_sq_neg_one :
    contactWeylMatrix * contactWeylMatrix =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [contactWeylMatrix_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- And four applications close. -/
theorem contactWeylMatrix_four_one :
    contactWeylMatrix * contactWeylMatrix *
      (contactWeylMatrix * contactWeylMatrix) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [contactWeylMatrix_sq_neg_one]
  simp

/-- Complexification of contact factor exchange agrees with the previously formalized
Dirac rest-sign matrix `beta=sigma1`. -/
theorem exchangeMatrix_eq_betaRest :
    exchangeMatrix = GppRelativePhaseDiracEnergy.betaRest := by
  rfl

/-- Contact chirality agrees with the previously formalized `sigma3Contact`. -/
theorem chiralityMatrix_eq_sigma3Contact :
    chiralityMatrix = sigma3Contact := by
  rfl

/-- State-level contact statement: applying exchange after chirality acts by the Weyl
quarter-turn matrix on the complexified two-component carrier. -/
theorem contact_exchange_after_chirality_is_Weyl (u : ContactVector) :
    contactToDirac (exchangeHalves (paraJ u)) =
      contactWeylMatrix *ᵥ contactToDirac u := by
  rw [contactToDirac_exchangeHalves, contactToDirac_paraJ]
  rw [← Matrix.mulVec_mulVec]
  rfl

/-- The real `2x2` null-ray Weyl representative has the same coordinate matrix. -/
theorem same_coordinates_as_rayWeyl :
    let w := rayWeyl
    w.1 = 0 ∧ w.2.1 = -1 ∧ w.2.2.1 = 1 ∧ w.2.2.2 = 0 := by
  norm_num [rayWeyl]

end GppContactCliffordWeylBridge
