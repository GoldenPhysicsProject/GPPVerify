import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.CelestialHolography.AmbitwistorBicomplexOrientation
import GppVerify.StandardModel.RelativePhaseDiracEnergy

/-!
# From ambitwistor contact chirality to Dirac rest energy: the Hadamard bridge

The previous contact module showed that the para-complex left/right sign

    K(X,Y) = (X,-Y)

is the product of two commuting real complex structures.  The previous Dirac module showed
that the rest-energy sign

    beta = sigma1

is likewise the product of the universal scalar phase `i` and the Grassmannian/Dirac
quarter-cycle `Uq=-i sigma1`.

Here the two structures are connected explicitly.

Identify each real contact half `R^2` with one complex coordinate by

    (x0,x1) |-> x0 + i x1.

Then the contact para-complex involution becomes

    sigma3 = diag(1,-1).

The raw Hadamard matrix

    H0 = [[1,1],[1,-1]]

intertwines this contact/chirality basis with the rest-energy basis:

    H0 sigma3 = sigma1 H0 = beta H0.

Moreover

    H0^2 = 2 I.

Therefore the orthonormal basis change is forced to carry the normalization `1/sqrt(2)`.
The ubiquitous `sqrt(2)` here is not a fitted number: it is the normalization of the equal
left/right superpositions which diagonalize the rest Dirac Hamiltonian in the Weyl basis.

This is finite-dimensional exact algebra.  It does not yet identify contact factor exchange
with electric charge conjugation or with Wigner time reversal.
-/

namespace GppContactDiracHadamardBridge

open GppAmbitwistorContactNeutralCone
open GppAmbitwistorBicomplexOrientation
open GppRelativePhaseDiracEnergy

/-- Real two-plane written as one complex coordinate. -/
def halfToComplex (x : ContactHalf) : ℂ :=
  (x.1 : ℂ) + Complex.I * (x.2 : ℂ)

/-- Complexification of the two contact halves into a two-component Weyl/Dirac carrier. -/
def contactToDirac (u : ContactVector) : Fin 2 → ℂ :=
  ![halfToComplex u.1, halfToComplex u.2]

/-- The planar quarter-turn is exactly multiplication by `i`. -/
theorem halfToComplex_quarter2 (x : ContactHalf) :
    halfToComplex (quarter2 x) = Complex.I * halfToComplex x := by
  rcases x with ⟨x0,x1⟩
  simp [halfToComplex, quarter2, Complex.I_mul_I]
  ring

/-- Matrix of the contact relative complex structure after complexification. -/
def relativeJMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-Complex.I, 0;
      0, Complex.I]

/-- Matrix of the contact para-complex sign after complexification. -/
def sigma3Contact : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0;
     0, -1]

/-- The common contact quarter-turn becomes the universal scalar complex phase. -/
theorem contactToDirac_commonJ (u : ContactVector) :
    contactToDirac (commonJ u) = Complex.I • contactToDirac u := by
  rcases u with ⟨x,y⟩
  ext i
  fin_cases i <;>
    simp [contactToDirac, commonJ, halfToComplex_quarter2]

/-- The relative contact quarter-turn becomes `diag(-i,+i) = -i sigma3`. -/
theorem contactToDirac_relativeJ (u : ContactVector) :
    contactToDirac (relativeJ u) = relativeJMatrix *ᵥ contactToDirac u := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  ext i
  fin_cases i <;>
    simp [contactToDirac, relativeJ, relativeJMatrix, halfToComplex,
      quarter2, Matrix.mulVec, Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring

/-- The para-complex left/right sign becomes the Pauli matrix `sigma3`. -/
theorem contactToDirac_paraJ (u : ContactVector) :
    contactToDirac (paraJ u) = sigma3Contact *ᵥ contactToDirac u := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  ext i
  fin_cases i <;>
    simp [contactToDirac, paraJ, sigma3Contact, halfToComplex,
      Matrix.mulVec, Fin.sum_univ_two] <;>
    ring

/-- Unnormalized Hadamard change of basis from chirality (`sigma3`) to rest-energy (`sigma1`). -/
def hadamardRaw : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 1;
     1, -1]

/-- Exact basis-change intertwiner: `H0 sigma3 = beta H0`. -/
theorem hadamardRaw_intertwines_contact_and_energy :
    hadamardRaw * sigma3Contact = betaRest * hadamardRaw := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamardRaw, sigma3Contact, betaRest,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The raw Hadamard square is exactly `2 I`. -/
theorem hadamardRaw_sq :
    hadamardRaw * hadamardRaw =
      !![(2 : ℂ), 0;
         0, (2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamardRaw, Matrix.mul_apply, Fin.sum_univ_two]

/-- A scalar normalization `a` makes the Hadamard involutive exactly when `2 a^2 = 1`.
The positive real solution is `a=1/sqrt(2)`. -/
theorem scaled_hadamard_sq_one
    (a : ℂ) (ha : (2 : ℂ) * a * a = 1) :
    (a • hadamardRaw) * (a • hadamardRaw) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [hadamardRaw, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf at ha ⊢ <;>
    nlinarith [ha]

/-- Contact `+/-` basis vectors become equal left/right combinations under the raw
Hadamard transform.  The normalized versions therefore carry coefficients `1/sqrt(2)`. -/
def contactPlusBasis : Fin 2 → ℂ := ![1,0]
def contactMinusBasis : Fin 2 → ℂ := ![0,1]

/-- The `+` contact/chirality basis vector maps to the symmetric rest branch. -/
theorem hadamardRaw_contactPlus :
    hadamardRaw *ᵥ contactPlusBasis = restPlus := by
  ext i
  fin_cases i <;>
    norm_num [hadamardRaw, contactPlusBasis, restPlus,
      Matrix.mulVec, Fin.sum_univ_two]

/-- The `-` contact/chirality basis vector maps to the antisymmetric rest branch. -/
theorem hadamardRaw_contactMinus :
    hadamardRaw *ᵥ contactMinusBasis = restMinus := by
  ext i
  fin_cases i <;>
    norm_num [hadamardRaw, contactMinusBasis, restMinus,
      Matrix.mulVec, Fin.sum_univ_two]

/-- Capstone: the contact para-sign and the Dirac rest-energy sign are the same involution
in two bases, intertwined by `H0`. -/
theorem contact_chirality_to_dirac_energy_sign :
    hadamardRaw * sigma3Contact = betaRest * hadamardRaw :=
  hadamardRaw_intertwines_contact_and_energy

end GppContactDiracHadamardBridge
