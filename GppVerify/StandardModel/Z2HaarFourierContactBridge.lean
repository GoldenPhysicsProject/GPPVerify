import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.StandardModel.ContactDiracHadamardBridge
import GppVerify.CelestialHolography.ContactCliffordWeylBridge

/-!
# Finite Haar/Fourier theory of the two contact orientations

The canonical contact-factor exchange generates the two-element group `Z2`.  On the basis
`{|L>,|R>}` its nontrivial element is the swap matrix

    E = sigma1.

The normalized Haar measure on a two-element group assigns weight `1/2` to each element.
Accordingly the two character projectors are

    P_+ = (I+E)/2,
    P_- = (I-E)/2.

They are complementary idempotents and project onto the symmetric/antisymmetric exchange
characters.  The character table is the raw Hadamard matrix

    H0 = [[1,1],[1,-1]],

with `H0^2=2I`; its unitary normalization therefore requires `1/sqrt(2)`.

This gives exact, non-numerological roles to both `1/2` and `sqrt(2)` inside the same
orientation sector:

* `1/2` is normalized Haar averaging over the two orientations;
* `1/sqrt(2)` is the corresponding unitary Fourier normalization.

The Dirac rest-energy branches are precisely the two `Z2` characters because the rest mass
Hamiltonian is proportional to `E`.
-/

namespace GppZ2HaarFourierContactBridge

open GppRelativePhaseDiracEnergy
open GppContactDiracHadamardBridge
open GppContactCliffordWeylBridge

/-- Normalized Haar-average projector onto the trivial character of contact exchange. -/
def haarPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + exchangeMatrix))

/-- Complementary projector onto the sign character. -/
def haarMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) - exchangeMatrix))

/-- Haar projectors sum to the identity. -/
theorem haarPlus_add_haarMinus_one :
    haarPlus + haarMinus = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [haarPlus, haarMinus, exchangeMatrix, Matrix.one_apply]

/-- The trivial-character Haar average is idempotent. -/
theorem haarPlus_idempotent :
    haarPlus * haarPlus = haarPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [haarPlus, exchangeMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The sign-character projector is idempotent. -/
theorem haarMinus_idempotent :
    haarMinus * haarMinus = haarMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [haarMinus, exchangeMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The two character sectors are orthogonal algebraically. -/
theorem haarPlus_haarMinus_zero :
    haarPlus * haarMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [haarPlus, haarMinus, exchangeMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The positive rest branch is fixed by normalized Haar averaging. -/
theorem haarPlus_restPlus :
    haarPlus *ᵥ restPlus = restPlus := by
  ext i
  fin_cases i <;>
    norm_num [haarPlus, exchangeMatrix, restPlus, Matrix.mulVec,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The positive branch is killed by the sign-character projector. -/
theorem haarMinus_restPlus_zero :
    haarMinus *ᵥ restPlus = 0 := by
  ext i
  fin_cases i <;>
    norm_num [haarMinus, exchangeMatrix, restPlus, Matrix.mulVec,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The negative rest branch is the sign character. -/
theorem haarMinus_restMinus :
    haarMinus *ᵥ restMinus = restMinus := by
  ext i
  fin_cases i <;>
    norm_num [haarMinus, exchangeMatrix, restMinus, Matrix.mulVec,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The negative branch is killed by the trivial-character Haar average. -/
theorem haarPlus_restMinus_zero :
    haarPlus *ᵥ restMinus = 0 := by
  ext i
  fin_cases i <;>
    norm_num [haarPlus, exchangeMatrix, restMinus, Matrix.mulVec,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The Hadamard character table diagonalizes the exchange generator: Fourier transform
turns translation/swap into the character-sign matrix. -/
theorem hadamard_diagonalizes_exchange :
    hadamardRaw * exchangeMatrix = sigma3Contact * hadamardRaw := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamardRaw, exchangeMatrix, sigma3Contact,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Conversely it turns the chirality/sign basis into the exchange basis. -/
theorem hadamard_conjugacy_other_direction :
    hadamardRaw * sigma3Contact = exchangeMatrix * hadamardRaw := by
  simpa [exchangeMatrix_eq_betaRest] using
    hadamardRaw_intertwines_contact_and_energy

/-- The raw finite Fourier matrix has squared norm factor exactly two. -/
theorem finiteFourier_raw_square_two :
    hadamardRaw * hadamardRaw =
      !![(2 : ℂ),0;
         0,(2 : ℂ)] :=
  hadamardRaw_sq

/-- Capstone: the constants `1/2` and raw Fourier norm `2` occur in the same normalized
Haar/character decomposition of the contact orientation doublet. -/
theorem z2_Haar_character_resolution :
    haarPlus + haarMinus = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    haarPlus * haarMinus = 0 := by
  exact ⟨haarPlus_add_haarMinus_one, haarPlus_haarMinus_zero⟩

end GppZ2HaarFourierContactBridge
