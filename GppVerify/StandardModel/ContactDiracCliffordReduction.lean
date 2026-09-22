import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.CelestialHolography.ContactCliffordWeylBridge
import GppVerify.StandardModel.MassAsContactExchangeHamiltonian

/-!
# The contact doublet is the two-state Weyl reduction of the Dirac Clifford algebra

After complexifying the two ambitwistor/contact halves, two matrices are already canonical:

    E = sigma1   (factor exchange),
    K = sigma3   (contact chirality).

In the standard Weyl representation of the Dirac algebra these are precisely the two-state
parts of

    gamma0  = sigma1 ⊗ 1,
    -gamma5 = sigma3 ⊗ 1

(up to the conventional overall sign chosen for `gamma5`).  Thus contact-factor exchange
has exactly the matrix action of parity on the left/right Weyl doublet, while `K` grades
chirality.  They anticommute.

The rest Hamiltonian is `m c^2 gamma0`, so mass is the parity-odd/chirality-mixing coupling
between the two contact halves.  The projectors

    (1 ± K)/2

are the two chiral projectors.  This supplies another exact role for `1/2`: it is forced by
projecting an involution onto its two eigenspaces.

This module states the matrix reduction only.  Full four-component gamma matrices, spatial
rotations, and the antiunitary C/T operators are not identified here.
-/

namespace GppContactDiracCliffordReduction

open GppContactCliffordWeylBridge
open GppRelativePhaseDiracEnergy

/-- Two-state `gamma0`/parity matrix in the Weyl left-right carrier. -/
def gamma0Reduced : Matrix (Fin 2) (Fin 2) ℂ := exchangeMatrix

/-- Two-state chirality grading, with sign convention chosen as `sigma3`. -/
def chiralityReduced : Matrix (Fin 2) (Fin 2) ℂ := chiralityMatrix

/-- The two canonical contact matrices satisfy the Clifford anticommutator. -/
theorem gamma0_chirality_anticommute :
    gamma0Reduced * chiralityReduced +
      chiralityReduced * gamma0Reduced = 0 := by
  rw [show gamma0Reduced * chiralityReduced =
      -(chiralityReduced * gamma0Reduced) by
    exact exchange_chirality_anticommute]
  simp

/-- Both generators square to `+1`. -/
theorem reduced_Clifford_squares :
    gamma0Reduced * gamma0Reduced = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    chiralityReduced * chiralityReduced = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  exact ⟨exchangeMatrix_sq_one, chiralityMatrix_sq_one⟩

/-- Chiral projector onto the `+1` contact-chirality sector. -/
def chiralProjectorPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + chiralityReduced)

/-- Chiral projector onto the `-1` sector. -/
def chiralProjectorMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) - chiralityReduced)

/-- The plus chiral projector is idempotent. -/
theorem chiralProjectorPlus_idempotent :
    chiralProjectorPlus * chiralProjectorPlus = chiralProjectorPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralProjectorPlus, chiralityReduced, chiralityMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The minus chiral projector is idempotent. -/
theorem chiralProjectorMinus_idempotent :
    chiralProjectorMinus * chiralProjectorMinus = chiralProjectorMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralProjectorMinus, chiralityReduced, chiralityMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The two chiral projectors resolve the identity. -/
theorem chiral_projectors_resolve_one :
    chiralProjectorPlus + chiralProjectorMinus =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralProjectorPlus, chiralProjectorMinus, chiralityReduced,
      chiralityMatrix, Matrix.one_apply]

/-- Factor exchange swaps the two chiral projectors. -/
theorem gamma0_swaps_chiral_projectors :
    gamma0Reduced * chiralProjectorPlus =
      chiralProjectorMinus * gamma0Reduced := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma0Reduced, exchangeMatrix, chiralProjectorPlus,
      chiralProjectorMinus, chiralityReduced, chiralityMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Mirror swapping relation. -/
theorem gamma0_swaps_chiral_projectors_opposite :
    gamma0Reduced * chiralProjectorMinus =
      chiralProjectorPlus * gamma0Reduced := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma0Reduced, exchangeMatrix, chiralProjectorPlus,
      chiralProjectorMinus, chiralityReduced, chiralityMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The rest-sign matrix used by the mass Hamiltonian is exactly reduced `gamma0`. -/
theorem betaRest_eq_gamma0Reduced :
    betaRest = gamma0Reduced := by
  rfl

/-- Therefore the mass coupling necessarily mixes the two chiral/contact eigenspaces. -/
theorem mass_exchange_is_chirality_flipping :
    gamma0Reduced * chiralProjectorPlus =
      chiralProjectorMinus * gamma0Reduced ∧
    gamma0Reduced * chiralProjectorMinus =
      chiralProjectorPlus * gamma0Reduced := by
  exact ⟨gamma0_swaps_chiral_projectors,
    gamma0_swaps_chiral_projectors_opposite⟩

end GppContactDiracCliffordReduction
