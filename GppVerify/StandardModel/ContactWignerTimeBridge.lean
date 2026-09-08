import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.StandardModel.HalfFlipProposition
import GppVerify.CelestialHolography.ContactCliffordWeylBridge
import GppVerify.StandardModel.RelativePhaseDiracEnergy

/-!
# Contact geometry and Wigner time reversal

The contact doublet carries two canonical involutions:

  E = sigma1       (exchange of the two contact/chiral halves),
  K = sigma3       (contact chirality/para-complex grading).

Their Clifford product is

  J = E K = [[0,-1],[1,0]] = - i sigma2,

with J^2=-1.  Standard spin-1/2 Wigner time reversal is antiunitary and can be written,
up to a physically irrelevant global phase convention, as

  T = (i sigma2) C,

where C denotes entrywise complex conjugation.  Hence the contact Clifford product is
exactly the unitary matrix core of Wigner time reversal up to sign:

  J C = - T.

This module proves that statement directly in components.  It also proves that the
antiunitary contact operation exchanges the beta=sigma1 rest-energy/frequency branches.
Thus the +/- exchange character supplied by the doubled contact/spinor geometry is not
merely a mnemonic for a time sign: Wigner time reversal actually reverses that character.

Semantic boundary: this is a two-component spin/contact theorem.  It does not identify
electric charge with either Lorentz SL(2) factor, and it does not by itself prove that the
full QFT CPT operator is exactly the product of gauge dualization with this finite carrier.
-/

namespace GppContactWignerTimeBridge

open scoped ComplexConjugate
open GppHalfFlip
open GppContactCliffordWeylBridge
open GppRelativePhaseDiracEnergy

/-- Entrywise complex conjugation on a two-component state. -/
def conjSpinor (psi : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![conj (psi 0), conj (psi 1)]

/-- Antiunitary contact time-reversal carrier: `J C`, where
`J = contactWeylMatrix = [[0,-1],[1,0]]`. -/
def contactAntiT (psi : Fin 2 → ℂ) : Fin 2 → ℂ :=
  contactWeylMatrix *ᵥ conjSpinor psi

/-- Explicit component form of the contact antiunitary operation. -/
theorem contactAntiT_apply (psi : Fin 2 → ℂ) :
    contactAntiT psi = ![-conj (psi 1), conj (psi 0)] := by
  ext i
  fin_cases i <;>
    simp [contactAntiT, conjSpinor, contactWeylMatrix_explicit,
      Matrix.mulVec, Fin.sum_univ_two]

/-- The contact antiunitary differs from the project's Wigner-T convention only by the
global phase/sign `-1`. -/
theorem contactAntiT_eq_neg_wignerT (psi1 psi2 : ℂ) :
    let psi : Fin 2 → ℂ := ![psi1,psi2]
    (contactAntiT psi 0, contactAntiT psi 1) =
      (-(wignerT psi1 psi2).1, -(wignerT psi1 psi2).2) := by
  simp [contactAntiT_apply, wignerT]

/-- As required for a spin-1/2 time-reversal lift, applying the antiunitary operation twice
gives the central fermionic sign. -/
theorem contactAntiT_sq_neg (psi : Fin 2 → ℂ) :
    contactAntiT (contactAntiT psi) = -psi := by
  rw [contactAntiT_apply, contactAntiT_apply]
  ext i
  fin_cases i <;> simp [conjSpinor]

/-- The unitary matrix core anticommutes with the rest-frequency sign operator beta. -/
theorem contactWeyl_anticommutes_beta :
    contactWeylMatrix * betaRest = -(betaRest * contactWeylMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [contactWeylMatrix_explicit, betaRest,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Therefore the contact/Wigner time reversal exchanges the two real canonical
positive/negative rest-frequency branches, up to the unavoidable spinor phase sign. -/
theorem contactAntiT_restPlus :
    contactAntiT restPlus = -restMinus := by
  rw [contactAntiT_apply]
  ext i
  fin_cases i <;> norm_num [restPlus, restMinus]

/-- The negative branch is sent back to the positive branch. -/
theorem contactAntiT_restMinus :
    contactAntiT restMinus = restPlus := by
  rw [contactAntiT_apply]
  ext i
  fin_cases i <;> norm_num [restPlus, restMinus]

/-- Frequency-sign reversal packaged as a single exact statement. -/
theorem contactAntiT_exchanges_beta_characters :
    (contactAntiT restPlus = -restMinus) ∧
    (contactAntiT restMinus = restPlus) := by
  exact ⟨contactAntiT_restPlus, contactAntiT_restMinus⟩

end GppContactWignerTimeBridge
