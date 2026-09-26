import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.StandardModel.HalfFlipProposition
import GppVerify.CelestialHolography.ContactCliffordWeylBridge
import GppVerify.StandardModel.RelativePhaseDiracEnergy

/-!
# Contact Clifford matrix versus the Wigner-time matrix

The contact doublet carries two canonical involutions:

  E = sigma1       (exchange of the two contact/chiral halves),
  K = sigma3       (contact chirality/para-complex grading).

Their Clifford product is

  J = E K = [[0,-1],[1,0]] = - i sigma2,

with J^2=-1.  Standard spin-1/2 Wigner time reversal uses the same 2x2 matrix pattern,
up to sign, as the unitary core of the antiunitary operator `T=(i sigma2) C`.

This module proves the coordinate-level statement

  J C = - T

AFTER choosing an identification of the two abstract two-component carriers.  That is a
matrix coincidence/intertwiner candidate, not yet a physical identification: the contact
carrier indexes left/right chiral/contact data, whereas Wigner T acts on a physical spin
doublet.  Indeed the contact operation anticommutes with `beta=sigma1` and exchanges the
beta branches, so `ContactTimeCarrierNoGo` shows it cannot simply be the physical
rest-Hamiltonian time-reversal symmetry.

The correct use of this result is therefore structural: the same Clifford `J^2=-1` matrix
occurs in both places, and a future full spin/soldering intertwiner must explain whether and
how those carriers are related.
-/

namespace GppContactWignerTimeBridge

open scoped ComplexConjugate
open GppHalfFlip
open GppContactCliffordWeylBridge
open GppRelativePhaseDiracEnergy

/-- Entrywise complex conjugation on a two-component coordinate carrier. -/
def conjSpinor (psi : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![conj (psi 0), conj (psi 1)]

/-- Coordinate antiunitary built from the contact Clifford matrix `J` and conjugation. -/
def contactAntiT (psi : Fin 2 → ℂ) : Fin 2 → ℂ :=
  contactWeylMatrix *ᵥ conjSpinor psi

/-- Explicit component form of the coordinate antiunitary. -/
theorem contactAntiT_apply (psi : Fin 2 → ℂ) :
    contactAntiT psi = ![-conj (psi 1), conj (psi 0)] := by
  ext i
  fin_cases i <;>
    simp [contactAntiT, conjSpinor, contactWeylMatrix_explicit,
      Matrix.mulVec, Fin.sum_univ_two]

/-- Under the chosen coordinate identification, the contact antiunitary differs from the
project's Wigner-T convention only by the global sign `-1`.  The carrier identification is
external to this finite equality. -/
theorem contactAntiT_eq_neg_wignerT (psi1 psi2 : ℂ) :
    let psi : Fin 2 → ℂ := ![psi1,psi2]
    (contactAntiT psi 0, contactAntiT psi 1) =
      (-(wignerT psi1 psi2).1, -(wignerT psi1 psi2).2) := by
  simp [contactAntiT_apply, wignerT]

/-- The coordinate antiunitary squares to the central sign. -/
theorem contactAntiT_sq_neg (psi : Fin 2 → ℂ) :
    contactAntiT (contactAntiT psi) = -psi := by
  rw [contactAntiT_apply, contactAntiT_apply]
  ext i
  fin_cases i <;> simp [conjSpinor]

/-- The contact Clifford core anticommutes with the beta/contact-exchange sign operator. -/
theorem contactWeyl_anticommutes_beta :
    contactWeylMatrix * betaRest = -(betaRest * contactWeylMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [contactWeylMatrix_explicit, betaRest,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Algebraically the coordinate antiunitary exchanges the two beta branches.  This is
precisely why it is NOT, without another intertwiner, the physical Wigner-T action on the
rest-energy carrier. -/
theorem contactAntiT_restPlus :
    contactAntiT restPlus = -restMinus := by
  rw [contactAntiT_apply]
  ext i
  fin_cases i <;> norm_num [restPlus, restMinus]

/-- The opposite beta branch maps back. -/
theorem contactAntiT_restMinus :
    contactAntiT restMinus = restPlus := by
  rw [contactAntiT_apply]
  ext i
  fin_cases i <;> norm_num [restPlus, restMinus]

/-- Coordinate beta-branch exchange packaged as a single exact statement. -/
theorem contactAntiT_exchanges_beta_characters :
    (contactAntiT restPlus = -restMinus) ∧
    (contactAntiT restMinus = restPlus) := by
  exact ⟨contactAntiT_restPlus, contactAntiT_restMinus⟩

end GppContactWignerTimeBridge
