import Mathlib.Tactic
import GppVerify.StandardModel.ContactWignerTimeBridge
import GppVerify.StandardModel.MassAsContactExchangeHamiltonian

/-!
# No-go: the contact L/R doublet is not by itself the physical Wigner-time spin doublet

The previous matrix comparison found that the contact Clifford product

  J = E K = [[0,-1],[1,0]]

has the same 2x2 coordinate form, up to sign, as the unitary core `i sigma2` appearing in
spin-1/2 Wigner time reversal.  That coordinate coincidence is useful but it is NOT yet a
physical identification, because the two 2-component carriers have different meanings:

* the contact/Dirac reduction indexes left/right chiral halves and has
  `H_rest = m c^2 beta`, `beta=E=sigma1`;
* the usual Wigner-T `i sigma2 K` acts on the physical spin doublet and preserves a
  time-reversal-even rest Hamiltonian.

On the contact chiral-energy carrier, `J` anticommutes with `beta`.  Therefore the
antiunitary `J C` exchanges the +/- beta/rest-frequency branches.  For nonzero rest-energy
scale this cannot simultaneously be a symmetry commuting with `H_rest`.

This is an important negative result: the project's time-orientation sign must not be
identified naively with the beta/rest-energy character merely because the same 2x2 matrix
appears.  A physical T dictionary needs an additional intertwiner/real structure (for
example the Lorentzian soldering/time-orientation structure) separating spin action from
chiral/frequency action.
-/

namespace GppContactTimeCarrierNoGo

open GppContactWignerTimeBridge
open GppContactCliffordWeylBridge
open GppRelativePhaseDiracEnergy
open GppMassAsContactExchangeHamiltonian

/-- The contact Clifford core does not commute with the beta/rest-energy sign operator. -/
theorem contactWeyl_not_commute_beta :
    contactWeylMatrix * betaRest ≠ betaRest * contactWeylMatrix := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [contactWeylMatrix_explicit, betaRest,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- In fact it anticommutes, so conjugation by the contact Clifford core flips beta. -/
theorem contactWeyl_conjugates_beta_to_negative :
    contactWeylMatrix * betaRest * (-contactWeylMatrix) = -betaRest := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [contactWeylMatrix_explicit, betaRest,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Algebraic obstruction to calling the contact antiunitary a time-reversal symmetry of a
nonzero rest Hamiltonian: if a nonzero scalar multiple of beta were invariant under this
unitary-core conjugation, the scalar would have to vanish. -/
theorem contact_core_rest_invariance_forces_zero (mu : ℂ)
    (hInv : contactWeylMatrix * (mu • betaRest) * (-contactWeylMatrix)
      = mu • betaRest) :
    mu = 0 := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hInv
  norm_num [contactWeylMatrix_explicit, betaRest,
    Matrix.mul_apply, Fin.sum_univ_two] at h00 ⊢
  linarith

/-- Therefore the beta character is best read here as a chiral/frequency exchange character,
not yet as the physical Wigner-time orientation bit. -/
theorem contact_frequency_character_is_not_time_even :
    contactWeylMatrix * betaRest ≠ betaRest * contactWeylMatrix :=
  contactWeyl_not_commute_beta

end GppContactTimeCarrierNoGo
