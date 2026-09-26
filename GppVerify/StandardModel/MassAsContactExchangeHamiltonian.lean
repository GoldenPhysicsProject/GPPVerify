import Mathlib.Tactic
import GppVerify.StandardModel.ContactDiracHadamardBridge
import GppVerify.StandardModel.ComptonZitterBeatBridge

/-!
# Mass as the coupling between the two ambitwistor/contact chiral halves

On the complexified contact screen the canonical factor exchange

    E : (Z_L,Z_R) -> (Z_R,Z_L)

is represented by the Pauli matrix

    sigma1 = beta.

But in the Weyl/chiral representation the rest Dirac Hamiltonian is exactly

    H_rest = m c^2 beta.

Therefore, after the explicit contact-to-Dirac identification already formalized in the
project, the rest mass term is literally the amplitude for exchanging the two chiral/contact
halves.  This gives a sharp finite-dimensional version of "mass as orientation coupling":

    H_rest Psi(contact u) = m c^2 Psi(exchange u).

The massless limit removes this coupling.  Squaring the exchange gives the identity, so

    H_rest^2 = m^2 c^4,

and the symmetric/antisymmetric combinations of the two chiral halves have energies
`+mc^2` and `-mc^2`.  Their relative phase therefore runs at `2mc^2/hbar`, the zitter beat
already proved in `ComptonZitterBeatBridge`.

This is exact Dirac/contact algebra.  It does not by itself prove a dynamical origin for the
numerical value of `m`, nor identify the contact halves with electric charge sectors.
-/

namespace GppMassAsContactExchangeHamiltonian

open GppAmbitwistorContactNeutralCone
open GppContactDiracHadamardBridge
open GppRelativePhaseDiracEnergy
open GppComptonZitterBeatBridge
open GppOrientationMassTime

/-- Contact factor exchange is exactly the Dirac `beta=sigma1` action after complexification. -/
theorem contactToDirac_exchangeHalves (u : ContactVector) :
    contactToDirac (exchangeHalves u) = betaRest *ᵥ contactToDirac u := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  ext i
  fin_cases i <;>
    simp [contactToDirac, exchangeHalves, betaRest, halfToComplex,
      Matrix.mulVec, Fin.sum_univ_two]

/-- Rest-energy scale as a complex scalar. -/
def restEnergyScale (m c : ℝ) : ℂ := ((m * c^2 : ℝ) : ℂ)

/-- Rest Hamiltonian acting on the two-component chiral carrier. -/
def restHamiltonianAct (m c : ℝ) (psi : Fin 2 → ℂ) : Fin 2 → ℂ :=
  restEnergyScale m c • (betaRest *ᵥ psi)

/-- Main contact statement: rest mass multiplies the canonical chiral-factor exchange. -/
theorem restHamiltonian_is_mass_times_contact_exchange
    (m c : ℝ) (u : ContactVector) :
    restHamiltonianAct m c (contactToDirac u) =
      restEnergyScale m c • contactToDirac (exchangeHalves u) := by
  rw [contactToDirac_exchangeHalves]
  rfl

/-- In the massless limit the rest coupling vanishes identically. -/
theorem massless_restHamiltonian_zero (c : ℝ) (psi : Fin 2 → ℂ) :
    restHamiltonianAct 0 c psi = 0 := by
  ext i
  simp [restHamiltonianAct, restEnergyScale]

/-- The symmetric combination of the two chiral halves has positive rest energy. -/
theorem restHamiltonian_restPlus (m c : ℝ) :
    restHamiltonianAct m c restPlus = restEnergyScale m c • restPlus := by
  rw [restHamiltonianAct, betaRest_restPlus]

/-- The antisymmetric combination has negative rest energy. -/
theorem restHamiltonian_restMinus (m c : ℝ) :
    restHamiltonianAct m c restMinus = (-restEnergyScale m c) • restMinus := by
  rw [restHamiltonianAct, betaRest_restMinus]
  ext i
  simp
  ring

/-- Applying the rest Hamiltonian twice gives the scalar `m^2 c^4` action. -/
theorem restHamiltonian_sq
    (m c : ℝ) (psi : Fin 2 → ℂ) :
    restHamiltonianAct m c (restHamiltonianAct m c psi) =
      (restEnergyScale m c * restEnergyScale m c) • psi := by
  rw [restHamiltonianAct, restHamiltonianAct]
  rw [Matrix.mulVec_smul]
  rw [← Matrix.mulVec_mulVec, betaRest_sq_eq_one]
  simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The two energy branches differ by exactly twice the Compton frequency after division by
`hbar`; this imports the already-proved beat identity into the contact-exchange picture. -/
theorem contact_exchange_energy_split_is_zitter_rate (m c hbar : ℝ) :
    positiveRestPhaseRate m c hbar - negativeRestPhaseRate m c hbar =
      zitterFrequency m c hbar := by
  exact restBeatRate_eq_zitterFrequency m c hbar

/-- Capstone: contact exchange, Dirac beta, and the rest-mass coupling are one finite operator. -/
theorem contact_exchange_is_rest_beta (u : ContactVector) :
    contactToDirac (exchangeHalves u) = betaRest *ᵥ contactToDirac u :=
  contactToDirac_exchangeHalves u

end GppMassAsContactExchangeHamiltonian
