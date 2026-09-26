import Mathlib.Tactic
import GppVerify.StandardModel.MassAsContactExchangeHamiltonian
import GppVerify.StandardModel.GrassmannianDiracIntertwiner

/-!
# The order-four spinor lift of an order-two contact-factor exchange

The contact/ruling exchange is an involution.  After complexification its matrix is

    E = sigma1 = beta,

so `E^2=1`.  The Grassmannian/Dirac quarter-cycle already present in the project is

    Uq = -i sigma1 = -i E.

Therefore `Uq` is precisely a phase-decorated lift of the geometric factor exchange:

    E^2 = +1,
    Uq^2 = -1,
    Uq^4 = +1.

On an actual contact state this says

    Uq Psi(u) = -i Psi(exchange u).

Thus an involution downstairs acquires the central spinorial sign after two lifted
applications.  This is exact finite algebra and is the correct structural pattern behind a
`Z2` geometric operation lifting to a `Z4` spinor operation.  Identifying this particular
lift with a physical spatial rotation still requires the separate Spin(3,1) rotation bridge;
that identification is not assumed here.
-/

namespace GppSpinLiftOfContactExchange

open GppRelativePhaseDiracEnergy
open GppGrassmannianDiracIntertwiner
open GppMassAsContactExchangeHamiltonian
open GppContactDiracHadamardBridge
open GppAmbitwistorContactNeutralCone

/-- The Dirac quarter-cycle is exactly `-i` times the contact exchange matrix `beta`. -/
theorem Uq_eq_negI_smul_betaRest :
    Uq = (-Complex.I) • betaRest := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uq, betaRest]

/-- Conversely, multiplying the quarter-cycle by the universal phase `i` recovers the
order-two exchange. -/
theorem phaseI_times_Uq_is_exchange :
    phaseI * Uq = betaRest :=
  phaseI_mul_Uq_eq_betaRest

/-- The geometric exchange itself has order two. -/
theorem beta_exchange_sq_one :
    betaRest * betaRest = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  betaRest_sq_eq_one

/-- The lifted exchange has the central spinor sign after two applications. -/
theorem lifted_exchange_sq_neg_one :
    Uq * Uq = -(1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  Uq_sq_eq_neg_one

/-- Four lifted exchanges close exactly. -/
theorem lifted_exchange_four_one :
    Uq * Uq * (Uq * Uq) = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  Uq_four_eq_one

/-- State-level bridge: one lifted exchange is contact-factor exchange accompanied by the
quarter phase `-i`. -/
theorem Uq_on_contact_state (u : ContactVector) :
    Uq *ᵥ contactToDirac u =
      (-Complex.I) • contactToDirac (exchangeHalves u) := by
  rw [contactToDirac_exchangeHalves]
  rw [Uq_eq_negI_smul_betaRest]
  simp [Matrix.smul_mulVec]

/-- Two lifted applications return to the same geometric factor ordering but acquire the
central minus sign. -/
theorem Uq_twice_on_contact_state (u : ContactVector) :
    Uq *ᵥ (Uq *ᵥ contactToDirac u) = - contactToDirac u := by
  rw [← Matrix.mulVec_mulVec, Uq_sq_eq_neg_one]
  simp

end GppSpinLiftOfContactExchange
