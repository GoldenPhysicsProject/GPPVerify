import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import GppVerify.StandardModel.SpinLiftOfContactExchange
import GppVerify.StandardModel.ComptonZitterBeatBridge

/-!
# Rest Compton evolution and the spin-half rotation subgroup are the same one-parameter matrix

In the two-state Weyl/chiral rest reduction,

    H_rest = m c^2 sigma1.

Writing `alpha = omega_C tau`, the exact time-evolution matrix is

    U_rest(alpha) = cos(alpha) I - i sin(alpha) sigma1.

The standard spin-half rotation about the same Pauli axis is

    R_x(theta) = cos(theta/2) I - i sin(theta/2) sigma1.

Therefore

    U_rest(alpha) = R_x(2 alpha),

or physically

    U_rest(tau) = R_x(2 omega_C tau).

This supplies an exact representation-theoretic locking between the Compton clock and the
spin double cover.  A Compton phase advance `alpha=pi/2` is a spatial-spin half-turn
`theta=pi` and equals the project's quarter-cycle `Uq=-i sigma1`; `alpha=pi` corresponds
to a `2pi` spin rotation and the central sign `-1`; `alpha=2pi` corresponds to `4pi` and
returns the spinor.

The theorem identifies the two matrix one-parameter subgroups.  It does not assert that a
resting particle literally rotates as a classical extended body.
-/

namespace GppComptonSpinRotationLock

open GppRelativePhaseDiracEnergy
open GppSpinLiftOfContactExchange
open GppGrassmannianDiracIntertwiner
open GppOrientationMassTime

/-- Exact two-state rest evolution as a function of the dimensionless Compton phase. -/
noncomputable def restEvolutionPhase (alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((Real.cos alpha : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
    ((-(Complex.I * ((Real.sin alpha : ℝ) : ℂ))) • betaRest)

/-- Standard spin-half rotation about the Pauli-1 axis. -/
noncomputable def spinRotationX (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  restEvolutionPhase (theta / 2)

/-- Main locking identity: rest phase `alpha` is spin rotation angle `2 alpha`. -/
theorem restEvolution_eq_spinRotation_doubleAngle (alpha : ℝ) :
    spinRotationX (2 * alpha) = restEvolutionPhase alpha := by
  simp [spinRotationX]

/-- In physical units the spin angle associated with proper time is `2 omega_C tau`. -/
theorem comptonProperTime_spinLock (m c hbar tau : ℝ) :
    spinRotationX (2 * comptonFrequency m c hbar * tau) =
      restEvolutionPhase (comptonFrequency m c hbar * tau) := by
  rw [show 2 * comptonFrequency m c hbar * tau =
      2 * (comptonFrequency m c hbar * tau) by ring]
  exact restEvolution_eq_spinRotation_doubleAngle _

/-- A quarter Compton phase is exactly the existing order-four Dirac/contact lift. -/
theorem quarterComptonPhase_eq_Uq :
    restEvolutionPhase (Real.pi / 2) = Uq := by
  rw [Uq_eq_negI_smul_betaRest]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [restEvolutionPhase, betaRest, Matrix.one_apply,
       Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Equivalently a physical spin half-turn is the same matrix `Uq`. -/
theorem spinPi_eq_Uq :
    spinRotationX Real.pi = Uq := by
  simpa [spinRotationX] using quarterComptonPhase_eq_Uq

/-- A `2pi` spin rotation gives the central fermionic sign. -/
theorem spinTwoPi_eq_neg_one :
    spinRotationX (2 * Real.pi) = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [spinRotationX, restEvolutionPhase, betaRest, Matrix.one_apply,
       Real.cos_pi, Real.sin_pi]

/-- A `4pi` spin rotation closes. -/
theorem spinFourPi_eq_one :
    spinRotationX (4 * Real.pi) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [spinRotationX, restEvolutionPhase, betaRest, Matrix.one_apply,
       Real.cos_two_pi, Real.sin_two_pi]

end GppComptonSpinRotationLock
