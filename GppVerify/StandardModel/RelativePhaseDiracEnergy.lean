import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.StandardModel.GrassmannianDiracIntertwiner

/-!
# Relative complex orientation and the rest-Dirac energy sign

The project already contains the exact rest-Dirac quarter-cycle

    Uq = -i sigma1,

with `Uq^2 = -1`, obtained as a quotient of the elliptic Grassmannian tangent sector.
There is also a universal complex phase quarter-turn on the Dirac carrier,

    I0 = i 1.

These two complex structures commute.  Their product is not another complex structure:

    I0 Uq = sigma1 = beta,

and therefore squares to `+1`.

In the chiral two-component rest reduction, `beta=sigma1` is precisely the sign operator
whose two eigenspaces carry the `+mc^2` and `-mc^2` rest-energy branches.  Thus the
Dirac energy-sign involution is the *relative orientation* of two commuting quarter-turns.
Simultaneously reversing both quarter-turn orientations leaves beta fixed, while reversing
only one flips beta.

This is the exact matrix analogue of the binary relation `(c,t) ~ (-c,-t)` and the
invariant product `ct`, but no identification of either quarter-turn with electric charge
conjugation is asserted here.  The physical content proved here is narrower and stronger:
the Grassmannian `±i` modes selected by `Phi` land exactly in the two beta/rest-energy
branches.
-/

namespace GppRelativePhaseDiracEnergy

open GppGrassmannianDiracIntertwiner
open GppGrassmannianComplexDifferential

/-- Universal scalar complex quarter-turn `i 1` on the two-component Dirac carrier. -/
def phaseI : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0;
     0, Complex.I]

/-- Rest-energy sign involution in the chiral two-state reduction: `beta = sigma1`. -/
def betaRest : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1;
     1, 0]

/-- The universal phase operator is itself a complex structure. -/
theorem phaseI_sq_eq_neg_one :
    phaseI * phaseI = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [phaseI, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
       Complex.I_mul_I]

/-- The scalar phase quarter-turn commutes with the Grassmannian/Dirac quarter-turn. -/
theorem phaseI_commutes_Uq :
    phaseI * Uq = Uq * phaseI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [phaseI, Uq, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring

/-- Main relative-orientation identity: `i 1` times `-i sigma1` is `sigma1`. -/
theorem phaseI_mul_Uq_eq_betaRest :
    phaseI * Uq = betaRest := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [phaseI, Uq, betaRest, Matrix.mul_apply, Fin.sum_univ_two,
       Complex.I_mul_I] <;>
    ring

/-- The same product in the opposite order, because the two quarter-turns commute. -/
theorem Uq_mul_phaseI_eq_betaRest :
    Uq * phaseI = betaRest := by
  rw [← phaseI_commutes_Uq, phaseI_mul_Uq_eq_betaRest]

/-- The product of the two commuting complex structures is a real-sign involution. -/
theorem betaRest_sq_eq_one :
    betaRest * betaRest = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [betaRest, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Simultaneously reversing both quarter-turn orientations leaves their relative product
unchanged.  This is the exact matrix version of `(-c)(-t)=ct`. -/
theorem reverse_both_preserves_relative_orientation :
    (-phaseI) * (-Uq) = phaseI * Uq := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [phaseI, Uq, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring

/-- Reversing only the universal phase orientation flips the relative sign operator. -/
theorem reverse_phase_only_flips_relative_orientation :
    (-phaseI) * Uq = -(phaseI * Uq) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [phaseI, Uq, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring

/-- Reversing only the Grassmannian/Dirac quarter-turn likewise flips the relative sign. -/
theorem reverse_Uq_only_flips_relative_orientation :
    phaseI * (-Uq) = -(phaseI * Uq) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [phaseI, Uq, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring

/-- Canonical `+1` rest-energy-sign eigenvector. -/
def restPlus : Fin 2 → ℂ := ![1,1]

/-- Canonical `-1` rest-energy-sign eigenvector. -/
def restMinus : Fin 2 → ℂ := ![1,-1]

/-- `betaRest` fixes the positive branch. -/
theorem betaRest_restPlus :
    betaRest *ᵥ restPlus = restPlus := by
  ext i
  fin_cases i <;>
    norm_num [betaRest, restPlus, Matrix.mulVec, Fin.sum_univ_two]

/-- `betaRest` negates the negative branch. -/
theorem betaRest_restMinus :
    betaRest *ᵥ restMinus = -restMinus := by
  ext i
  fin_cases i <;>
    norm_num [betaRest, restMinus, Matrix.mulVec, Fin.sum_univ_two]

/-- The Grassmannian `-i` mode descends to the `+1` rest-energy-sign branch. -/
theorem betaRest_Phi_vNegI :
    betaRest *ᵥ (Phi *ᵥ vNegI) = Phi *ᵥ vNegI := by
  rw [Phi_vNegI]
  ext i
  fin_cases i <;>
    simp [betaRest, Matrix.mulVec, Fin.sum_univ_two] <;>
    ring

/-- The Grassmannian `+i` mode descends to the `-1` rest-energy-sign branch. -/
theorem betaRest_Phi_vI :
    betaRest *ᵥ (Phi *ᵥ vI) = -(Phi *ᵥ vI) := by
  rw [Phi_vI]
  ext i
  fin_cases i <;>
    simp [betaRest, Matrix.mulVec, Fin.sum_univ_two] <;>
    ring

/-- Equivalently, the two surviving Grassmannian modes differ only by the relative
orientation between the universal scalar phase `i` and the geometric quarter-cycle `Uq`:
`Uq` eigenvalue `-i` gives beta `+1`, while `+i` gives beta `-1`. -/
theorem grassmannian_phase_to_energy_sign :
    (betaRest *ᵥ (Phi *ᵥ vNegI) = Phi *ᵥ vNegI) ∧
    (betaRest *ᵥ (Phi *ᵥ vI) = -(Phi *ᵥ vI)) := by
  exact ⟨betaRest_Phi_vNegI, betaRest_Phi_vI⟩

end GppRelativePhaseDiracEnergy
