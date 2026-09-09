import Mathlib.Tactic
import GppVerify.StandardModel.ChargedCARComplexOrientationNoGo

/-!
# Charged CAR charge reversal versus time reversal: exact two-complex-structure dictionary

Derezinski--Gerard's charged-fermion formalism makes a distinction that is almost exactly
what the orientation programme needs.  A charged phase space has its original complex
structure `I` (the U(1)/charge-phase structure).  Positive-energy quantization introduces

    q = sgn b,
    J = I q,
    h = |b|,

so `q = - I J` is the relative orientation of two commuting complex structures.

Their discrete symmetries act differently:

* charge reversal is anti-linear on the original phase space but LINEAR on the positive-
  energy one-particle space.  Therefore it reverses `I`, preserves `J`, and flips `q`;
* time reversal is anti-linear on BOTH phase space and one-particle space.  Therefore it
  reverses BOTH `I` and `J`, while preserving `q`.

The finite two-sector model below realizes those statements exactly.  This is a major
correction/refinement of the project's earlier Boolean language: the two signs underlying
physical charge are naturally COMPLEX ORIENTATIONS, not two independently measurable
particle labels.  Standard time reversal flips the two absolute orientations together and
leaves their relative charge unchanged.

The `T` below is only the charge/frequency-sector core and has square +1.  Physical spin-1/2
Wigner time reversal carries an additional spin factor with the familiar possible square
`-1`; the two must be tensored/intertwined, not identified by matrix size.
-/

namespace GppChargedCARChargeTimeComplexDictionary

open scoped ComplexConjugate
open GppChargedCARComplexOrientationNoGo

/-- Charge reversal core: conjugate and exchange the two relative-charge sectors. -/
def chargeC (v : V2) : V2 := ![conj (v 1), conj (v 0)]

/-- Time reversal core on the charge/frequency carrier: componentwise conjugation. -/
def timeT (v : V2) : V2 := conjV v

/-- The product CT is complex-linear sector exchange. -/
def CT (v : V2) : V2 := ![v 1, v 0]

 theorem chargeC_sq (v : V2) : chargeC (chargeC v) = v := by
  ext i
  fin_cases i <;> simp [chargeC]

 theorem timeT_sq (v : V2) : timeT (timeT v) = v := by
  exact conjV_involutive v

/-- On this finite core C and T commute. -/
theorem chargeC_timeT_commute (v : V2) : chargeC (timeT v) = timeT (chargeC v) := by
  ext i
  fin_cases i <;> simp [chargeC, timeT, conjV]

/-- Their product is the linear sector swap. -/
theorem chargeC_after_timeT_eq_CT (v : V2) : chargeC (timeT v) = CT v := by
  ext i
  fin_cases i <;> simp [chargeC, timeT, CT, conjV]

/-- CHARGE REVERSAL: anti-linear for the original U(1) complex structure. -/
theorem C_reverses_phaseI (v : V2) :
    chargeC (phaseI *ᵥ v) = (-phaseI) *ᵥ chargeC v := by
  ext i
  fin_cases i <;>
    simp [chargeC, phaseI, Matrix.mulVec, Fin.sum_univ_two]

/-- CHARGE REVERSAL: linear for the positive-energy complex structure J. -/
theorem C_preserves_energyJ (v : V2) :
    chargeC (energyJ *ᵥ v) = energyJ *ᵥ chargeC v := by
  rw [energyJ_explicit]
  ext i
  fin_cases i <;>
    simp [chargeC, Matrix.mulVec, Fin.sum_univ_two]

/-- Therefore charge reversal flips the relative product q=-IJ. -/
theorem C_flips_qSign (v : V2) :
    chargeC (qSign *ᵥ v) = (-qSign) *ᵥ chargeC v := by
  ext i
  fin_cases i <;>
    simp [chargeC, qSign, Matrix.mulVec, Fin.sum_univ_two]

/-- TIME REVERSAL: anti-linear for the original phase-space complex structure. -/
theorem T_reverses_phaseI (v : V2) :
    timeT (phaseI *ᵥ v) = (-phaseI) *ᵥ timeT v := by
  exact conjV_reverses_phaseI v

/-- TIME REVERSAL: also anti-linear for the positive-energy one-particle complex structure. -/
theorem T_reverses_energyJ (v : V2) :
    timeT (energyJ *ᵥ v) = (-energyJ) *ᵥ timeT v := by
  exact conjV_reverses_energyJ v

/-- Therefore time reversal preserves the relative charge grading. -/
theorem T_preserves_qSign (v : V2) :
    timeT (qSign *ᵥ v) = qSign *ᵥ timeT v := by
  exact conjV_preserves_qSign v

/-- CT is complex-linear on the original charged phase space. -/
theorem CT_preserves_phaseI (v : V2) :
    CT (phaseI *ᵥ v) = phaseI *ᵥ CT v := by
  ext i
  fin_cases i <;>
    simp [CT, phaseI, Matrix.mulVec, Fin.sum_univ_two]

/-- CT reverses the positive-energy complex structure. -/
theorem CT_reverses_energyJ (v : V2) :
    CT (energyJ *ᵥ v) = (-energyJ) *ᵥ CT v := by
  rw [energyJ_explicit]
  ext i
  fin_cases i <;>
    simp [CT, Matrix.mulVec, Fin.sum_univ_two]

/-- Hence CT flips charge, as expected from C while T itself preserves charge. -/
theorem CT_flips_qSign (v : V2) :
    CT (qSign *ᵥ v) = (-qSign) *ᵥ CT v := by
  ext i
  fin_cases i <;>
    simp [CT, qSign, Matrix.mulVec, Fin.sum_univ_two]

/-- Both C and T preserve the one-particle probability norm. -/
theorem C_preserves_normSq2 (v : V2) : normSq2 (chargeC v) = normSq2 v := by
  simp [normSq2, chargeC, add_comm]

 theorem T_preserves_normSq2 (v : V2) : normSq2 (timeT v) = normSq2 v := by
  exact conjV_preserves_normSq2 v

/-- Capstone: C is the one-orientation flip, T is the diagonal two-orientation flip, and
    physical charge is exactly the relative alignment that distinguishes them. -/
theorem charged_C_T_relative_orientation_capstone (v : V2) :
    chargeC (phaseI *ᵥ v) = (-phaseI) *ᵥ chargeC v ∧
    chargeC (energyJ *ᵥ v) = energyJ *ᵥ chargeC v ∧
    chargeC (qSign *ᵥ v) = (-qSign) *ᵥ chargeC v ∧
    timeT (phaseI *ᵥ v) = (-phaseI) *ᵥ timeT v ∧
    timeT (energyJ *ᵥ v) = (-energyJ) *ᵥ timeT v ∧
    timeT (qSign *ᵥ v) = qSign *ᵥ timeT v := by
  exact ⟨C_reverses_phaseI v, C_preserves_energyJ v, C_flips_qSign v,
    T_reverses_phaseI v, T_reverses_energyJ v, T_preserves_qSign v⟩

end GppChargedCARChargeTimeComplexDictionary
