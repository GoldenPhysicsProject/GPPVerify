import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# Electric-charge flip versus U(1) gauge invariance

This finite module isolates the exact algebra behind a basic physical obstruction.
On a two-sector carrier with charge operator

    Q = diag(+1,-1),

a linear operator which exchanges the two charge sectors is

    F = sigma1.

Then F anticommutes with Q rather than commuting with it:

    Q F = - F Q.

Therefore F is not neutral under the charge grading.  In a theory whose physical local
observable algebra is required to commute with the unbroken electric-charge generator,
a bare charge-flip operator cannot itself be a gauge-invariant local observable.

This is the finite algebraic core of electric-charge superselection.  It does not by itself
formalize Gauss-law superselection in continuum QED, nor does it claim that charge can never
be redistributed between a subsystem and an environment.
-/

namespace GppChargeFlipGaugeObstruction

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev V2C := Fin 2 → ℂ

/-- Physical charge grading with eigenvalues +1 and -1. -/
def chargeQ : M2C := !![(1:ℂ),0;0,-1]

/-- Bare operator exchanging the two charge sectors. -/
def chargeFlip : M2C := !![0,1;1,0]

/-- Positive- and negative-charge basis states. -/
def plusState : V2C := ![1,0]
def minusState : V2C := ![0,1]

 theorem charge_plus : chargeQ *ᵥ plusState = plusState := by
  ext i
  fin_cases i <;> norm_num [chargeQ, plusState, Matrix.mulVec, Fin.sum_univ_two]

 theorem charge_minus : chargeQ *ᵥ minusState = -minusState := by
  ext i
  fin_cases i <;> norm_num [chargeQ, minusState, Matrix.mulVec, Fin.sum_univ_two]

/-- The bare flip exchanges opposite electric-charge sectors. -/
theorem flip_exchanges_charge_states :
    chargeFlip *ᵥ plusState = minusState ∧
    chargeFlip *ᵥ minusState = plusState := by
  constructor <;>
    ext i <;> fin_cases i <;>
      norm_num [chargeFlip, plusState, minusState, Matrix.mulVec, Fin.sum_univ_two]

/-- Charge flip anticommutes with the charge generator. -/
theorem chargeFlip_anticommutes :
    chargeQ * chargeFlip = -(chargeFlip * chargeQ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chargeQ, chargeFlip, Matrix.mul_apply, Fin.sum_univ_two]

/-- Hence the bare charge-flip map is not neutral/gauge-invariant with respect to Q. -/
theorem chargeFlip_not_commuting :
    chargeQ * chargeFlip ≠ chargeFlip * chargeQ := by
  intro h
  have hij := congrArg (fun M : M2C => M 0 1) h
  norm_num [chargeQ, chargeFlip, Matrix.mul_apply, Fin.sum_univ_two] at hij

/-- A Q-commuting operator cannot literally be the bare sector-exchange operator. -/
theorem gauge_neutral_operator_not_bare_flip
    (O : M2C) (hO : chargeQ * O = O * chargeQ) :
    O ≠ chargeFlip := by
  intro h
  subst O
  exact chargeFlip_not_commuting hO

end GppChargeFlipGaugeObstruction
