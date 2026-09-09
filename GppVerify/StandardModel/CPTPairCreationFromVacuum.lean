import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# CPT-paired matter creation from a neutral vacuum

This finite two-sheet fermion model isolates a mechanism which does NOT require a charge
half-flip.  Use the basis

    |00>, |10>, |01>, |11>

where the first occupation is relational matter on the + sheet and the second occupation is
relational matter on the - sheet.  Relative to one external convention the two sheet
species carry opposite conventional conjugacy charge, so

    Qconv = N+ - N-.

But both are matter relative to their own sheet orientation, so the relational matter count
is

    Nrel = N+ + N-.

The cross-sheet pair creator `Pdag` sends the vacuum directly to `|11>`.  It COMMUTES with
`Qconv`, is invariant under sheet exchange, and raises `Nrel` by two.  Thus an exactly
CPT/sheet-symmetric, conventionally neutral interaction can create two relational-matter
quanta from the vacuum without ever creating a local anti-aligned `+-` half-flip state.

This is the finite algebraic core of a possible Big-Bang production mechanism.  It does not
supply the cosmological mode functions, production rate, species spectrum, or observed
baryon abundance.
-/

namespace GppCPTPairCreationFromVacuum

abbrev M4C := Matrix (Fin 4) (Fin 4) ℂ
abbrev V4C := Fin 4 → ℂ

/-- Basis vectors in order vacuum, plus-sheet matter, minus-sheet matter, pair. -/
def vacuum : V4C := ![1,0,0,0]
def plusMatter : V4C := ![0,1,0,0]
def minusMatter : V4C := ![0,0,1,0]
def pairState : V4C := ![0,0,0,1]

/-- Conventional charge: opposite signs on the two sheet representatives. -/
def Qconv : M4C :=
  !![0,0,0,0;
     0,1,0,0;
     0,0,-1,0;
     0,0,0,0]

/-- Relational matter number: both sheets count positively. -/
def Nrel : M4C :=
  !![0,0,0,0;
     0,1,0,0;
     0,0,1,0;
     0,0,0,2]

/-- Cross-sheet pair creator: vacuum -> paired matter. -/
def Pdag : M4C :=
  !![0,0,0,0;
     0,0,0,0;
     0,0,0,0;
     1,0,0,0]

/-- Reverse pair annihilation. -/
def P : M4C :=
  !![0,0,0,1;
     0,0,0,0;
     0,0,0,0;
     0,0,0,0]

/-- Sheet/CPT label exchange: the one-particle sheet states swap while vacuum and the
    paired state are fixed. -/
def sheetSwap : M4C :=
  !![1,0,0,0;
     0,0,1,0;
     0,1,0,0;
     0,0,0,1]

/-- The pair creator does what its name says. -/
theorem pair_creator_on_vacuum : Pdag *ᵥ vacuum = pairState := by
  ext i
  fin_cases i <;>
    norm_num [Pdag, vacuum, pairState, Matrix.mulVec, Fin.sum_univ_succ]

/-- Vacuum and pair both have zero conventional cross-sheet charge. -/
theorem conventional_charge_neutral_endpoints :
    Qconv *ᵥ vacuum = 0 ∧ Qconv *ᵥ pairState = 0 := by
  constructor <;>
    ext i <;> fin_cases i <;>
      norm_num [Qconv, vacuum, pairState, Matrix.mulVec, Fin.sum_univ_succ]

/-- Pair creation exactly conserves the conventional charge generator. -/
theorem pair_creation_commutes_Qconv : Qconv * Pdag = Pdag * Qconv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qconv, Pdag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- But it creates two units of relational matter number. -/
theorem pair_creation_raises_relational_number :
    Nrel * Pdag - Pdag * Nrel = (2 : ℂ) • Pdag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Nrel, Pdag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The sheet exchange is an involution. -/
theorem sheetSwap_sq_one : sheetSwap * sheetSwap = (1 : M4C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sheetSwap, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Pair creation is invariant under the sheet/CPT label exchange. -/
theorem pair_creation_sheet_symmetric :
    sheetSwap * Pdag = Pdag * sheetSwap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sheetSwap, Pdag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The created pair itself is sheet symmetric. -/
theorem pair_state_sheet_symmetric : sheetSwap *ᵥ pairState = pairState := by
  ext i
  fin_cases i <;>
    norm_num [sheetSwap, pairState, Matrix.mulVec, Fin.sum_univ_succ]

/-- Capstone: a sheet-symmetric operator can create relational matter from a neutral vacuum
    while preserving conventional charge exactly. -/
theorem CPT_symmetric_neutral_creation_package :
    Pdag *ᵥ vacuum = pairState ∧
    Qconv *ᵥ vacuum = 0 ∧
    Qconv *ᵥ pairState = 0 ∧
    sheetSwap *ᵥ pairState = pairState := by
  exact ⟨pair_creator_on_vacuum,
    conventional_charge_neutral_endpoints.1,
    conventional_charge_neutral_endpoints.2,
    pair_state_sheet_symmetric⟩

end GppCPTPairCreationFromVacuum
