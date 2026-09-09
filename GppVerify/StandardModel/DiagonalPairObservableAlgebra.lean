import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# Observable algebra of the diagonal (++/--) orientation pair

Restrict first to the two kinematic lifts

    |++>, |-->

of one relational matter class.  The diagonal reversal is the swap

    D = sigma_1.

There are two logically different notions of "invisible doubling":

1. If an observable is diagonal in the lift basis and invariant under `D`, then it is
   necessarily a scalar on this two-state sector.  Such an observable cannot distinguish
   `++` from `--` at all.

2. Merely requiring an arbitrary operator to commute with `D` is weaker.  The full
   commutant consists of matrices `[[a,b],[b,a]]`; the off-diagonal term can measure the
   relative coherence between the two lifts.  In particular `D` itself distinguishes the
   coherent symmetric state from the incoherent 50/50 mixture.

This is an important no-go/refinement: diagonal reversal symmetry alone does NOT make the
relative phase unobservable.  To make the doubling truly hidden one needs either a gauge
quotient, a superselection rule/locality restriction excluding lift-changing operators, or
some other dynamical reason the off-diagonal commutant is inaccessible.
-/

namespace GppDiagonalPairObservableAlgebra

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Diagonal reversal on the two lifts. -/
def liftSwap : M2C :=
  !![0,1;
     1,0]

/-- Observable diagonal in the microscopic lift basis. -/
def diagObservable (a b : ℂ) : M2C :=
  !![a,0;
     0,b]

/-- The diagonal reversal is an involution. -/
theorem liftSwap_sq :
    liftSwap * liftSwap = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [liftSwap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- A lift-diagonal observable commutes with the diagonal reversal iff it assigns the
same value to `++` and `--`. -/
theorem diagObservable_commutes_swap_iff (a b : ℂ) :
    diagObservable a b * liftSwap = liftSwap * diagObservable a b ↔ a = b := by
  constructor
  · intro h
    have h01 := congrArg (fun M : M2C => M 0 1) h
    simpa [diagObservable, liftSwap, Matrix.mul_apply, Fin.sum_univ_two] using h01
  · intro hab
    subst b
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagObservable, liftSwap, Matrix.mul_apply, Fin.sum_univ_two]

/-- Hence every diagonal and reversal-invariant observable is scalar on the pair. -/
theorem invariant_diagonal_is_scalar (a b : ℂ)
    (h : diagObservable a b * liftSwap = liftSwap * diagObservable a b) :
    diagObservable a b = a • (1 : M2C) := by
  have hab := (diagObservable_commutes_swap_iff a b).1 h
  subst b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true})
      [diagObservable, Matrix.one_apply]

/-- General commuting operators have equal diagonal entries and equal off-diagonal entries. -/
theorem commutes_swap_iff (O : M2C) :
    O * liftSwap = liftSwap * O ↔
      O 0 0 = O 1 1 ∧ O 0 1 = O 1 0 := by
  constructor
  · intro h
    constructor
    · have h01 := congrArg (fun M : M2C => M 0 1) h
      simpa [liftSwap, Matrix.mul_apply, Fin.sum_univ_two] using h01
    · have h00 := congrArg (fun M : M2C => M 0 0) h
      simpa [liftSwap, Matrix.mul_apply, Fin.sum_univ_two] using h00
  · rintro ⟨hdiag,hoff⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [liftSwap, Matrix.mul_apply, Fin.sum_univ_two, hdiag, hoff]

/-- Normal form for the full commutant of the swap. -/
theorem commuting_swap_normal_form (O : M2C)
    (h : O * liftSwap = liftSwap * O) :
    ∃ a b : ℂ, O = !![a,b;b,a] := by
  have hs := (commutes_swap_iff O).1 h
  refine ⟨O 0 0, O 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · simpa [hs.2]
  · simpa [hs.1]

/-- Two density matrices: coherent equal superposition and incoherent 50/50 mixture. -/
def coherentDensity : M2C :=
  !![(1/2 : ℂ), (1/2 : ℂ);
     (1/2 : ℂ), (1/2 : ℂ)]

def mixedDensity : M2C :=
  !![(1/2 : ℂ), 0;
     0, (1/2 : ℂ)]

/-- Two-dimensional trace. -/
def trace2 (A : M2C) : ℂ := A 0 0 + A 1 1

/-- Expectation functional `Tr(O rho)`. -/
def expectation (O rho : M2C) : ℂ := trace2 (O * rho)

/-- Any lift-diagonal observable gives identical statistics on the coherent equal
superposition and the incoherent 50/50 mixture. -/
theorem diagonal_cannot_see_coherence (a b : ℂ) :
    expectation (diagObservable a b) coherentDensity =
      expectation (diagObservable a b) mixedDensity := by
  simp [expectation, trace2, diagObservable, coherentDensity, mixedDensity,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The lift-changing swap DOES see the coherence: expectation one in the coherent state. -/
theorem swap_expectation_coherent :
    expectation liftSwap coherentDensity = 1 := by
  norm_num [expectation, trace2, liftSwap, coherentDensity,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- The same swap has zero expectation in the incoherent mixture. -/
theorem swap_expectation_mixed :
    expectation liftSwap mixedDensity = 0 := by
  norm_num [expectation, trace2, liftSwap, mixedDensity,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- Therefore reversal symmetry by itself is not enough to hide coherent doubling. -/
theorem commuting_observable_can_detect_coherence :
    (liftSwap * liftSwap = liftSwap * liftSwap) ∧
    expectation liftSwap coherentDensity ≠ expectation liftSwap mixedDensity := by
  constructor
  · rfl
  · rw [swap_expectation_coherent, swap_expectation_mixed]
    norm_num

/-- Group average onto the reversal-even sector. -/
def evenProjector : M2C := coherentDensity

/-- The group-average matrix is an idempotent projector. -/
theorem evenProjector_sq :
    evenProjector * evenProjector = evenProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [evenProjector, coherentDensity, Matrix.mul_apply, Fin.sum_univ_two]

/-- It is fixed by reversal on either side. -/
theorem evenProjector_swap_fixed :
    liftSwap * evenProjector = evenProjector ∧
    evenProjector * liftSwap = evenProjector := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [evenProjector, coherentDensity, liftSwap,
        Matrix.mul_apply, Fin.sum_univ_two]

end GppDiagonalPairObservableAlgebra
