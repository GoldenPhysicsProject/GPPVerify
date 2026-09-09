import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# Charged Kahler geometry: physical charge as a relative complex orientation

Prior-art anchor: the charged-Kahler formalism reviewed by C. Gerard and C. D. Jaekel,
"Thermal Quantum Fields with Spatially Cut-off Interactions in 1+1 Space-time Dimensions"
(2004), Section 2.4 and the charged Klein-Gordon standard form in Section 8.  There one has
two commuting complex structures `i` and `j` and the charge operator is

    q = - i j,

with `q^2=1`.  In the standard charged Klein-Gordon representation,

    i = diag(i,i),
    j = diag(i,-i),
    q = diag(1,-1),

while the Hamiltonian is positive and identical on both charge sectors.

This is extremely close to the project's relational-orientation algebra.  It establishes
that "two commuting quarter-turn structures whose relative orientation is a physical Z2
charge" is not an ad-hoc construction: it is standard charged-field mathematics.

What remains conjectural in the GPP interpretation is the dictionary assigning one of these
complex structures to the proposed microscopic temporal/frequency orientation in the full
Dirac/twistor theory, and the global CPT/horizon interpretation.
-/

namespace GppChargedKahlerRelativeOrientation

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev V2C := Fin 2 → ℂ

/-- Kahler/one-particle complex structure in the standard two-sector form. -/
def dynI : M2C :=
  !![Complex.I,0;
     0,Complex.I]

/-- Charge/gauge complex structure. -/
def gaugeJ : M2C :=
  !![Complex.I,0;
     0,-Complex.I]

/-- Relative involution / physical charge operator `Q=-I J`. -/
def chargeQ : M2C := -(dynI * gaugeJ)

/-- Explicit standard form of the charge operator. -/
theorem chargeQ_explicit :
    chargeQ = !![(1:ℂ),0;0,-1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chargeQ, dynI, gaugeJ, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_mul_I]

/-- Both underlying orientations are complex structures. -/
theorem dynI_sq_neg_one : dynI * dynI = -(1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true})
      [dynI, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
       Complex.I_mul_I]

 theorem gaugeJ_sq_neg_one : gaugeJ * gaugeJ = -(1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true})
      [gaugeJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
       Complex.I_mul_I] <;> ring

/-- The two complex structures commute. -/
theorem dynI_gaugeJ_commute : dynI * gaugeJ = gaugeJ * dynI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynI, gaugeJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Their relative product is an involution. -/
theorem chargeQ_sq_one : chargeQ * chargeQ = (1 : M2C) := by
  rw [chargeQ_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Simultaneously reversing both complex orientations leaves physical charge unchanged. -/
theorem reverse_both_preserves_charge :
    -((-dynI) * (-gaugeJ)) = chargeQ := by
  simp [chargeQ]

/-- Reversing only one underlying orientation reverses physical charge. -/
theorem reverse_dyn_only_flips_charge :
    -((-dynI) * gaugeJ) = -chargeQ := by
  simp [chargeQ]

 theorem reverse_gauge_only_flips_charge :
    -(dynI * (-gaugeJ)) = -chargeQ := by
  simp [chargeQ]

/-- Positive and negative charge basis vectors. -/
def plusState : V2C := ![1,0]
def minusState : V2C := ![0,1]

 theorem chargeQ_plus : chargeQ *ᵥ plusState = plusState := by
  rw [chargeQ_explicit]
  ext i
  fin_cases i <;> norm_num [plusState, Matrix.mulVec, Fin.sum_univ_two]

 theorem chargeQ_minus : chargeQ *ᵥ minusState = -minusState := by
  rw [chargeQ_explicit]
  ext i
  fin_cases i <;> norm_num [minusState, Matrix.mulVec, Fin.sum_univ_two]

/-- Positive Hamiltonian with the same energy scale on both charge sectors. -/
def positiveHamiltonian (eps : ℝ) : M2C :=
  !![(eps:ℂ),0;
     0,(eps:ℂ)]

 theorem Hamiltonian_plus (eps : ℝ) :
    positiveHamiltonian eps *ᵥ plusState = (eps:ℂ) • plusState := by
  ext i
  fin_cases i <;>
    norm_num [positiveHamiltonian, plusState, Matrix.mulVec, Fin.sum_univ_two]

 theorem Hamiltonian_minus (eps : ℝ) :
    positiveHamiltonian eps *ᵥ minusState = (eps:ℂ) • minusState := by
  ext i
  fin_cases i <;>
    norm_num [positiveHamiltonian, minusState, Matrix.mulVec, Fin.sum_univ_two]

/-- Therefore opposite physical charge does not imply opposite physical energy. -/
theorem opposite_charge_same_positive_energy (eps : ℝ) :
    chargeQ *ᵥ plusState = plusState ∧
    chargeQ *ᵥ minusState = -minusState ∧
    positiveHamiltonian eps *ᵥ plusState = (eps:ℂ) • plusState ∧
    positiveHamiltonian eps *ᵥ minusState = (eps:ℂ) • minusState := by
  exact ⟨chargeQ_plus, chargeQ_minus, Hamiltonian_plus eps, Hamiltonian_minus eps⟩

/-- Charge conjugation swaps the two sectors. -/
def chargeConjugationCore : M2C :=
  !![0,1;
     1,0]

 theorem chargeConjugation_exchanges_states :
    chargeConjugationCore *ᵥ plusState = minusState ∧
    chargeConjugationCore *ᵥ minusState = plusState := by
  constructor <;>
    ext i <;> fin_cases i <;>
      norm_num [chargeConjugationCore, plusState, minusState,
        Matrix.mulVec, Fin.sum_univ_two]

/-- Charge conjugation anticommutes with the physical charge grading. -/
theorem chargeConjugation_anticommutes_Q :
    chargeConjugationCore * chargeQ = -(chargeQ * chargeConjugationCore) := by
  rw [chargeQ_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chargeConjugationCore, Matrix.mul_apply, Fin.sum_univ_two]

end GppChargedKahlerRelativeOrientation
