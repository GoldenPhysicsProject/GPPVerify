import Mathlib.Tactic

/-!
# *Which Way Is Forward?*: Pauli strings (G4 concrete layer, engine)

The concrete engine for the parent charge-conjugation signs. A Pauli
string of length `n` is a function `Fin n → Pauli`; its matrix is the
Kronecker product of the letter matrices over a recursive index type.
All cross-string products live at a fixed `n`, so the dependent index
type never has to be cast.

Banked facts:
* `letterMatrix_mul`: the slot product table, all sixteen entries,
  with phases in `{1, i, -1, -i}`.
* `letterMatrix_conj`: entrywise conjugation eigenvalue per letter
  (`Y` is the only imaginary letter).
* `stringMatrix_mul`: a product of two strings is the accumulated
  phase times the slotwise-product string.
* `stringMatrix_sq`: every string squares to `1`.
* `stringMatrix_conj`: conjugation of a string is the product of the
  letters' conjugation signs times the string.
* `stringMatrix_anticommute_of_odd`: two strings anticommute when the
  number of slots with anticommuting letter pairs is odd.

Everything the family layer needs is reduced here to slot data; the
families themselves are finite generator functions fed through these
lemmas and layer A (`WhichWayForwardFamilySigns`).
-/

namespace GppWhichWayForwardPauliStrings

/-- A Pauli letter. -/
inductive Pauli | I | X | Y | Z
  deriving DecidableEq, Repr

instance : Fintype Pauli :=
  ⟨{Pauli.I, Pauli.X, Pauli.Y, Pauli.Z}, by intro x; cases x <;> simp⟩

open Pauli Matrix
open scoped Kronecker

/-- The letter as a `2 × 2` complex matrix. -/
def letterMatrix : Pauli → Matrix (Fin 2) (Fin 2) ℂ
  | I => 1
  | X => !![0, 1; 1, 0]
  | Y => !![0, -Complex.I; Complex.I, 0]
  | Z => !![1, 0; 0, -1]

/-- The slot product: `slotMul a b = (phase, letter)` with
`letterMatrix a * letterMatrix b = phase • letterMatrix letter`. -/
def slotMul : Pauli → Pauli → ℂ × Pauli
  | I, b => (1, b)
  | a, I => (1, a)
  | X, X => (1, I)
  | Y, Y => (1, I)
  | Z, Z => (1, I)
  | X, Y => (Complex.I, Z)
  | Y, X => (-Complex.I, Z)
  | Y, Z => (Complex.I, X)
  | Z, Y => (-Complex.I, X)
  | Z, X => (Complex.I, Y)
  | X, Z => (-Complex.I, Y)

/-- Whether two letters anticommute as matrices: distinct non-identity
letters. -/
def slotAnti : Pauli → Pauli → Bool
  | I, _ => false
  | _, I => false
  | X, X => false
  | Y, Y => false
  | Z, Z => false
  | _, _ => true

/-- The conjugation sign of a letter: `Y` is imaginary, the rest real. -/
def slotConj : Pauli → ℂ
  | Y => -1
  | _ => 1

/-- The slot product table, all sixteen entries. -/
theorem letterMatrix_mul (a b : Pauli) :
    letterMatrix a * letterMatrix b
      = (slotMul a b).1 • letterMatrix (slotMul a b).2 := by
  fin_cases a <;> fin_cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [letterMatrix, slotMul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;> ring

/-- Entrywise conjugation of a letter is its sign times itself. -/
theorem letterMatrix_conj (p : Pauli) :
    (letterMatrix p).map (starRingEnd ℂ) = slotConj p • letterMatrix p := by
  fin_cases p <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [letterMatrix, slotConj, Matrix.map_apply, Matrix.smul_apply,
      Complex.ext_iff]

/-- Swapping a slot product multiplies the phase by `-1` exactly at
anticommuting slots, and never changes the resulting letter. -/
theorem slotMul_swap (a b : Pauli) :
    (slotMul b a).2 = (slotMul a b).2
      ∧ (slotMul b a).1
        = (if slotAnti a b then -1 else 1) * (slotMul a b).1 := by
  fin_cases a <;> fin_cases b <;> simp [slotMul, slotAnti] <;> ring

/-- Every slot phase is nonzero. -/
theorem slotMul_phase_ne_zero (a b : Pauli) : (slotMul a b).1 ≠ 0 := by
  fin_cases a <;> fin_cases b <;> simp [slotMul]

/-- A slot squares to the identity letter with phase `1`. -/
theorem slotMul_self (a : Pauli) : slotMul a a = (1, Pauli.I) := by
  fin_cases a <;> rfl

/-- The recursive index type: `idx (m+1) = Fin 2 × idx m`. -/
def idx : ℕ → Type
  | 0 => PUnit
  | m + 1 => Fin 2 × idx m

instance decEqIdx : (m : ℕ) → DecidableEq (idx m)
  | 0 => (inferInstance : DecidableEq PUnit)
  | m + 1 => @instDecidableEqProd (Fin 2) (idx m) inferInstance (decEqIdx m)

instance fintypeIdx : (m : ℕ) → Fintype (idx m)
  | 0 => PUnit.fintype
  | m + 1 => @instFintypeProd (Fin 2) (idx m) inferInstance (fintypeIdx m)

/-- The matrix of a Pauli string, by Kronecker recursion on the
number of slots. -/
def stringMatrix : (n : ℕ) → (Fin n → Pauli) → Matrix (idx n) (idx n) ℂ
  | 0, _ => 1
  | m + 1, f => (letterMatrix (f 0)) ⊗ₖ (stringMatrix m (fun i => f i.succ))

theorem stringMatrix_zero (f : Fin 0 → Pauli) : stringMatrix 0 f = 1 := rfl

theorem stringMatrix_succ {m : ℕ} (f : Fin (m + 1) → Pauli) :
    stringMatrix (m + 1) f = (letterMatrix (f 0)) ⊗ₖ (stringMatrix m (fun i => f i.succ)) := rfl

/-- The slotwise product letter function. -/
def zipLetter {n : ℕ} (f g : Fin n → Pauli) (i : Fin n) : Pauli :=
  (slotMul (f i) (g i)).2

/-- The accumulated phase of a slotwise product. -/
def phaseF {n : ℕ} (f g : Fin n → Pauli) : ℂ :=
  ∏ i, (slotMul (f i) (g i)).1

/-- The number of slots at which the two strings' letters anticommute. -/
def antiCountF {n : ℕ} (f g : Fin n → Pauli) : ℕ :=
  ∑ i, (if slotAnti (f i) (g i) then 1 else 0)

/-- The conjugation phase of a string: product of the letters' signs. -/
def conjPhaseF {n : ℕ} (f : Fin n → Pauli) : ℂ :=
  ∏ i, slotConj (f i)

theorem phaseF_succ {m : ℕ} (f g : Fin (m + 1) → Pauli) :
    phaseF f g = (slotMul (f 0) (g 0)).1
      * phaseF (fun i => f i.succ) (fun i => g i.succ) :=
  Fin.prod_univ_succ _

theorem antiCountF_succ {m : ℕ} (f g : Fin (m + 1) → Pauli) :
    antiCountF f g = (if slotAnti (f 0) (g 0) then 1 else 0)
      + antiCountF (fun i => f i.succ) (fun i => g i.succ) :=
  Fin.sum_univ_succ _

theorem conjPhaseF_succ {m : ℕ} (f : Fin (m + 1) → Pauli) :
    conjPhaseF f = slotConj (f 0)
      * conjPhaseF (fun i => f i.succ) :=
  Fin.prod_univ_succ _

/-- A string of identity letters is the identity matrix. -/
theorem stringMatrix_const_I :
    ∀ n : ℕ, stringMatrix n (fun _ => Pauli.I) = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    show (letterMatrix ((fun _ => Pauli.I) 0)) ⊗ₖ
        (stringMatrix m (fun i => (fun _ => Pauli.I) i.succ)) = 1
    rw [ih]
    have hI : letterMatrix Pauli.I = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [hI]
    exact Matrix.one_kronecker_one

/-- The product of two strings is the accumulated phase times the
slotwise-product string. -/
theorem stringMatrix_mul :
    ∀ (n : ℕ) (f g : Fin n → Pauli),
      stringMatrix n f * stringMatrix n g
        = phaseF f g • stringMatrix n (zipLetter f g) := by
  intro n
  induction n with
  | zero =>
    intro f g
    rw [stringMatrix_zero, stringMatrix_zero]
    simp [phaseF, stringMatrix_zero]
  | succ m ih =>
    intro f g
    have hhead : zipLetter f g 0 = (slotMul (f 0) (g 0)).2 := rfl
    have htail : (fun i => zipLetter f g i.succ)
        = zipLetter (fun i => f i.succ) (fun i => g i.succ) := rfl
    show (letterMatrix (f 0)) ⊗ₖ (stringMatrix m (fun i => f i.succ))
        * ((letterMatrix (g 0)) ⊗ₖ (stringMatrix m (fun i => g i.succ)))
      = phaseF f g • ((letterMatrix (zipLetter f g 0)) ⊗ₖ
          (stringMatrix m (fun i => zipLetter f g i.succ)))
    rw [htail, hhead, ← Matrix.mul_kronecker_mul, letterMatrix_mul, ih,
      phaseF_succ]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- Every Pauli string squares to the identity. -/
theorem stringMatrix_sq (n : ℕ) (f : Fin n → Pauli) :
    stringMatrix n f * stringMatrix n f = 1 := by
  have hzip : zipLetter f f = fun _ => Pauli.I := by
    funext i
    simp [zipLetter, slotMul_self]
  have hph : phaseF f f = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [slotMul_self]
  rw [stringMatrix_mul, hzip, hph, stringMatrix_const_I, one_smul]

/-- A default index in `idx n`, for entry evaluation. -/
def idxDefault : (n : ℕ) → idx n
  | 0 => PUnit.unit
  | m + 1 => (0, idxDefault m)

/-- A Pauli string is nonzero (its square is `1`). -/
theorem stringMatrix_ne_zero (n : ℕ) (f : Fin n → Pauli) :
    stringMatrix n f ≠ 0 := by
  intro h0
  have hsq := stringMatrix_sq n f
  rw [h0, Matrix.zero_mul] at hsq
  have h01 := congrArg
    (fun M : Matrix (idx n) (idx n) ℂ => M (idxDefault n) (idxDefault n)) hsq
  rw [Matrix.zero_apply, Matrix.one_apply_eq] at h01
  exact zero_ne_one h01

/-- Entrywise conjugation of a string is its conjugation phase times
itself. -/
theorem stringMatrix_conj :
    ∀ (n : ℕ) (f : Fin n → Pauli),
      (stringMatrix n f).map (starRingEnd ℂ)
        = conjPhaseF f • stringMatrix n f := by
  intro n
  induction n with
  | zero =>
    intro f
    rw [stringMatrix_zero]
    ext ⟨⟩ ⟨⟩
    simp [conjPhaseF, Matrix.map_apply, Matrix.one_apply]
  | succ m ih =>
    intro f
    show ((letterMatrix (f 0)) ⊗ₖ
          (stringMatrix m (fun i => f i.succ))).map (starRingEnd ℂ)
      = conjPhaseF f • ((letterMatrix (f 0)) ⊗ₖ
          (stringMatrix m (fun i => f i.succ)))
    have hmap : ((letterMatrix (f 0)) ⊗ₖ
          (stringMatrix m (fun i => f i.succ))).map (starRingEnd ℂ)
        = ((letterMatrix (f 0)).map (starRingEnd ℂ))
            ⊗ₖ ((stringMatrix m (fun i => f i.succ)).map (starRingEnd ℂ)) := by
      ext ⟨i1, i2⟩ ⟨j1, j2⟩
      simp [Matrix.map_apply, Matrix.kronecker_apply, map_mul]
    rw [hmap, ih, letterMatrix_conj, conjPhaseF_succ]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- A product of `±1` slot factors is `(-1)` to the count of the
negative slots. -/
theorem prod_if_neg_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → Bool) :
    ∏ i ∈ s, (if p i then (-1 : ℂ) else 1)
      = (-1) ^ (∑ i ∈ s, (if p i then 1 else 0)) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pow_add]
    by_cases hp : p a <;> simp [hp]

/-- Swapping the two strings multiplies the product phase by
`(-1)^(antiCount)`. -/
theorem phaseF_swap {n : ℕ} (f g : Fin n → Pauli) :
    phaseF g f = (-1 : ℂ) ^ (antiCountF f g) * phaseF f g := by
  have h1 : phaseF g f = ∏ i, ((if slotAnti (f i) (g i) then -1 else 1)
      * (slotMul (f i) (g i)).1) := by
    apply Finset.prod_congr rfl
    intro i _
    exact (slotMul_swap (f i) (g i)).2
  rw [h1, Finset.prod_mul_distrib, prod_if_neg_one]
  rfl

/-- Two strings whose anticommuting-slot count is odd anticommute. -/
theorem stringMatrix_anticommute_of_odd {n : ℕ} {f g : Fin n → Pauli}
    (hodd : Odd (antiCountF f g)) :
    stringMatrix n f * stringMatrix n g
      = - (stringMatrix n g * stringMatrix n f) := by
  have hzip : zipLetter g f = zipLetter f g := by
    funext i
    simp [zipLetter, (slotMul_swap (f i) (g i)).1]
  rw [stringMatrix_mul, stringMatrix_mul, hzip, phaseF_swap f g,
    Odd.neg_one_pow hodd, ← smul_smul, neg_one_smul, neg_neg]

end GppWhichWayForwardPauliStrings
