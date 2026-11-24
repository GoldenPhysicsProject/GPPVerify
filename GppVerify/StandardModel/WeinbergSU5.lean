import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

/-!
# sin²θ_W = 3/8 from the SU(5) embedding (retires `open_weinberg_angle_full_derivation`)

The Georgi–Glashow derivation, as finite algebra:

1. **Embedding.** On the fundamental `5` of SU(5), the Standard-Model Cartan generators are the
   diagonal matrices `T₃ = diag(0,0,0,½,−½)` and `Y = diag(−⅓,−⅓,−⅓,½,½)`, and `Q = T₃ + Y =
   diag(−⅓,−⅓,−⅓,1,0)`. Both are traceless (they lie in `su(5)`), and they are trace-orthogonal,
   `Tr(T₃ Y) = 0` (`trace_T3`, `trace_Y`, `trace_T3_Y`).
2. **Normalization.** A simple group has one coupling, so every generator must be normalized
   alike: `Tr(T₁²) = Tr(T₃²)` with `T₁ = c·Y`. On the `5`, `Tr(Y²)/Tr(T₃²) = 5/3`
   (`hypercharge_normalization`), i.e. `c² = 3/5`, and the hypercharge coupling is
   `g'² = (3/5) g²` at unification.
3. **Angle.** `sin²θ_W = g'²/(g² + g'²)`. With `g'² = g²·Tr(T₃²)/Tr(Y²)` and `Tr(T₃Y) = 0`,
   this equals `Tr(T₃²)/Tr(Q²)` (`sin_sq_eq_trace_ratio`, an identity for any trace-orthogonal
   pair), and on the `5` that is `(1/2)/(4/3) = 3/8` (`weinberg_su5`).
4. **Representation independence check.** On the `10 = Λ²5` (weights `X_i + X_j`, `i < j`) the
   same ratios come out: `Tr₁₀(T₃²)/Tr₁₀(Q²) = 3/8` and `Tr₁₀(Y²)/Tr₁₀(T₃²) = 5/3`
   (`weinberg_su5_ten`, `hypercharge_normalization_ten`), as they must, since the Killing form
   on `su(5)` is unique up to scale.

This is the tree-level, unification-scale value. Running to `M_Z` (≈ 0.231) is not here.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppWeinbergSU5

open Finset

/-- Weights of `T₃` on the `5`. -/
def T3 : Fin 5 → ℚ := ![0, 0, 0, 1/2, -1/2]

/-- Weights of `Y` on the `5`. -/
def Y : Fin 5 → ℚ := ![-1/3, -1/3, -1/3, 1/2, 1/2]

/-- Electric charge `Q = T₃ + Y` on the `5`. -/
def Q : Fin 5 → ℚ := fun i => T3 i + Y i

theorem Q_eq : Q = ![-1/3, -1/3, -1/3, 1, 0] := by
  funext i; fin_cases i <;> simp [Q, T3, Y] <;> norm_num

theorem trace_T3 : ∑ i, T3 i = 0 := by simp [T3, Fin.sum_univ_five]; norm_num
theorem trace_Y : ∑ i, Y i = 0 := by simp [Y, Fin.sum_univ_five]; norm_num
theorem trace_T3_Y : ∑ i, T3 i * Y i = 0 := by simp [T3, Y, Fin.sum_univ_five]; norm_num

theorem trace_T3_sq : ∑ i, T3 i ^ 2 = 1/2 := by simp [T3, Fin.sum_univ_five]; norm_num
theorem trace_Y_sq : ∑ i, Y i ^ 2 = 5/6 := by simp [Y, Fin.sum_univ_five]; norm_num
theorem trace_Q_sq : ∑ i, Q i ^ 2 = 4/3 := by simp [Q_eq, Fin.sum_univ_five]; norm_num

/-- `Tr(Y²)/Tr(T₃²) = 5/3`: the GUT normalization of hypercharge, `T₁ = √(3/5)·Y`. -/
theorem hypercharge_normalization : (∑ i, Y i ^ 2) / (∑ i, T3 i ^ 2) = 5/3 := by
  rw [trace_Y_sq, trace_T3_sq]; norm_num

/-- For trace-orthogonal `A`, `B`, with `g'² = g²·Tr(A²)/Tr(B²)`, the mixing angle
`g'²/(g² + g'²)` is `Tr(A²)/Tr((A+B)²)`. -/
theorem sin_sq_eq_trace_ratio {ι : Type*} [Fintype ι] (A B : ι → ℚ)
    (horth : ∑ i, A i * B i = 0) (hA : 0 < ∑ i, A i ^ 2) (hB : 0 < ∑ i, B i ^ 2)
    (g g' : ℚ) (hg : g ≠ 0) (hcoup : g' ^ 2 = g ^ 2 * (∑ i, A i ^ 2) / (∑ i, B i ^ 2)) :
    g' ^ 2 / (g ^ 2 + g' ^ 2) = (∑ i, A i ^ 2) / (∑ i, (A i + B i) ^ 2) := by
  have hsq : ∑ i, (A i + B i) ^ 2 = ∑ i, A i ^ 2 + ∑ i, B i ^ 2 := by
    have : ∀ i, (A i + B i) ^ 2 = A i ^ 2 + B i ^ 2 + 2 * (A i * B i) := fun i => by ring
    simp_rw [this, sum_add_distrib, ← mul_sum, horth]; ring
  rw [hsq, hcoup]
  have hg2 : 0 < g ^ 2 := by positivity
  field_simp
  ring

/-- **sin²θ_W = 3/8 at the SU(5) unification scale.** With one gauge coupling `g` and the
hypercharge coupling fixed by the normalization, `g'² = g²·Tr(T₃²)/Tr(Y²)`. -/
theorem weinberg_su5 (g g' : ℚ) (hg : g ≠ 0)
    (hcoup : g' ^ 2 = g ^ 2 * (∑ i, T3 i ^ 2) / (∑ i, Y i ^ 2)) :
    g' ^ 2 / (g ^ 2 + g' ^ 2) = 3/8 := by
  rw [sin_sq_eq_trace_ratio T3 Y trace_T3_Y (by rw [trace_T3_sq]; norm_num)
    (by rw [trace_Y_sq]; norm_num) g g' hg hcoup]
  have : ∀ i, T3 i + Y i = Q i := fun _ => rfl
  simp_rw [this, trace_Q_sq, trace_T3_sq]
  norm_num

/-! ### The `10 = Λ²5` -/

/-- Weight of a generator with weights `X` on `e_i ∧ e_j`. -/
def wedgeWeight (X : Fin 5 → ℚ) (p : Fin 5 × Fin 5) : ℚ := X p.1 + X p.2

/-- The ten basis pairs `i < j` of `Λ²5`. -/
def tenPairs : Finset (Fin 5 × Fin 5) := univ.filter fun p => p.1 < p.2

theorem card_tenPairs : tenPairs.card = 10 := by decide

theorem trace_ten_T3_sq : ∑ p ∈ tenPairs, wedgeWeight T3 p ^ 2 = 3/2 := by
  rw [tenPairs, Finset.sum_filter, Fintype.sum_prod_type]
  simp [wedgeWeight, T3, Fin.sum_univ_five]
  norm_num

theorem trace_ten_Y_sq : ∑ p ∈ tenPairs, wedgeWeight Y p ^ 2 = 5/2 := by
  rw [tenPairs, Finset.sum_filter, Fintype.sum_prod_type]
  simp [wedgeWeight, Y, Fin.sum_univ_five]
  norm_num

theorem trace_ten_Q_sq : ∑ p ∈ tenPairs, wedgeWeight Q p ^ 2 = 4 := by
  rw [tenPairs, Finset.sum_filter, Fintype.sum_prod_type]
  simp [wedgeWeight, Q_eq, Fin.sum_univ_five]
  norm_num

theorem weinberg_su5_ten :
    (∑ p ∈ tenPairs, wedgeWeight T3 p ^ 2) / (∑ p ∈ tenPairs, wedgeWeight Q p ^ 2) = 3/8 := by
  rw [trace_ten_T3_sq, trace_ten_Q_sq]; norm_num

theorem hypercharge_normalization_ten :
    (∑ p ∈ tenPairs, wedgeWeight Y p ^ 2) / (∑ p ∈ tenPairs, wedgeWeight T3 p ^ 2) = 5/3 := by
  rw [trace_ten_Y_sq, trace_ten_T3_sq]; norm_num

end GppWeinbergSU5

#print axioms GppWeinbergSU5.weinberg_su5
