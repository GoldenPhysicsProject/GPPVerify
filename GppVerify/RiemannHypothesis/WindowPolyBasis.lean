import GppVerify.RiemannHypothesis.WindowEntries

/-!
# Polynomials from rational coefficient lists: moments and inner products on `[-ℓ, ℓ]`

For a polynomial given by a rational coefficient list `a` (ascending), `evalR a x = Σ a_i x^i`.
On a window `[-ℓ, ℓ]` with `ℓ` rational, its moments and inner products are rational numbers given
by computable functions (`momQ`, `ipQ`), so finite identities about them (orthogonality,
spanning, matrix entries) can be checked by `decide`:

* `intervalIntegral_pow_eq`: `∫_{-ℓ}^{ℓ} x^n = ipMono ℓ n` (`= 2ℓ^{n+1}/(n+1)` for even `n`, else `0`);
* `mom_evalR`: `∫ (evalR a) x^p = momQ ℓ a p`;
* `ip_evalR`: `⟨evalR a, evalR b⟩ = ipQ ℓ a b`;
* `evalR_eq_of_coeff`: a coefficientwise identity gives the pointwise one.

Unconditional; no `sorry`, no axioms.
-/

namespace GppWindowPolyBasis

open Set MeasureTheory intervalIntegral Finset GppWindowBilinear GppWindowEntries

/-- `∫_{-ℓ}^{ℓ} x^n dx` as a rational function of `ℓ`. -/
def ipMono (ℓ : ℚ) (n : ℕ) : ℚ := if n % 2 = 0 then 2 * ℓ ^ (n + 1) / ((n : ℚ) + 1) else 0

/-- Evaluate a rational coefficient list at a real point. -/
noncomputable def evalR (a : List ℚ) (x : ℝ) : ℝ := ∑ i ∈ range a.length, (a.getD i 0 : ℝ) * x ^ i

/-- `∫ (Σ a_i x^i) x^p` over `[-ℓ, ℓ]`. -/
def momQ (ℓ : ℚ) (a : List ℚ) (p : ℕ) : ℚ :=
  ((List.range a.length).map fun i => a.getD i 0 * ipMono ℓ (i + p)).sum

/-- `⟨Σ a_i x^i, Σ b_j x^j⟩` over `[-ℓ, ℓ]`. -/
def ipQ (ℓ : ℚ) (a b : List ℚ) : ℚ :=
  ((List.range b.length).map fun j => b.getD j 0 * momQ ℓ a j).sum

theorem sum_range_eq_list (n : ℕ) (f : ℕ → ℚ) :
    ∑ i ∈ range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem continuous_evalR (a : List ℚ) : Continuous (evalR a) := by
  unfold evalR; fun_prop

theorem intervalIntegral_pow_eq (ℓ : ℚ) (n : ℕ) :
    ∫ x in (-(ℓ : ℝ))..(ℓ : ℝ), x ^ n = ((ipMono ℓ n : ℚ) : ℝ) := by
  rw [integral_pow]
  unfold ipMono
  split_ifs with h
  · obtain ⟨k, hk⟩ := Nat.even_iff.mpr h
    have hodd : (-(ℓ : ℝ)) ^ (n + 1) = -(ℓ : ℝ) ^ (n + 1) := by
      rw [neg_pow, pow_succ (-1 : ℝ), hk, ← two_mul, pow_mul]; norm_num
    rw [hodd]; push_cast; ring
  · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
    have heven : (-(ℓ : ℝ)) ^ (n + 1) = (ℓ : ℝ) ^ (n + 1) := (hodd.add_one).neg_pow _
    rw [heven]; simp

theorem mom_evalR (ℓ : ℚ) (a : List ℚ) (p : ℕ) :
    mom (ℓ : ℝ) (evalR a) p = ((momQ ℓ a p : ℚ) : ℝ) := by
  unfold mom evalR momQ
  rw [← sum_range_eq_list, Rat.cast_sum]
  simp_rw [sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun i _ => ?_
    have : (fun x : ℝ => (a.getD i 0 : ℝ) * x ^ i * x ^ p) =
        fun x => (a.getD i 0 : ℝ) * x ^ (i + p) := by funext x; rw [pow_add]; ring
    rw [this, intervalIntegral.integral_const_mul, intervalIntegral_pow_eq, Rat.cast_mul]
  · intro i _
    exact (by fun_prop : Continuous fun x : ℝ =>
      (a.getD i 0 : ℝ) * x ^ i * x ^ p).intervalIntegrable _ _

theorem ip_evalR (ℓ : ℚ) (a b : List ℚ) :
    ip (ℓ : ℝ) (evalR a) (evalR b) = ((ipQ ℓ a b : ℚ) : ℝ) := by
  unfold ipQ
  rw [← sum_range_eq_list, Rat.cast_sum]
  have h : ip (ℓ : ℝ) (evalR a) (evalR b) =
      ∑ j ∈ range b.length, (b.getD j 0 : ℝ) * mom (ℓ : ℝ) (evalR a) j := by
    unfold ip mom
    conv_lhs => enter [1, x]; rw [show evalR b x = ∑ j ∈ range b.length, (b.getD j 0 : ℝ) * x ^ j
      from rfl, mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun j _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext x; ring
    · intro j _
      exact ((continuous_evalR a).mul (by fun_prop : Continuous fun x : ℝ =>
        (b.getD j 0 : ℝ) * x ^ j)).intervalIntegrable _ _
  rw [h]
  refine sum_congr rfl fun j _ => ?_
  rw [mom_evalR, Rat.cast_mul]

/-- **Coefficientwise identities give pointwise ones.** If `c_i = Σ_j α_j (b_j)_i` for every `i < K`,
all lists have length `≤ K`, then `evalR c x = Σ_j α_j evalR (b_j) x`. -/
theorem evalR_eq_of_coeff {n K : ℕ} (c : List ℚ) (b : Fin n → List ℚ) (α : Fin n → ℚ)
    (hc : c.length ≤ K) (hb : ∀ j, (b j).length ≤ K)
    (hcoef : ∀ i < K, c.getD i 0 = ∑ j, α j * (b j).getD i 0) (x : ℝ) :
    evalR c x = ∑ j, (α j : ℝ) * evalR (b j) x := by
  have ext : ∀ (a : List ℚ), a.length ≤ K →
      evalR a x = ∑ i ∈ range K, (a.getD i 0 : ℝ) * x ^ i := by
    intro a ha
    unfold evalR
    refine (sum_subset (range_subset_range.mpr ha) fun i hi hni => ?_)
    have : a.length ≤ i := by simpa using hni
    have h0 : a.getD i 0 = 0 := List.getD_eq_default _ _ this
    rw [h0]; simp
  rw [ext c hc]
  simp_rw [ext _ (hb _), mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [hcoef i (mem_range.mp hi), Rat.cast_sum, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  push_cast; ring

end GppWindowPolyBasis

#print axioms GppWindowPolyBasis.ip_evalR
#print axioms GppWindowPolyBasis.evalR_eq_of_coeff
