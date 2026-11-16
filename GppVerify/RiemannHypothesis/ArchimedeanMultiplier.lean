import GppVerify.RiemannHypothesis.EdgeOverlap

/-!
# The archimedean energy multiplier `a(ξ)` and its kernel-checked rational lower bounds

For the Fourier-side form of the translation Dirichlet energy
`ℰ(f) = ∫ a(ξ) |f̂(ξ)|² dξ`, the multiplier is the positive series

`a(ξ) = 2 Σ_{k ≥ 0} ξ² / ((2k + ½)((2k + ½)² + ξ²))`   (`= Re ψ(¼ + iξ/2) − ψ(¼)`),

which is nonnegative, termwise nondecreasing in `|ξ|`, and summable (`aMult`). This file proves those
elementary facts and the two **kernel-checked rational lower bounds** of the first-prime-window index
estimate (Turbo relay `7399083`, formalisation order step (3)):

* `a(47/4) > 1199/200` from the first 100 terms (five-moment case, `R = 47/4`);
* `a(25/2) > 121/20` from the first 100 terms (six-moment case, `R = 25/2`);

and the exact margin arithmetic `(1199/200)(1 − 9/500) − 147/25 = 709/100000` and
`(121/20)(1 − 1/80) − 59/10 = 119/1600`.

**Scope.** Only the series and its rational partial sums. The Plancherel identity `ℰ(f) = ∫ a |f̂|²`, the
Legendre band-leakage bounds, the transcendental bound on `M₋` (needs `γ`, `log π`, `π`, `log 2` rational
bounds, `π < 3.1416` from `Real.pi_lt_d6`) and the resulting positivity statement are **not** here.

No `sorry`, no axiom.
-/

open Finset

noncomputable section

namespace GppFirstPrime

/-- `k`-th term of the multiplier series. -/
def aTerm (ξ : ℝ) (k : ℕ) : ℝ := ξ ^ 2 / ((2 * k + 1 / 2) * ((2 * k + 1 / 2) ^ 2 + ξ ^ 2))

theorem aTerm_nonneg (ξ : ℝ) (k : ℕ) : 0 ≤ aTerm ξ k := by
  unfold aTerm; positivity

/-- Termwise monotone in `|ξ|`. -/
theorem aTerm_mono {ξ η : ℝ} (h : |ξ| ≤ |η|) (k : ℕ) : aTerm ξ k ≤ aTerm η k := by
  have h2 : ξ ^ 2 ≤ η ^ 2 := by
    have := sq_le_sq.mpr h; simpa using this
  unfold aTerm
  have hc : (0 : ℝ) < 2 * k + 1 / 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_pos hc (mul_pos hc hc)
  nlinarith [mul_nonneg (sq_nonneg ξ) (sq_nonneg η), sq_nonneg ξ, sq_nonneg η, sub_nonneg.mpr h2]

theorem aTerm_le (ξ : ℝ) (k : ℕ) : aTerm ξ k ≤ 8 * ξ ^ 2 / ((k + 1 : ℝ) ^ 3) := by
  unfold aTerm
  have hc : (0 : ℝ) < 2 * k + 1 / 2 := by positivity
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hlow : ((k : ℝ) + 1) / 2 ≤ 2 * k + 1 / 2 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hcube : (((k : ℝ) + 1) / 2) ^ 3 ≤ (2 * k + 1 / 2) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hlow 3
  calc ξ ^ 2 / ((2 * k + 1 / 2) * ((2 * k + 1 / 2) ^ 2 + ξ ^ 2))
      ≤ ξ ^ 2 / ((2 * k + 1 / 2) ^ 3) := by
        apply div_le_div_of_nonneg_left (sq_nonneg ξ) (by positivity)
        nlinarith [sq_nonneg ξ, hc]
    _ ≤ ξ ^ 2 / ((((k : ℝ) + 1) / 2) ^ 3) :=
        div_le_div_of_nonneg_left (sq_nonneg ξ) (by positivity) hcube
    _ = 8 * ξ ^ 2 / ((k + 1 : ℝ) ^ 3) := by field_simp; ring

theorem summable_aTerm (ξ : ℝ) : Summable (aTerm ξ) := by
  have hs : Summable fun k : ℕ => 8 * ξ ^ 2 / ((k + 1 : ℝ) ^ 3) := by
    have h3 : Summable fun k : ℕ => 1 / ((k : ℝ) ^ 3) := Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h4 : Summable fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 3) :=
      (summable_nat_add_iff 1).mpr h3
    have := h4.mul_left (8 * ξ ^ 2)
    refine this.congr fun k => ?_
    push_cast; ring
  exact Summable.of_nonneg_of_le (aTerm_nonneg ξ) (aTerm_le ξ) hs

/-- **The archimedean energy multiplier** `a(ξ) = 2 Σ_k ξ²/((2k+½)((2k+½)²+ξ²))`. -/
def aMult (ξ : ℝ) : ℝ := 2 * ∑' k, aTerm ξ k

theorem aMult_nonneg (ξ : ℝ) : 0 ≤ aMult ξ :=
  mul_nonneg (by norm_num) (tsum_nonneg (aTerm_nonneg ξ))

/-- **`a` is nondecreasing in `|ξ|`.** -/
theorem aMult_mono {ξ η : ℝ} (h : |ξ| ≤ |η|) : aMult ξ ≤ aMult η := by
  unfold aMult
  have := (summable_aTerm ξ).tsum_le_tsum (fun k => aTerm_mono h k) (summable_aTerm η)
  linarith

/-- Partial sums bound `a` from below. -/
theorem aMult_ge_partial (ξ : ℝ) (n : ℕ) : 2 * ∑ k ∈ range n, aTerm ξ k ≤ aMult ξ := by
  unfold aMult
  have := (summable_aTerm ξ).sum_le_tsum (range n) (fun k _ => aTerm_nonneg ξ k)
  linarith

/-! ### Rational certificates -/

/-- The rational version of the term. -/
def aTermQ (ξ : ℚ) (k : ℕ) : ℚ := ξ ^ 2 / ((2 * k + 1 / 2) * ((2 * k + 1 / 2) ^ 2 + ξ ^ 2))

theorem aTermQ_cast (ξ : ℚ) (k : ℕ) : ((aTermQ ξ k : ℚ) : ℝ) = aTerm (ξ : ℝ) k := by
  unfold aTermQ aTerm; push_cast; rfl

theorem partial_cast (ξ : ℚ) (n : ℕ) :
    ((2 * ∑ k ∈ range n, aTermQ ξ k : ℚ) : ℝ) = 2 * ∑ k ∈ range n, aTerm (ξ : ℝ) k := by
  push_cast
  simp [aTermQ_cast]

/-- **Kernel-checked:** the first 100 terms at `ξ = 47/4` exceed `1199/200`. -/
theorem partial_47_4 : (1199 / 200 : ℚ) < 2 * ∑ k ∈ range 100, aTermQ (47 / 4) k := by
  decide +kernel

/-- **Kernel-checked:** the first 100 terms at `ξ = 25/2` exceed `121/20`. -/
theorem partial_25_2 : (121 / 20 : ℚ) < 2 * ∑ k ∈ range 100, aTermQ (25 / 2) k := by
  decide +kernel

/-- **Five-moment multiplier bound:** `a(47/4) > 1199/200`. -/
theorem aMult_47_4_gt : (1199 / 200 : ℝ) < aMult (47 / 4) := by
  have h := partial_cast (47 / 4) 100
  have hq : ((1199 / 200 : ℚ) : ℝ) < ((2 * ∑ k ∈ range 100, aTermQ (47 / 4) k : ℚ) : ℝ) :=
    Rat.cast_lt.mpr partial_47_4
  rw [h] at hq
  have := aMult_ge_partial ((47 / 4 : ℚ) : ℝ) 100
  push_cast at hq this
  linarith

/-- **Six-moment multiplier bound:** `a(25/2) > 121/20`. -/
theorem aMult_25_2_gt : (121 / 20 : ℝ) < aMult (25 / 2) := by
  have h := partial_cast (25 / 2) 100
  have hq : ((121 / 20 : ℚ) : ℝ) < ((2 * ∑ k ∈ range 100, aTermQ (25 / 2) k : ℚ) : ℝ) :=
    Rat.cast_lt.mpr partial_25_2
  rw [h] at hq
  have := aMult_ge_partial ((25 / 2 : ℚ) : ℝ) 100
  push_cast at hq this
  linarith

/-- Five-moment margin arithmetic: `(1199/200)(1 − 9/500) − 147/25 = 709/100000`. -/
theorem margin_five : (1199 / 200 : ℚ) * (1 - 9 / 500) - 147 / 25 = 709 / 100000 := by norm_num

/-- Six-moment margin arithmetic: `(121/20)(1 − 1/80) − 59/10 = 119/1600`. -/
theorem margin_six : (121 / 20 : ℚ) * (1 - 1 / 80) - 59 / 10 = 119 / 1600 := by norm_num

end GppFirstPrime

#print axioms GppFirstPrime.aMult_47_4_gt
#print axioms GppFirstPrime.aMult_25_2_gt
#print axioms GppFirstPrime.aMult_mono
