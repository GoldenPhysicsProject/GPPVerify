import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Ring.GeomSum

/-!
# The alternating harmonic series: `Σ (−1)ᵏ/(k+1) = log 2`

Thread C1 of `docs/FORMALIZATION_PLAN.md`: `η(1) = log 2` in its classical series form —
absent from the pinned Mathlib, whose logarithm power series
(`hasSum_pow_div_log_of_abs_lt_one`) stops strictly inside `|x| < 1` and whose alternating
series *test* gives convergence but not the value.

The proof is the elementary integral-remainder argument, requiring no boundary Abel
theorem: from the finite geometric sum

  `Σ_{k<n} (−1)ᵏ xᵏ = (1 − (−x)ⁿ)/(1+x)`,

integrating over `[0,1]` gives

  `log 2 − Σ_{k<n} (−1)ᵏ/(k+1) = ∫₀¹ (−x)ⁿ/(1+x) dx`,

and the remainder integral is sandwiched by `±∫₀¹ xⁿ dx = ±1/(n+1) → 0`.

Together with `SechSquaredIntegral.lean` (which produced the same constant as
`∫₀^∞ u/cosh²u du`), the value `η(1) = log 2` now exists in the repo in both its Mellin
and its series incarnations — the two forms used by Yakaboylu's biorthogonality relation
(eq. 50) and by Definition 2.1's `η(1) = log 2` remark.
-/

namespace GppAlternatingHarmonic

open Filter intervalIntegral

/-- `∫₀¹ dx/(1+x) = log 2`. -/
theorem integral_one_div_one_add : ∫ x in (0:ℝ)..1, 1 / (1 + x) = Real.log 2 := by
  have hcongr : ∫ x in (0:ℝ)..1, 1 / (1 + x) = ∫ x in (0:ℝ)..1, 1 / (x + 1) := by
    apply intervalIntegral.integral_congr
    intro x _
    show 1 / (1 + x) = 1 / (x + 1)
    rw [add_comm 1 x]
  have hshift : (∫ x in (0:ℝ)..1, 1 / (x + 1)) = ∫ x in (1:ℝ)..2, 1 / x := by
    have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 1)
      (f := fun u : ℝ => 1 / u) 1
    rw [show (0:ℝ) + 1 = 1 by norm_num, show (1:ℝ) + 1 = 2 by norm_num] at h
    exact h
  have h02 : (0:ℝ) ∉ Set.uIcc (1:ℝ) 2 := by
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
    simp only [Set.mem_Icc, not_and_or]
    left
    norm_num
  rw [hcongr, hshift, integral_one_div h02, show (2:ℝ) / 1 = 2 by norm_num]

/-- The finite geometric sum with ratio `−x`: `Σ_{k<n} (−1)ᵏxᵏ = (1 − (−x)ⁿ)/(1+x)`. -/
theorem sum_neg_pow_eq (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ Finset.range n, (-1:ℝ)^k * x^k = (1 - (-x)^n) / (1 + x) := by
  have hne : (-x : ℝ) ≠ 1 := by
    intro h
    linarith [h ▸ (by linarith : (-x : ℝ) ≤ 0)]
  have h1x : (0:ℝ) < 1 + x := by linarith
  have h := geom_sum_eq hne n
  have hterm : ∀ k ∈ Finset.range n, (-x:ℝ)^k = (-1:ℝ)^k * x^k := by
    intro k _
    rw [neg_pow]
  rw [Finset.sum_congr rfl hterm] at h
  rw [h, show (-x:ℝ) - 1 = -(1 + x) by ring, div_neg, ← neg_div, neg_sub]

/-- **The integral form of the partial-sum defect**:
    `log 2 − Σ_{k<n} (−1)ᵏ/(k+1) = ∫₀¹ (−x)ⁿ/(1+x) dx`. -/
theorem log_two_sub_partial (n : ℕ) :
    Real.log 2 - ∑ k ∈ Finset.range n, (-1:ℝ)^k / (k+1) =
      ∫ x in (0:ℝ)..1, (-x)^n / (1 + x) := by
  have hint1 : IntervalIntegrable (fun x : ℝ => 1 / (1 + x)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    simp only [Pi.add_apply, id_eq]
    exact ne_of_gt (by linarith)
  have hint2 : IntervalIntegrable
      (fun x : ℝ => ∑ k ∈ Finset.range n, (-1:ℝ)^k * x^k) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_pow k)
  have hsum_int : ∫ x in (0:ℝ)..1, (∑ k ∈ Finset.range n, (-1:ℝ)^k * x^k) =
      ∑ k ∈ Finset.range n, (-1:ℝ)^k / (k+1) := by
    -- pin `f` explicitly: otherwise the integrability argument forces `f k` to
    -- elaborate as the point-free `(fun _ => c) * (fun a => a ^ k)`, which no longer
    -- matches the lambda in the goal.
    rw [intervalIntegral.integral_finsetSum (f := fun k (x : ℝ) => (-1 : ℝ) ^ k * x ^ k)
      (fun k _ => (continuous_const.mul (continuous_pow k)).intervalIntegrable 0 1)]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow, one_pow,
      zero_pow (by omega : k + 1 ≠ 0), sub_zero]
    ring
  have hpt : Set.EqOn (fun x : ℝ => 1 / (1 + x) - ∑ k ∈ Finset.range n, (-1:ℝ)^k * x^k)
      (fun x : ℝ => (-x)^n / (1 + x)) (Set.uIcc (0:ℝ) 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    have h1x : (0:ℝ) < 1 + x := by linarith
    show 1 / (1 + x) - ∑ k ∈ Finset.range n, (-1:ℝ)^k * x^k = (-x)^n / (1 + x)
    rw [sum_neg_pow_eq n hx0]
    field_simp
    -- Mathlib 4.33: `field_simp` stops one `ring` step short here.
    ring
  calc Real.log 2 - ∑ k ∈ Finset.range n, (-1:ℝ)^k / (k+1)
      = (∫ x in (0:ℝ)..1, 1 / (1 + x)) -
          ∫ x in (0:ℝ)..1, (∑ k ∈ Finset.range n, (-1:ℝ)^k * x^k) := by
        rw [integral_one_div_one_add, hsum_int]
    _ = ∫ x in (0:ℝ)..1,
          (1 / (1 + x) - ∑ k ∈ Finset.range n, (-1:ℝ)^k * x^k) :=
        (intervalIntegral.integral_sub hint1 hint2).symm
    _ = ∫ x in (0:ℝ)..1, (-x)^n / (1 + x) := intervalIntegral.integral_congr hpt

/-- The pointwise remainder bound on `[0,1]`: `|(−x)ⁿ/(1+x)| ≤ xⁿ`. -/
theorem remainder_pointwise {n : ℕ} {x : ℝ} (hx0 : 0 ≤ x) :
    |(-x)^n / (1 + x)| ≤ x^n := by
  have h1x : (0:ℝ) < 1 + x := by linarith
  rw [abs_div, abs_pow, abs_neg, abs_of_nonneg hx0, abs_of_pos h1x]
  calc x^n / (1 + x) ≤ x^n := div_le_self (pow_nonneg hx0 n) (by linarith)

/-- **The remainder bound**: `|∫₀¹ (−x)ⁿ/(1+x) dx| ≤ 1/(n+1)`. -/
theorem remainder_bound (n : ℕ) :
    |∫ x in (0:ℝ)..1, (-x)^n / (1 + x)| ≤ 1 / ((n:ℝ) + 1) := by
  have hintR : IntervalIntegrable (fun x : ℝ => (-x)^n / (1 + x))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (continuousOn_id.neg.pow n)
      (continuousOn_const.add continuousOn_id)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    simp only [Pi.add_apply, id_eq]
    exact ne_of_gt (by linarith)
  have hintP : IntervalIntegrable (fun x : ℝ => x^n) MeasureTheory.volume 0 1 :=
    (continuous_pow n).intervalIntegrable 0 1
  have hval : ∫ x in (0:ℝ)..1, x^n = 1 / ((n:ℝ) + 1) := by
    rw [integral_pow, one_pow, zero_pow (by omega : n + 1 ≠ 0), sub_zero]
  have hub : ∫ x in (0:ℝ)..1, (-x)^n / (1 + x) ≤ 1 / ((n:ℝ) + 1) := by
    rw [← hval]
    apply intervalIntegral.integral_mono_on (by norm_num) hintR hintP
    intro x hx
    exact (abs_le.mp (remainder_pointwise hx.1)).2
  have hlb : -(1 / ((n:ℝ) + 1)) ≤ ∫ x in (0:ℝ)..1, (-x)^n / (1 + x) := by
    rw [← hval, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on (by norm_num) hintP.neg hintR
    intro x hx
    exact (abs_le.mp (remainder_pointwise hx.1)).1
  exact abs_le.mpr ⟨hlb, hub⟩

/-- **The alternating harmonic series converges to `log 2`** — `η(1) = log 2` in series
    form: `Σ_{k<n} (−1)ᵏ/(k+1) → log 2`. -/
theorem tendsto_alternating_harmonic_log_two :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (-1:ℝ)^k / (k+1)) atTop
      (nhds (Real.log 2)) := by
  have hone : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hR : Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..1, (-x)^n / (1 + x)) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun n : ℕ => -(1 / ((n:ℝ) + 1))) (h := fun n : ℕ => 1 / ((n:ℝ) + 1))
    · simpa only [neg_zero] using hone.neg
    · exact hone
    · exact fun n => (abs_le.mp (remainder_bound n)).1
    · exact fun n => (abs_le.mp (remainder_bound n)).2
  have hid : ∀ n : ℕ, ∑ k ∈ Finset.range n, (-1:ℝ)^k / (k+1) =
      Real.log 2 - ∫ x in (0:ℝ)..1, (-x)^n / (1 + x) := by
    intro n
    have h := log_two_sub_partial n
    linarith
  rw [tendsto_congr hid]
  have h := (tendsto_const_nhds (x := Real.log 2) (f := (atTop : Filter ℕ))).sub hR
  simpa only [sub_zero] using h

end GppAlternatingHarmonic
