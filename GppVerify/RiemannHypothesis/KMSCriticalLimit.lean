import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The finite-place KMS midpoint field has a tame critical limit

Source: Codex, GPPDiscovery2 `discovery/rh/RH_KMS_CRITICAL_LIMIT_2026-09-24.md`
(formalized here 2026-09-27).

At inverse temperature `β` the Bost–Connes midpoint normalization gives the prime-power field
`c_β(n) = Λ(n) n^{-β/2}`. The critical KMS dual metric on the ladder of `p` has
`d₁(p^k) = (1 - p^{-k}) / (k log p)`, which depends on `n = p^k` only, as
`d₁(n) = (1 - 1/n) / log n`. With cutoff `n ≤ N` the dual norm is
`‖a‖²_{*,N} = Σ_{prime powers n ≤ N} a(n)² / d₁(n)`.

The note's claim is `‖c₁ - c_β‖_{*,N} = O(|β - 1| (log N)³)` with no zero information and no
prime number theorem. Formalized here:

* `midpoint_diff_bounds`: `0 ≤ c₁(n) - c_β(n) ≤ ((β-1)/2) log n · c₁(n)` for `β ≥ 1`
  (from `1 - e^{-x} ≤ x`);
* `kms_term_bound`: each prime-power term is at most `((β-1)²/2) (log n)⁵ / n`;
* `kms_critical_limit`: `‖c₁ - c_β‖²_{*,N} ≤ ((β-1)²/2) (log N)⁵ (1 + log N)`;
* `kms_critical_limit_clean`: for `N ≥ 3`, `‖c₁ - c_β‖²_{*,N} ≤ (β-1)² (log N)⁶`, i.e.
  `‖c₁ - c_β‖_{*,N} ≤ |β-1| (log N)³`.

The note bounds `Σ (log n)⁵/n` by the integral test (`C + L⁶/6`); here the cruder
`(log N)⁵ · H_N ≤ (log N)⁵ (1 + log N)` is used, which gives the same `L³` rate with an explicit
constant.

## Scope

This is the finite-place estimate only. As the note itself says, it does not control the
scalar pullback of the KMS field to the Weil form (which is not bounded on the raw KMS Hilbert
space), nor the real-place and pole channels, and it is not a step that proves RH.
-/

open Real Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GppKMSCriticalLimit

/-- The Bost–Connes midpoint field `c_β(n) = Λ(n) n^{-β/2}`. -/
noncomputable def midpoint (β : ℝ) (n : ℕ) : ℝ := Λ n * (n : ℝ) ^ (-β / 2)

/-- The critical KMS dual weight `d₁(n) = (1 - 1/n) / log n`. -/
noncomputable def kmsDual (n : ℕ) : ℝ := (1 - (n : ℝ)⁻¹) / Real.log n

/-- `d₁` on a prime power is the note's `(1 - p^{-k}) / (k log p)`. -/
lemma kmsDual_primePow (p k : ℕ) :
    kmsDual (p ^ k) = (1 - ((p : ℝ) ^ k)⁻¹) / (k * Real.log p) := by
  simp [kmsDual, Real.log_pow]

/-- The critical KMS dual norm squared, with cutoff `n ≤ N`. -/
noncomputable def kmsNormSq (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, if IsPrimePow n then a n ^ 2 / kmsDual n else 0

lemma midpoint_diff_bounds (β : ℝ) (hβ : 1 ≤ β) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ midpoint 1 n - midpoint β n ∧
      midpoint 1 n - midpoint β n ≤ (β - 1) / 2 * Real.log n * midpoint 1 n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set x := (β - 1) / 2 * Real.log n with hx
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) hlog
  have hsplit : (n : ℝ) ^ (-β / 2) = (n : ℝ) ^ (-1 / 2 : ℝ) * Real.exp (-x) := by
    rw [show -β / 2 = (-1 / 2 : ℝ) + (-(β - 1) / 2) by ring, Real.rpow_add hnpos,
      Real.rpow_def_of_pos hnpos (-(β - 1) / 2), hx]
    congr 2
    ring
  have hdiff : midpoint 1 n - midpoint β n = midpoint 1 n * (1 - Real.exp (-x)) := by
    simp only [midpoint, hsplit]
    ring
  have hc1 : 0 ≤ midpoint 1 n :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnpos.le _)
  have he1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hex : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  refine ⟨?_, ?_⟩
  · rw [hdiff]; exact mul_nonneg hc1 (by linarith)
  · rw [hdiff]
    calc midpoint 1 n * (1 - Real.exp (-x)) ≤ midpoint 1 n * x :=
          mul_le_mul_of_nonneg_left hex hc1
      _ = x * midpoint 1 n := by ring

lemma kms_term_bound (β : ℝ) (hβ : 1 ≤ β) (n : ℕ) (hn : 2 ≤ n) :
    (midpoint 1 n - midpoint β n) ^ 2 / kmsDual n ≤
      (β - 1) ^ 2 / 2 * (Real.log n ^ 5 / n) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  obtain ⟨h0, h1⟩ := midpoint_diff_bounds β hβ n hn1
  -- `c₁(n)² = Λ(n)² / n`
  have hc1sq : midpoint 1 n ^ 2 = Λ n ^ 2 / n := by
    have hs : ((n : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = (n : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
      exact Real.rpow_neg_one _
    simp only [midpoint]
    rw [mul_pow, hs, div_eq_mul_inv]
  have hΛ : Λ n ^ 2 ≤ Real.log n ^ 2 :=
    pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_le_log 2
  have hdual : kmsDual n = (n - 1) / (n * Real.log n) := by
    unfold kmsDual
    field_simp
  have hdpos : 0 < kmsDual n := by
    rw [hdual]; exact div_pos (by linarith) (by positivity)
  set δ := β - 1
  have hsq : (midpoint 1 n - midpoint β n) ^ 2 ≤
      (δ / 2 * Real.log n) ^ 2 * (Real.log n ^ 2 / n) := by
    calc (midpoint 1 n - midpoint β n) ^ 2
        ≤ (δ / 2 * Real.log n * midpoint 1 n) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (δ / 2 * Real.log n) ^ 2 * midpoint 1 n ^ 2 := by ring
      _ ≤ (δ / 2 * Real.log n) ^ 2 * (Real.log n ^ 2 / n) := by
          rw [hc1sq]
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hΛ hnpos.le) (sq_nonneg _)
  rw [div_le_iff₀ hdpos]
  refine hsq.trans ?_
  rw [hdual]
  have eL : (δ / 2 * Real.log n) ^ 2 * (Real.log n ^ 2 / n) =
      δ ^ 2 * Real.log n ^ 4 * (1 / (4 * n)) := by
    field_simp; ring
  have eR : δ ^ 2 / 2 * (Real.log n ^ 5 / n) * ((n - 1) / (n * Real.log n)) =
      δ ^ 2 * Real.log n ^ 4 * ((n - 1) / (2 * n ^ 2)) := by
    field_simp
  rw [eL, eR]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Critical-limit estimate.**
`‖c₁ - c_β‖²_{*,N} ≤ ((β-1)²/2) (log N)⁵ (1 + log N)` for every `β ≥ 1` and cutoff `N`. -/
theorem kms_critical_limit (β : ℝ) (hβ : 1 ≤ β) (N : ℕ) :
    kmsNormSq (fun n => midpoint 1 n - midpoint β n) N ≤
      (β - 1) ^ 2 / 2 * (Real.log N ^ 5 * (1 + Real.log N)) := by
  have hterm : ∀ n ∈ Icc 1 N,
      (if IsPrimePow n then (midpoint 1 n - midpoint β n) ^ 2 / kmsDual n else 0) ≤
        (β - 1) ^ 2 / 2 * (Real.log N ^ 5 * (n : ℝ)⁻¹) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hlogle : Real.log n ≤ Real.log N :=
      Real.log_le_log hnpos (by exact_mod_cast hnN)
    have hmono : Real.log n ^ 5 / n ≤ Real.log N ^ 5 * (n : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlogn hlogle 5)
        (inv_nonneg.mpr hnpos.le)
    split_ifs with hpp
    · exact (kms_term_bound β hβ n hpp.two_le).trans
        (mul_le_mul_of_nonneg_left hmono (by positivity))
    · exact mul_nonneg (by positivity)
        (mul_nonneg (pow_nonneg (hlogn.trans hlogle) 5) (inv_nonneg.mpr hnpos.le))
  have hharm : ∑ n ∈ Icc 1 N, ((n : ℝ))⁻¹ ≤ 1 + Real.log N := by
    have := harmonic_le_one_add_log N
    simpa [harmonic_eq_sum_Icc] using this
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc kmsNormSq (fun n => midpoint 1 n - midpoint β n) N
      ≤ ∑ n ∈ Icc 1 N, (β - 1) ^ 2 / 2 * (Real.log N ^ 5 * (n : ℝ)⁻¹) :=
        sum_le_sum hterm
    _ = (β - 1) ^ 2 / 2 * (Real.log N ^ 5 * ∑ n ∈ Icc 1 N, ((n : ℝ))⁻¹) := by
        rw [← mul_sum, ← mul_sum]
    _ ≤ (β - 1) ^ 2 / 2 * (Real.log N ^ 5 * (1 + Real.log N)) := by
        gcongr

/-- **Clean form.** For `N ≥ 3` (so `log N ≥ 1`),
`‖c₁ - c_β‖²_{*,N} ≤ (β-1)² (log N)⁶`, i.e. `‖c₁ - c_β‖_{*,N} ≤ |β - 1| (log N)³`. -/
theorem kms_critical_limit_clean (β : ℝ) (hβ : 1 ≤ β) (N : ℕ) (hN : 3 ≤ N) :
    kmsNormSq (fun n => midpoint 1 n - midpoint β n) N ≤
      (β - 1) ^ 2 * Real.log N ^ 6 := by
  have hlog1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  refine (kms_critical_limit β hβ N).trans ?_
  have h5 : 0 ≤ Real.log N ^ 5 := by positivity
  have : Real.log N ^ 5 * (1 + Real.log N) ≤ 2 * Real.log N ^ 6 := by nlinarith
  nlinarith [sq_nonneg (β - 1)]

end GppKMSCriticalLimit
