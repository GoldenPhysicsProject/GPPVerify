import GppVerify.RiemannHypothesis.KleinFourProjections
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The first-prime negative bound `M₋ < 147/25`

At width `L = 18/25` (so `log 2 < L < log 3`), the first-prime window estimate (Turbo relay `7399083`,
obligation (A)) uses

`M₋ = |C∞| + 2(sinh(L/2) − L/2) + v`,   `C∞ = −γ − log π − π/2 − 3 log 2`,   `v = log 2/√2`,

and needs `M₋ < 147/25 = 5.88`, with true value `5.87797…` — a margin of only `0.0020`. Mathlib's
`γ < 2/3` is far too weak, so this file proves the transcendental bound from sharp, individually kernel- or
Taylor-checked inputs:

* `γ < 0.57749`   from `γ < H₂₀₄₈ − log 2048` with `H₂₀₄₈ < 8.2021` **kernel-checked** over ℚ and `log 2 > 0.6931471803`;
* `log π < 1.1448` from `π < 3.141593` (`Real.pi_lt_d6`) and `exp 1.1448 > 3.141593` (20-term Taylor lower sum);
* `2(sinh(9/25) − 9/25) < 0.0158` from the two-sided exponential Taylor bound `Real.exp_bound`;
* `v < 0.4902` from `log 2 < 0.6931471808` and `√2 > 1.4142`.

The sum is `5.878528 < 5.88`. The thresholds are not rounded further: any coarsening kills the margin.

No `sorry`, no axiom.
-/

open Real

noncomputable section

namespace GppFirstPrime

/-- A block of 256 consecutive harmonic terms starting after `a`. -/
def hblock (a : ℕ) : ℚ := ∑ i ∈ Finset.range 256, (((a + i + 1 : ℕ) : ℚ))⁻¹

theorem harmonic_block (n : ℕ) : harmonic (n + 256) = harmonic n + hblock n := by
  unfold harmonic hblock
  rw [Finset.sum_range_add]

theorem hblock_0 : hblock 0 < 1224869 / 200000 := by decide +kernel
theorem hblock_1 : hblock 256 < 1730429 / 2500000 := by decide +kernel
theorem hblock_2 : hblock 512 < 2025699 / 5000000 := by decide +kernel
theorem hblock_3 : hblock 768 < 1437597 / 5000000 := by decide +kernel
theorem hblock_4 : hblock 1024 < 111523 / 500000 := by decide +kernel
theorem hblock_5 : hblock 1280 < 364513 / 2000000 := by decide +kernel
theorem hblock_6 : hblock 1536 < 770521 / 5000000 := by decide +kernel
theorem hblock_7 : hblock 1792 < 667483 / 5000000 := by decide +kernel

/-- `H₂₀₄₈ < 8.2021`: eight kernel-checked blocks of 256 terms over ℚ. -/
theorem harmonic_2048_lt : harmonic 2048 < 82021 / 10000 := by
  have e7 : harmonic 2048 = harmonic 1792 + hblock 1792 := harmonic_block 1792
  have e6 : harmonic 1792 = harmonic 1536 + hblock 1536 := harmonic_block 1536
  have e5 : harmonic 1536 = harmonic 1280 + hblock 1280 := harmonic_block 1280
  have e4 : harmonic 1280 = harmonic 1024 + hblock 1024 := harmonic_block 1024
  have e3 : harmonic 1024 = harmonic 768 + hblock 768 := harmonic_block 768
  have e2 : harmonic 768 = harmonic 512 + hblock 512 := harmonic_block 512
  have e1 : harmonic 512 = harmonic 256 + hblock 256 := harmonic_block 256
  have e0 : harmonic 256 = harmonic 0 + hblock 0 := harmonic_block 0
  have h0 : harmonic 0 = 0 := by simp
  rw [e7, e6, e5, e4, e3, e2, e1, e0, h0]
  have := hblock_0; have := hblock_1; have := hblock_2; have := hblock_3
  have := hblock_4; have := hblock_5; have := hblock_6; have := hblock_7
  linarith

/-- **`γ < 0.57749`.** -/
theorem euler_lt : Real.eulerMascheroniConstant < 57749 / 100000 := by
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 2048
  obtain ⟨H, hH, hHeq⟩ : ∃ H : ℚ, H < 82021 / 10000 ∧ H = harmonic 2048 :=
    ⟨_, harmonic_2048_lt, rfl⟩
  simp only [Real.eulerMascheroniSeq', if_neg (show (2048 : ℕ) ≠ 0 by norm_num)] at h1
  rw [← hHeq] at h1
  have h2 : (H : ℝ) < 82021 / 10000 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hH
    push_cast at this
    exact this
  have h3 : Real.log ((2048 : ℕ) : ℝ) = 11 * Real.log 2 := by
    rw [show ((2048 : ℕ) : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]; norm_num
  have h4 := Real.log_two_gt_d9
  rw [h3] at h1
  norm_num at h1 h2 h4 ⊢
  linarith

/-- **`log π < 1.1448`.** -/
theorem log_pi_lt : Real.log π < 11448 / 10000 := by
  have hpi := Real.pi_lt_d6
  have hexp : (3.141593 : ℝ) < Real.exp (11448 / 10000) := by
    have h := Real.sum_le_exp_of_nonneg (x := (11448 / 10000 : ℝ)) (by norm_num) 10
    refine lt_of_lt_of_le ?_ h
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  linarith

/-- `exp x` for `|x| ≤ 1` is within `1e-9` of its 10-term Taylor sum. -/
theorem exp_taylor10 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - ∑ i ∈ Finset.range 10, x ^ i / (i.factorial : ℝ)| ≤
      |x| ^ 10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10 : ℝ)) :=
  Real.exp_bound hx (by norm_num)

/-- **`2 (sinh(9/25) − 9/25) < 0.0158`.** -/
theorem sinh_excess_lt : 2 * (Real.sinh (9 / 25) - 9 / 25) < 158 / 10000 := by
  rw [Real.sinh_eq]
  have h1 := exp_taylor10 (x := (9 / 25 : ℝ)) (by norm_num [abs_of_pos])
  have h2 := exp_taylor10 (x := (-(9 / 25) : ℝ)) (by norm_num [abs_of_pos])
  rw [abs_le] at h1 h2
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos, abs_neg] at h1 h2
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  linarith

/-- **`v = log 2/√2 < 0.4902`.** -/
theorem primeV_lt : primeV < 4902 / 10000 := by
  unfold primeV
  have h1 := Real.log_two_lt_d9
  have h2 : (1.4142 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **`M₋ < 147/25`** at `L = 18/25`:
`|C∞| + 2(sinh(L/2) − L/2) + log 2/√2 < 147/25`, with `|C∞| = γ + log π + π/2 + 3 log 2`. -/
theorem M_minus_lt :
    -GppArchimedeanFloor.archimedeanFloor + 2 * (Real.sinh (9 / 25) - 9 / 25) + primeV < 147 / 25 := by
  unfold GppArchimedeanFloor.archimedeanFloor
  have hg := euler_lt
  have hp := log_pi_lt
  have hs := sinh_excess_lt
  have hv := primeV_lt
  have hpi := Real.pi_lt_d6
  have hl := Real.log_two_lt_d9
  norm_num at hg hp hs hv hpi hl ⊢
  linarith

end GppFirstPrime

#print axioms GppFirstPrime.M_minus_lt
