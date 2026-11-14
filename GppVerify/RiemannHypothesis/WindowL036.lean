import GppVerify.RiemannHypothesis.WindowBlockL036
import GppVerify.RiemannHypothesis.WindowAssembly
import GppVerify.Upstream.LogArctanBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The first prime-visible window `supp f ⊂ [-9/25, 9/25]`, conditional on input (b) only

`weilForm_autocorr_nonneg_l036`: for every real test function `g` vanishing outside
`[-9/25, 9/25]`, `weilForm (autocorr g) ≥ 0`, **provided** the piecewise-polynomial minorant `mfun`
of `WindowMinorantL036` satisfies

* `mfun r ≤ Ψ₂(r) - β₂(25)` on `[-25, 25]` (`symbolTwo`, `betaTwo`), and
* `|mfun r| ≤ 8` on `[-25, 25]`.

These two hypotheses are input (b) of the certificate. They are finite statements about 100 explicit
polynomials against the digamma function, **not** proved here; nothing here asserts them.
Everything else is proved:
* input (a), the finite block (`GppWindowBlockL036.block_bound`, kernel-checked tables);
* input (c), the identification of the minorant form (`GppWindowAssembly.minorantForm_eq_B`);
* the tail condition (`tail_mu_nonneg`, `tail_cond`) and `β₂(25) ≥ b_lo` (`betaTwo_ge_bLo`), here.

The window `[-9/25, 9/25]` is the first one whose autocorrelation reaches `log 2`
(`2 · 9/25 = 0.72 > log 2`), so the prime `2` is visible; rung 0 stops at `log 2 / 2`.
Unconditional implication; no `sorry`, no axioms. Nothing here concerns the zeros.
-/

namespace GppWindowL036

open Set MeasureTheory GppMeyerSpectralWeil GppArithmeticReflection GppWeilLadder
  GppRungOneReductionTwo GppWindowBilinear GppWindowTail GppWindowAssembly GppWindowPolyBasis
  GppWindowBasisL036 GppWindowMinorantL036 GppWindowBlockDataL036 GppWindowBlockL036

/-! ### `β₂(25) ≥ b_lo` -/

/-- A rational point just below `25/(2π)`. -/
def x0Q : ℚ := 3978873577 / 1000000000

theorem x0_le : ((x0Q : ℚ) : ℝ) ≤ 25 / (2 * Real.pi) := by
  have hhi : Real.pi < (314159265358979323847 / 10 ^ 20 : ℝ) := by
    have := Real.pi_lt_d20; norm_num at this ⊢; linarith
  rw [le_div_iff₀ (by positivity)]
  unfold x0Q; push_cast
  nlinarith

/-- The 15-term partial sum of the log series at `x0`, exactly. -/
def logSumQ : ℚ :=
  let u : ℚ := (x0Q - 1) / (x0Q + 1)
  ((List.range 15).map fun k : ℕ => 2 * (1 / (2 * (k : ℚ) + 1)) * u ^ (2 * k + 1 : ℕ)).sum

theorem logSumQ_eq :
    Real.logSeriesSum ((((x0Q : ℚ) : ℝ) - 1) / (((x0Q : ℚ) : ℝ) + 1)) 15 = ((logSumQ : ℚ) : ℝ) := by
  unfold Real.logSeriesSum logSumQ
  simp only
  rw [← sum_range_eq_list, Rat.cast_sum]
  push_cast; rfl

/-- `log x0 ≥ 13811522 / 10^7`. -/
theorem log_x0_ge : (138099874 / 10 ^ 8 : ℝ) ≤ Real.log ((x0Q : ℚ) : ℝ) := by
  have h := Real.sum_le_log (x := ((x0Q : ℚ) : ℝ)) (by unfold x0Q; norm_num) 15
  rw [logSumQ_eq] at h
  have hq : (138099874 / 10 ^ 8 : ℚ) ≤ logSumQ := by decide +kernel
  have := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at this
  linarith

theorem betaTwo_ge_bLo : ((bLoQ : ℚ) : ℝ) ≤ betaTwo 25 := by
  have hlog : (138099874 / 10 ^ 8 : ℝ) ≤ Real.log (25 / (2 * Real.pi)) :=
    log_x0_ge.trans (Real.log_le_log (by unfold x0Q; norm_num) x0_le)
  have hl2 := Real.log_two_lt_d9
  have hs2 : (141421356 / 10 ^ 8 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hA : primeTwoA ≤ 2 * (6931471808 / 10 ^ 10) / (141421356 / 10 ^ 8) := by
    unfold primeTwoA
    have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num at hl2
    nlinarith
  unfold betaTwo
  have hb : ((bLoQ : ℚ) : ℝ) ≤ 138099874 / 10 ^ 8 - 1 / 25 -
      2 * (6931471808 / 10 ^ 10) / (141421356 / 10 ^ 8) := by
    unfold bLoQ; push_cast; norm_num
  linarith

/-! ### The scalar tail condition -/

theorem tail_mu_nonneg :
    0 ≤ betaTwo 25 - 2 * ℓR * (2 * ((ℓR / 2) ^ 32 * Real.exp (ℓR / 2)) ^ 2 +
      8 * 25 * ((25 * ℓR) ^ 32 / (32 : ℕ).factorial) ^ 2 / Real.pi) := by
  have hb := betaTwo_ge_bLo
  have he : Real.exp (ℓR / 2) ≤ 3 := by
    have := exp_half_le; rwa [show 1 / 2 * ℓR = ℓR / 2 by ring] at this
  have hpi : 3 < Real.pi := Real.pi_gt_three
  rw [ℓR_eq] at he ⊢
  have hS : ((25 * (9 / 25 : ℝ)) ^ 32 / (32 : ℕ).factorial) ^ 2 ≤ 1 / 10 ^ 9 := by
    norm_num [Nat.factorial]
  have hP : ((9 / 25 / 2 : ℝ) ^ 32 * Real.exp (9 / 25 / 2)) ^ 2 ≤ ((9 / 50) ^ 32 * 3) ^ 2 := by
    rw [show (9 / 25 / 2 : ℝ) = 9 / 50 by norm_num]
    rw [show (9 / 25 / 2 : ℝ) = 9 / 50 by norm_num] at he
    gcongr
  have h1 : 8 * 25 * ((25 * (9 / 25 : ℝ)) ^ 32 / (32 : ℕ).factorial) ^ 2 / Real.pi ≤
      8 * 25 * (1 / 10 ^ 9) / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hbq : ((bLoQ : ℚ) : ℝ) ≥ 36 / 100 := by unfold bLoQ; push_cast; norm_num
  have : (2 * (9 / 25) * (2 * ((9 / 50 : ℝ) ^ 32 * 3) ^ 2 + 8 * 25 * (1 / 10 ^ 9) / 3)) ≤ 36 / 100 := by
    norm_num
  nlinarith

theorem tail_cond :
    ((32 : ℕ) : ℝ) * (2 * ℓR * (2 * Real.exp (ℓR / 2) * ((ℓR / 2) ^ 32 * Real.exp (ℓR / 2)) +
      8 * 25 * ((25 * ℓR) ^ 32 / (32 : ℕ).factorial) / Real.pi)) ^ 2 ≤
      ((lamPrimeQ : ℚ) : ℝ) * (betaTwo 25 - 2 * ℓR * (2 * ((ℓR / 2) ^ 32 * Real.exp (ℓR / 2)) ^ 2 +
        8 * 25 * ((25 * ℓR) ^ 32 / (32 : ℕ).factorial) ^ 2 / Real.pi)) := by
  have hb := betaTwo_ge_bLo
  have he : Real.exp (ℓR / 2) ≤ 3 := by
    have := exp_half_le; rwa [show 1 / 2 * ℓR = ℓR / 2 by ring] at this
  have he0 : 0 < Real.exp (ℓR / 2) := Real.exp_pos _
  have hpi : 3 < Real.pi := Real.pi_gt_three
  rw [ℓR_eq] at he he0 ⊢
  set S : ℝ := (25 * (9 / 25 : ℝ)) ^ 32 / (32 : ℕ).factorial
  have hS0 : 0 ≤ S := by positivity
  have hS : S ≤ 2 / 10 ^ 5 := by simp only [S]; norm_num [Nat.factorial]
  set E : ℝ := Real.exp (9 / 25 / 2)
  -- the left side
  have hκ : 2 * E * ((9 / 25 / 2 : ℝ) ^ 32 * E) + 8 * 25 * S / Real.pi ≤
      2 * 3 * ((9 / 50) ^ 32 * 3) + 8 * 25 * (2 / 10 ^ 5) / 3 := by
    have h1 : 2 * E * ((9 / 25 / 2 : ℝ) ^ 32 * E) ≤ 2 * 3 * ((9 / 50) ^ 32 * 3) := by
      have : (9 / 25 / 2 : ℝ) = 9 / 50 := by norm_num
      rw [this]
      have hp : (0 : ℝ) ≤ (9 / 50) ^ 32 := by positivity
      nlinarith
    have h2 : 8 * 25 * S / Real.pi ≤ 8 * 25 * (2 / 10 ^ 5) / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    linarith
  have hκ0 : 0 ≤ 2 * E * ((9 / 25 / 2 : ℝ) ^ 32 * E) + 8 * 25 * S / Real.pi := by positivity
  have hL : ((32 : ℕ) : ℝ) * (2 * (9 / 25) * (2 * E * ((9 / 25 / 2 : ℝ) ^ 32 * E) +
      8 * 25 * S / Real.pi)) ^ 2 ≤
      32 * (2 * (9 / 25) * (2 * 3 * ((9 / 50) ^ 32 * 3) + 8 * 25 * (2 / 10 ^ 5) / 3)) ^ 2 := by
    push_cast; gcongr
  -- the right side
  have hμ := tail_mu_nonneg
  rw [ℓR_eq] at hμ
  have hS2 : S ^ 2 ≤ 1 / 10 ^ 9 := by nlinarith
  have hP : ((9 / 25 / 2 : ℝ) ^ 32 * E) ^ 2 ≤ ((9 / 50) ^ 32 * 3) ^ 2 := by
    have : (9 / 25 / 2 : ℝ) = 9 / 50 := by norm_num
    rw [this]; gcongr
  have hmu_lo : 36 / 100 - 2 * (9 / 25) * (2 * ((9 / 50 : ℝ) ^ 32 * 3) ^ 2 + 8 * 25 * (1 / 10 ^ 9) / 3) ≤
      betaTwo 25 - 2 * (9 / 25) * (2 * ((9 / 25 / 2 : ℝ) ^ 32 * E) ^ 2 + 8 * 25 * S ^ 2 / Real.pi) := by
    have hbq : ((bLoQ : ℚ) : ℝ) ≥ 36 / 100 := by unfold bLoQ; push_cast; norm_num
    have h2 : 8 * 25 * S ^ 2 / Real.pi ≤ 8 * 25 * (1 / 10 ^ 9) / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    nlinarith
  have hlam : ((lamPrimeQ : ℚ) : ℝ) ≥ 27 / 10 ^ 5 := by
    have h : (27 / 10 ^ 5 : ℚ) ≤ lamPrimeQ := by
      unfold lamPrimeQ lamQ resQ ellQ; norm_num
    have := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at this
    linarith
  have hfin : 32 * (2 * (9 / 25) * (2 * 3 * ((9 / 50 : ℝ) ^ 32 * 3) + 8 * 25 * (2 / 10 ^ 5) / 3)) ^ 2 ≤
      27 / 10 ^ 5 * (36 / 100 - 2 * (9 / 25) * (2 * ((9 / 50 : ℝ) ^ 32 * 3) ^ 2 +
        8 * 25 * (1 / 10 ^ 9) / 3)) := by norm_num
  have hmu0 : 0 ≤ 36 / 100 - 2 * (9 / 25) * (2 * ((9 / 50 : ℝ) ^ 32 * 3) ^ 2 +
      8 * 25 * (1 / 10 ^ 9) / 3) := by norm_num
  calc _ ≤ 32 * (2 * (9 / 25) * (2 * 3 * ((9 / 50) ^ 32 * 3) + 8 * 25 * (2 / 10 ^ 5) / 3)) ^ 2 := hL
    _ ≤ 27 / 10 ^ 5 * (36 / 100 - 2 * (9 / 25) * (2 * ((9 / 50 : ℝ) ^ 32 * 3) ^ 2 +
          8 * 25 * (1 / 10 ^ 9) / 3)) := hfin
    _ ≤ _ := mul_le_mul hlam hmu_lo hmu0 (by linarith)

/-! ### The window theorem -/

theorem two_ell_lt_log_three : 2 * ℓR < Real.log 3 := by
  rw [ℓR_eq, Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 : Real.exp (2 * (9 / 25)) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
  have h2 := Real.exp_one_lt_d9
  linarith

theorem lamPrimeQ_nonneg : (0 : ℝ) ≤ ((lamPrimeQ : ℚ) : ℝ) := by
  have h : (0 : ℚ) ≤ lamPrimeQ := by unfold lamPrimeQ lamQ resQ ellQ; norm_num
  exact_mod_cast h

/-- **The first prime-visible window, conditional on input (b).** If the minorant satisfies
`mfun ≤ Ψ₂ - β₂(25)` and `|mfun| ≤ 8` on `[-25, 25]`, then `weilForm (autocorr g) ≥ 0` for every real
test function `g` vanishing outside `[-9/25, 9/25]`. -/
theorem weilForm_autocorr_nonneg_l036
    (hb : ∀ r ∈ Icc (-25 : ℝ) 25, mfun r ≤ symbolTwo r - betaTwo 25)
    (hb8 : ∀ r ∈ Icc (-25 : ℝ) 25, |mfun r| ≤ 8)
    {g : ℝ → ℝ} (hg : IsTestFunction g) (hs : HasSupportIn g (9 / 25)) :
    0 ≤ weilForm (autocorr g) := by
  have hs' : HasSupportIn g ℓR := by rw [ℓR_eq]; exact hs
  have hmi : IntegrableOn mfun (Icc (-25 : ℝ) 25) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp intervalIntegrable_mfun
  exact weilForm_autocorr_nonneg_of_window_certificate (ℓ := ℓR) (T := 25) (m := mfun) (Mm := 8)
    hg ℓR_nonneg hs' two_ell_lt_log_three (by norm_num) hmi hb hb8 phi continuous_phi phi_orth
    phi_d_pos phi_span lamPrimeQ_nonneg (block_bound betaTwo_ge_bLo hb8 le_rfl) tail_mu_nonneg
    tail_cond

end GppWindowL036

#print axioms GppWindowL036.betaTwo_ge_bLo
#print axioms GppWindowL036.tail_cond
#print axioms GppWindowL036.weilForm_autocorr_nonneg_l036
