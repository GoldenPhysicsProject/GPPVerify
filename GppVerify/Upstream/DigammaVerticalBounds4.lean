import GppVerify.Upstream.DigammaVerticalBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# A fourth-order two-sided bound for `Re ψ` on vertical lines

`Complex.re_digamma_mem_Icc` encloses `Re ψ(a + b i)` in an interval of width `≈ 3/(4(a+M)²)`. For
rigorous rational enclosures at the `10⁻⁹` level that is too coarse (it needs `M ≈ 3·10⁴` terms).
This file adds the next Stirling term and proves an enclosure of width `O((a+M)⁻⁴)`, uniform in `b`:

**`re_digamma_mem_Icc4`.** For `a > 0`, `b` real and `M : ℕ` with `a + M ≥ 1`, put `y = a + M` and
`G₄ = ½ log((y - ½)² + b²) + (1/24) · ((y - ½)² - b²)/((y - ½)² + b²)² - Σ_{k<M} (a+k)/((a+k)² + b²)`.
Then `|Re ψ(a + b i) - G₄| ≤ 1/(32 (y - ½)⁴)`.

**Route.** For `x ≥ 1` and `v = x + b i`, `w = 1/(2v)` (so `‖w‖ ≤ ½`):
* `x/(x² + b²) = Re 2w`, `½ log((x ± ½)² + b²) = log‖v‖ + Re log(1 ± w)`,
  `Re 1/(x ± ½ + b i)² = Re 4w²/(1 ± w)²`;
* so the per-term error of the corrected telescoping identity is `-Re H(w)` with
  `H(w) = log(1+w) - log(1-w) - 2w - (2/3) w³/(1 - w²)²` (`perTerm_eq`);
* `‖H(w)‖ ≤ 4‖w‖⁵` for `‖w‖ ≤ ½`, from Mathlib's Taylor remainder for `log(1 + z)` (`norm_H_le`);
* the telescoped sum, the Gauss series of `ψ` (`hasSum_reTerm`) and `harmonic N - log N → γ` give
  `Re ψ(y + b i) = ½ log((y-½)² + b²) + (1/24)Q(y - ½) - Σ_{n≥0} err(y + n)` (`re_digamma_eq_tsum`),
  and `Σ 1/(8(y+n)⁵) ≤ 1/(32(y - ½)⁴)`.

Numerically (mpmath, evidence only) the true constant is `≈ 7/960 ≈ 0.0073`; `1/32` is a safe bound.
Unconditional; no `sorry`, no axioms.
-/

open Filter Topology Set Finset Complex

namespace Complex

namespace DigammaVertical4

open DigammaGauss DigammaVertical

/-- `Re 1/(t + b i)² = (t² - b²)/(t² + b²)²`. -/
noncomputable def Q (b t : ℝ) : ℝ := (t ^ 2 - b ^ 2) / (t ^ 2 + b ^ 2) ^ 2

/-- The per-term error of the corrected telescoping identity. -/
noncomputable def err (b x : ℝ) : ℝ :=
  phi b x - (logPot b (x + 1 / 2) - logPot b (x - 1 / 2)) - (Q b (x + 1 / 2) - Q b (x - 1 / 2)) / 24

/-- `H(w) = log(1+w) - log(1-w) - 2w - (2/3) w³/(1 - w²)²`. -/
noncomputable def H (w : ℂ) : ℂ :=
  log (1 + w) - log (1 - w) - 2 * w - 2 / 3 * w ^ 3 / (1 - w ^ 2) ^ 2

/-! ### (A) The analytic estimate `‖H(w)‖ ≤ 4‖w‖⁵` -/

theorem logTaylor_six (z : ℂ) :
    logTaylor 6 z = z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 + z ^ 5 / 5 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring

theorem norm_H_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖H w‖ ≤ 4 * ‖w‖ ^ 5 := by
  have hw1 : ‖w‖ < 1 := by linarith
  have hnw : ‖-w‖ = ‖w‖ := norm_neg w
  have r1 := norm_log_sub_logTaylor_le 5 hw1
  have r2 := norm_log_sub_logTaylor_le 5 (hnw ▸ hw1 : ‖-w‖ < 1)
  rw [hnw] at r2
  set R1 := log (1 + w) - logTaylor (5 + 1) w
  set R2 := log (1 + -w) - logTaylor (5 + 1) (-w)
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have bR : ∀ R : ℂ, ‖R‖ ≤ ‖w‖ ^ (5 + 1) * (1 - ‖w‖)⁻¹ / ((5 : ℕ) + 1) → ‖R‖ ≤ ‖w‖ ^ 5 / 6 := by
    intro R hR
    refine hR.trans ?_
    push_cast
    have : ‖w‖ ^ 6 * (1 - ‖w‖)⁻¹ ≤ ‖w‖ ^ 5 * (1 / 2) * 2 := by
      have h6 : ‖w‖ ^ 6 = ‖w‖ ^ 5 * ‖w‖ := by ring
      rw [h6]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hw (by positivity)) hinv (by positivity)
        (by positivity)
    nlinarith
  have b1 := bR R1 r1
  have b2 := bR R2 r2
  -- the rational part
  have hden : (3 / 4 : ℝ) ≤ ‖1 - w ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (w ^ 2)
    rw [norm_one, norm_pow] at this
    nlinarith
  have hden0 : (1 - w ^ 2) ≠ 0 := by
    intro h; rw [h, norm_zero] at hden; norm_num at hden
  have hrat : ‖2 / 3 * w ^ 3 * (1 - 1 / (1 - w ^ 2) ^ 2)‖ ≤ 8 / 3 * ‖w‖ ^ 5 := by
    have e : 1 - 1 / (1 - w ^ 2) ^ 2 = (w ^ 4 - 2 * w ^ 2) / (1 - w ^ 2) ^ 2 := by
      field_simp; ring
    have hn23 : ‖(2 / 3 : ℂ)‖ = 2 / 3 := by norm_num
    rw [e, norm_mul, norm_mul, hn23, norm_pow, norm_div, norm_pow]
    have hnum : ‖w ^ 4 - 2 * w ^ 2‖ ≤ (9 / 4) * ‖w‖ ^ 2 := by
      calc ‖w ^ 4 - 2 * w ^ 2‖ ≤ ‖w ^ 4‖ + ‖2 * w ^ 2‖ := norm_sub_le _ _
        _ = ‖w‖ ^ 4 + 2 * ‖w‖ ^ 2 := by simp [norm_pow]
        _ ≤ (9 / 4) * ‖w‖ ^ 2 := by nlinarith [pow_le_pow_left₀ hw0 hw 2]
    have hd2 : (9 / 16 : ℝ) ≤ ‖1 - w ^ 2‖ ^ 2 := by nlinarith
    have : ‖w ^ 4 - 2 * w ^ 2‖ / ‖1 - w ^ 2‖ ^ 2 ≤ 4 * ‖w‖ ^ 2 := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith [sq_nonneg ‖w‖]
    calc 2 / 3 * ‖w‖ ^ 3 * (‖w ^ 4 - 2 * w ^ 2‖ / ‖1 - w ^ 2‖ ^ 2)
        ≤ 2 / 3 * ‖w‖ ^ 3 * (4 * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 8 / 3 * ‖w‖ ^ 5 := by ring
  -- assemble
  have hsplit : H w = R1 - R2 + 2 / 5 * w ^ 5 + 2 / 3 * w ^ 3 * (1 - 1 / (1 - w ^ 2) ^ 2) := by
    simp only [H, R1, R2, show (5 : ℕ) + 1 = 6 from rfl, logTaylor_six]
    rw [show (1 : ℂ) + -w = 1 - w by ring]
    ring
  rw [hsplit]
  have h5 : ‖(2 / 5 : ℂ) * w ^ 5‖ = 2 / 5 * ‖w‖ ^ 5 := by
    rw [norm_mul, norm_pow]; norm_num
  calc ‖R1 - R2 + 2 / 5 * w ^ 5 + 2 / 3 * w ^ 3 * (1 - 1 / (1 - w ^ 2) ^ 2)‖
      ≤ ‖R1‖ + ‖R2‖ + ‖(2 / 5 : ℂ) * w ^ 5‖ + ‖2 / 3 * w ^ 3 * (1 - 1 / (1 - w ^ 2) ^ 2)‖ := by
        have t1 := norm_add_le (R1 - R2 + 2 / 5 * w ^ 5) (2 / 3 * w ^ 3 * (1 - 1 / (1 - w ^ 2) ^ 2))
        have t2 := norm_add_le (R1 - R2) ((2 / 5 : ℂ) * w ^ 5)
        have t3 := norm_sub_le R1 R2
        linarith
    _ ≤ ‖w‖ ^ 5 / 6 + ‖w‖ ^ 5 / 6 + 2 / 5 * ‖w‖ ^ 5 + 8 / 3 * ‖w‖ ^ 5 := by
        rw [h5]; linarith
    _ ≤ 4 * ‖w‖ ^ 5 := by nlinarith [pow_nonneg hw0 5]


/-! ### (B) The per-term identity `err = -Re H(1/(2v))` and `|err(x)| ≤ 1/(8x⁵)` -/

theorem Q_eq_re (b t : ℝ) : Q b t = (((⟨t, b⟩ : ℂ))⁻¹ ^ 2).re := by
  rw [sq, mul_re, inv_re, inv_im, normSq_apply]
  unfold Q
  rcases eq_or_ne (t ^ 2 + b ^ 2) 0 with h | h
  · have ht : t = 0 := by nlinarith [sq_nonneg t, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg t, sq_nonneg b]
    subst ht; subst hb; simp
  · simp only
    field_simp

theorem logPot_eq (b t : ℝ) : logPot b t = Real.log ‖(⟨t, b⟩ : ℂ)‖ := by
  unfold logPot
  rw [Complex.norm_def, normSq_apply]
  simp only
  rw [Real.log_sqrt (by nlinarith [mul_self_nonneg t, mul_self_nonneg b])]
  ring_nf

theorem perTerm_eq {b x : ℝ} (hx : 1 ≤ x) :
    err b x = -(H (1 / (2 * (⟨x, b⟩ : ℂ)))).re := by
  set v : ℂ := ⟨x, b⟩ with hv
  set w : ℂ := 1 / (2 * v) with hw
  have hv0 : v ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hv] at this; linarith
  have hvw : v * w = 1 / 2 := by rw [hw]; field_simp
  have hp : (⟨x + 1 / 2, b⟩ : ℂ) = v * (1 + w) := by
    rw [mul_add, mul_one, hvw]; apply Complex.ext <;> simp [hv]
  have hm : (⟨x - 1 / 2, b⟩ : ℂ) = v * (1 - w) := by
    rw [mul_sub, mul_one, hvw]; apply Complex.ext <;> simp [hv]
  have h1w : 1 + w ≠ 0 := by
    intro h; have : (⟨x + 1 / 2, b⟩ : ℂ) = 0 := by rw [hp, h, mul_zero]
    have := congrArg Complex.re this; simp at this; linarith
  have h1w' : 1 - w ≠ 0 := by
    intro h; have : (⟨x - 1 / 2, b⟩ : ℂ) = 0 := by rw [hm, h, mul_zero]
    have := congrArg Complex.re this; simp at this; linarith
  -- φ
  have hphi : phi b x = (2 * w).re := by
    have : 2 * w = v⁻¹ := by rw [hw]; field_simp
    rw [this, hv, re_inv]; rfl
  -- log potentials
  have hlog : logPot b (x + 1 / 2) - logPot b (x - 1 / 2) = (log (1 + w) - log (1 - w)).re := by
    rw [logPot_eq, logPot_eq, hp, hm, norm_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hv0) (norm_ne_zero_iff.mpr h1w),
      Real.log_mul (norm_ne_zero_iff.mpr hv0) (norm_ne_zero_iff.mpr h1w'), sub_re, log_re, log_re]
    ring
  -- the Q-difference, with `U = w³/(1 - w²)²`
  set U : ℂ := w ^ 3 / (1 - w ^ 2) ^ 2 with hU
  have hQ : Q b (x + 1 / 2) - Q b (x - 1 / 2) = (((-16 : ℝ) : ℂ) * U).re := by
    rw [Q_eq_re, Q_eq_re, hp, hm, ← sub_re]
    congr 1
    have hvinv : v⁻¹ = 2 * w := by rw [hw]; field_simp
    have h2 : (1 - w ^ 2) ≠ 0 := by
      have : 1 - w ^ 2 = (1 + w) * (1 - w) := by ring
      rw [this]; exact mul_ne_zero h1w h1w'
    rw [mul_inv, mul_inv, hvinv, hU]
    push_cast
    field_simp
    ring
  have hH : (H w).re = (log (1 + w) - log (1 - w)).re - (2 * w).re - (((2 / 3 : ℝ) : ℂ) * U).re := by
    simp only [H, hU, sub_re]
    congr 2
    push_cast; ring
  unfold err
  rw [hphi, hlog, hQ, hH, re_ofReal_mul, re_ofReal_mul]
  ring

theorem abs_err_le {b x : ℝ} (hx : 1 ≤ x) : |err b x| ≤ 1 / (8 * x ^ 5) := by
  rw [perTerm_eq hx, abs_neg]
  set v : ℂ := ⟨x, b⟩
  have hx0 : 0 < x := by linarith
  have hvx : x ≤ ‖v‖ := by
    have := Complex.abs_re_le_norm v; simp [v] at this; exact (le_abs_self x).trans this
  have hwn : ‖1 / (2 * v)‖ = 1 / (2 * ‖v‖) := by
    rw [norm_div, norm_one, norm_mul]; norm_num
  have hw2 : ‖1 / (2 * v)‖ ≤ 1 / (2 * x) := by
    rw [hwn]; exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hwh : ‖1 / (2 * v)‖ ≤ 1 / 2 := hw2.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  refine (Complex.abs_re_le_norm _).trans ((norm_H_le hwh).trans ?_)
  calc 4 * ‖1 / (2 * v)‖ ^ 5 ≤ 4 * (1 / (2 * x)) ^ 5 := by
        gcongr
    _ = 1 / (8 * x ^ 5) := by field_simp; ring

/-! ### (D) The tail sum -/

theorem inv_pow_five_le {x : ℝ} (hx : 1 / 2 < x) :
    1 / x ^ 5 ≤ (1 / (x - 1 / 2) ^ 4 - 1 / (x + 1 / 2) ^ 4) / 4 := by
  have h1 : 0 < x - 1 / 2 := by linarith
  have h2 : 0 < x + 1 / 2 := by linarith
  have hx0 : 0 < x := by linarith
  have key : 1 / (x - 1 / 2) ^ 4 - 1 / (x + 1 / 2) ^ 4
      = (4 * x ^ 3 + x) / ((x - 1 / 2) ^ 4 * (x + 1 / 2) ^ 4) := by
    rw [div_sub_div _ _ (pow_ne_zero 4 h1.ne') (pow_ne_zero 4 h2.ne')]
    congr 1; ring
  have hD : (x - 1 / 2) ^ 4 * (x + 1 / 2) ^ 4 = (x ^ 2 - 1 / 4) ^ 4 := by ring
  have hq : 0 < x ^ 2 - 1 / 4 := by nlinarith
  have hle : (x ^ 2 - 1 / 4) ^ 4 ≤ (x ^ 2) ^ 4 :=
    pow_le_pow_left₀ hq.le (by linarith) 4
  rw [key, hD, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hx0 3, pow_pos hx0 5, pow_pos hx0 6]


theorem sum_inv_pow_five_le {y : ℝ} (hy : 1 / 2 < y) (N : ℕ) :
    ∑ n ∈ range N, 1 / (y + n) ^ 5 ≤ 1 / (4 * (y - 1 / 2) ^ 4) := by
  have key : ∀ N : ℕ, ∑ n ∈ range N, 1 / (y + n) ^ 5
      ≤ (1 / (y - 1 / 2) ^ 4 - 1 / (y + N - 1 / 2) ^ 4) / 4 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have h := inv_pow_five_le (x := y + N) (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
      have e1 : y + (N : ℝ) + 1 / 2 = y + ((N + 1 : ℕ) : ℝ) - 1 / 2 := by push_cast; ring
      have e2 : y + (N : ℝ) - 1 / 2 = y + (N : ℝ) - 1 / 2 := rfl
      rw [e1] at h
      linarith
  refine (key N).trans ?_
  have h1 : 0 < y - 1 / 2 := by linarith
  have : 0 ≤ 1 / (y + N - 1 / 2) ^ 4 := by
    have : 0 < y + (N : ℝ) - 1 / 2 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
    positivity
  calc (1 / (y - 1 / 2) ^ 4 - 1 / (y + N - 1 / 2) ^ 4) / 4 ≤ (1 / (y - 1 / 2) ^ 4) / 4 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
    _ = 1 / (4 * (y - 1 / 2) ^ 4) := by rw [div_div, mul_comm]

theorem summable_err {b y : ℝ} (hy : 1 ≤ y) : Summable (fun n : ℕ => err b (y + n)) := by
  have hs2 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  refine Summable.of_norm_bounded hs2 (fun n => ?_)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.norm_eq_abs]
  refine (abs_err_le (by linarith)).trans ?_
  have h1 : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 8 * (y + n) ^ 5 := by
    push_cast
    have hb : (n : ℝ) + 1 ≤ y + n := by linarith
    have h1' : 1 ≤ y + n := by linarith
    calc ((n : ℝ) + 1) ^ 2 ≤ (y + n) ^ 2 := pow_le_pow_left₀ (by linarith) hb 2
      _ ≤ (y + n) ^ 5 := pow_le_pow_right₀ h1' (by norm_num)
      _ ≤ 8 * (y + n) ^ 5 := by nlinarith [pow_pos (by linarith : (0 : ℝ) < y + n) 5]
  exact one_div_le_one_div_of_le (by positivity) h1

theorem abs_tsum_err_le {b y : ℝ} (hy : 1 ≤ y) :
    |∑' n : ℕ, err b (y + n)| ≤ 1 / (32 * (y - 1 / 2) ^ 4) := by
  have hs := summable_err (b := b) hy
  have hb : ∀ N : ℕ, ∑ n ∈ range N, |err b (y + n)| ≤ 1 / (32 * (y - 1 / 2) ^ 4) := by
    intro N
    calc ∑ n ∈ range N, |err b (y + n)| ≤ ∑ n ∈ range N, 1 / (8 * (y + n) ^ 5) :=
          sum_le_sum fun n _ => abs_err_le (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      _ = (1 / 8) * ∑ n ∈ range N, 1 / (y + n) ^ 5 := by
          rw [mul_sum]; exact sum_congr rfl fun n _ => by field_simp
      _ ≤ (1 / 8) * (1 / (4 * (y - 1 / 2) ^ 4)) :=
          mul_le_mul_of_nonneg_left (sum_inv_pow_five_le (by linarith) N) (by norm_num)
      _ = 1 / (32 * (y - 1 / 2) ^ 4) := by field_simp; ring
  have habs : Summable (fun n : ℕ => |err b (y + n)|) := hs.abs
  calc |∑' n : ℕ, err b (y + n)| ≤ ∑' n : ℕ, |err b (y + n)| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using habs)).trans
          (le_of_eq (by simp [Real.norm_eq_abs]))
    _ ≤ 1 / (32 * (y - 1 / 2) ^ 4) :=
        habs.tsum_le_of_sum_range_le (fun N => hb N)

/-! ### (C) The limit identity -/

theorem sum_phi_telescope (b y : ℝ) (N : ℕ) :
    ∑ n ∈ range N, phi b (y + n) = logPot b (y + N - 1 / 2) - logPot b (y - 1 / 2)
      + (Q b (y + N - 1 / 2) - Q b (y - 1 / 2)) / 24 + ∑ n ∈ range N, err b (y + n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have e : y + ((N + 1 : ℕ) : ℝ) - 1 / 2 = y + (N : ℝ) + 1 / 2 := by push_cast; ring
    have e' : y + (N : ℝ) - 1 / 2 = y + (N : ℝ) - 1 / 2 := rfl
    rw [e]
    unfold err
    ring

theorem tendsto_Q (b : ℝ) (c : ℝ) : Tendsto (fun N : ℕ => Q b ((N : ℝ) + c)) atTop (𝓝 0) := by
  have hbound : ∀ t : ℝ, t ≠ 0 → |Q b t| ≤ 1 / t ^ 2 := by
    intro t ht
    unfold Q
    have hp : 0 < t ^ 2 + b ^ 2 := by positivity
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (t ^ 2 + b ^ 2) ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : |t ^ 2 - b ^ 2| ≤ t ^ 2 + b ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg t, sq_nonneg b]
    nlinarith [sq_nonneg t, sq_nonneg b, sq_nonneg (t ^ 2), mul_nonneg (sq_nonneg t) (sq_nonneg b)]
  have h2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + c) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => (N : ℝ) + c) atTop atTop :=
      tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
    exact (((tendsto_pow_atTop two_ne_zero).comp this).inv_tendsto_atTop).congr
      (fun N => by simp [Function.comp, one_div])
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_gt_atTop (Nat.ceil (|c| + 1))] with N hN
  rw [Real.norm_eq_abs]
  apply hbound
  have : (Nat.ceil (|c| + 1) : ℝ) < N := by exact_mod_cast hN
  have := Nat.le_ceil (|c| + 1)
  have := neg_abs_le c
  intro h0; linarith

/-- **`Re ψ(y + b i)` as the corrected telescoped sum.** For `y ≥ 1`. -/
theorem re_digamma_eq_tsum {b y : ℝ} (hy : 1 ≤ y) :
    (digamma ⟨y, b⟩).re
      = logPot b (y - 1 / 2) + Q b (y - 1 / 2) / 24 - ∑' n : ℕ, err b (y + n) := by
  have hy0 : 0 < y := by linarith
  have hS := (hasSum_reTerm (b := b) hy0).tendsto_sum_nat
  -- partial sums of the Gauss series via the telescoping identity
  have hpart : ∀ N : ℕ, ∑ n ∈ range N, reTerm y b n
      = (((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + (y + 1 / 2))) + logPot b (y - 1 / 2)
        - (Q b ((N : ℝ) + (y + 1 / 2)) - Q b (y - 1 / 2)) / 24
        - ∑ n ∈ range (N + 1), err b (y + n) + phi b y := by
    intro N
    rw [sum_reTerm]
    have ht := sum_phi_telescope b y (N + 1)
    rw [sum_range_succ'] at ht
    have e1 : y + ((N + 1 : ℕ) : ℝ) - 1 / 2 = (N : ℝ) + (y + 1 / 2) := by push_cast; ring
    rw [e1] at ht
    have e2 : ∀ n : ℕ, phi b ((n : ℝ) + 1 + y) = phi b (y + ((n + 1 : ℕ) : ℝ)) := by
      intro n; congr 1; push_cast; ring
    simp only [e2, Nat.cast_zero, add_zero] at ht ⊢
    linarith
  have hL : Tendsto (fun N : ℕ => (((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + (y + 1 / 2)))
      + logPot b (y - 1 / 2) - (Q b ((N : ℝ) + (y + 1 / 2)) - Q b (y - 1 / 2)) / 24
      - ∑ n ∈ range (N + 1), err b (y + n) + phi b y) atTop
      (𝓝 (Real.eulerMascheroniConstant + logPot b (y - 1 / 2) - (0 - Q b (y - 1 / 2)) / 24
        - ∑' n : ℕ, err b (y + n) + phi b y)) := by
    have h1 := tendsto_harmonic_sub_logPot b (y + 1 / 2)
    have h2 := tendsto_Q b (y + 1 / 2)
    have h3 : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), err b (y + n)) atTop
        (𝓝 (∑' n : ℕ, err b (y + n))) :=
      ((summable_err (b := b) hy).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    exact ((((h1.add_const _).sub ((h2.sub_const _).div_const 24)).sub h3).add_const _)
  have hU := tendsto_nhds_unique (hS.congr hpart) hL
  have e : (y : ℝ) / (y ^ 2 + b ^ 2) = phi b y := rfl
  rw [← e] at hU
  linarith

/-! ### (E) The enclosure -/

/-- **Fourth-order two-sided enclosure of `Re ψ` on a vertical line.** For `a > 0`, `b` real and
`M : ℕ` with `1 ≤ a + M`, with `y = a + M`:
`|Re ψ(a + b i) - G₄| ≤ 1/(32 (y - ½)⁴)`, where
`G₄ = ½ log((y-½)² + b²) + (1/24)((y-½)² - b²)/((y-½)² + b²)² - Σ_{k<M} (a+k)/((a+k)² + b²)`. -/
theorem re_digamma_abs_sub_le4 {a : ℝ} (ha : 0 < a) (b : ℝ) (M : ℕ) (hy : 1 ≤ a + M) :
    |(digamma ⟨a, b⟩).re - (Real.log ((a + M - 1 / 2) ^ 2 + b ^ 2) / 2
        + ((a + M - 1 / 2) ^ 2 - b ^ 2) / ((a + M - 1 / 2) ^ 2 + b ^ 2) ^ 2 / 24
        - ∑ k ∈ range M, (a + k) / ((a + k) ^ 2 + b ^ 2))|
      ≤ 1 / (32 * (a + M - 1 / 2) ^ 4) := by
  rw [re_digamma_shift ha b M, re_digamma_eq_tsum hy]
  have := abs_tsum_err_le (b := b) hy
  unfold logPot Q at *
  rw [show ∀ u v w s : ℝ, u + v - w - s - (u + v - s) = -w by intros; ring]
  rwa [abs_neg]

end DigammaVertical4

open DigammaVertical4 in
/-- Re-export: the fourth-order enclosure in the `Complex` namespace. -/
theorem re_digamma_mem_Icc4 {a : ℝ} (ha : 0 < a) (b : ℝ) (M : ℕ) (hy : 1 ≤ a + M) :
    |(digamma ⟨a, b⟩).re - (Real.log ((a + M - 1 / 2) ^ 2 + b ^ 2) / 2
        + ((a + M - 1 / 2) ^ 2 - b ^ 2) / ((a + M - 1 / 2) ^ 2 + b ^ 2) ^ 2 / 24
        - ∑ k ∈ range M, (a + k) / ((a + k) ^ 2 + b ^ 2))|
      ≤ 1 / (32 * (a + M - 1 / 2) ^ 4) :=
  re_digamma_abs_sub_le4 ha b M hy

end Complex

#print axioms Complex.DigammaVertical4.norm_H_le
#print axioms Complex.DigammaVertical4.abs_err_le
#print axioms Complex.DigammaVertical4.inv_pow_five_le
#print axioms Complex.re_digamma_mem_Icc4
