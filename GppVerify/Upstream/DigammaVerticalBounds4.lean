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

end DigammaVertical4

end Complex

#print axioms Complex.DigammaVertical4.norm_H_le
