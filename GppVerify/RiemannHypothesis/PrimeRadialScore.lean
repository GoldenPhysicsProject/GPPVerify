import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The signed prime multiplier is the radial score of a positive Euler amplitude

Source: Codex, `research/codex/2026-10-04_finite_euler_score_scattering_phase.md`, §2.

Fix `L = log p > 0`, `c = cos θ ∈ [-1, 1]`, and put `r(σ) = e^{-σL} = p^{-σ}`,
`D(σ) = 1 − 2 r c + r²`, and the Poisson kernel `P(σ) = (1 − r²)/D`. For `σ > 0`:

* `normSq_euler_denominator`: `|1 − r e^{-iθ}|² = D` (so `|ζ_p(σ + it)|² = 1/D` with `θ = tL`);
* `hasDerivAt_neg_log_D`: `∂_σ (−log D) = L (1 − P)`; at `σ = 1/2` and `θ = t log p` this is the note's
  `∂_σ log|ζ_p(σ + it)|² = −W_p(t)`, where `W_p = (log p)(P − 1)`;
* `hasDerivAt_log_poisson`: `∂_σ log P = L (1 − P) + 2 L r²/(1 − r²)`, the normalized Poisson score; at
  `σ = 1/2` (`r² = 1/p`) the second term is the counterterm `2 log p/(p − 1)` (`counterterm_half`).

## Checks and scope

All claims check (they are exact calculus identities). **Not formalized:** the probability-measure
normalization `∫ P dθ/2π = 1` (so that the normalized score has mean zero), the Archimedean score
(§3, whose digamma form is in `ArchimedeanScatteringRatio`), the finite-Euler completed score and the
scattering-phase form `−ϑ_L' = m_L` (§§4–5), and the Paley–Wiener inequality the note reduces to, which is
**open** and not claimed. No RH claim.
-/

open Real

namespace GppPrimeRadialScore

/-- `r(σ) = e^{-σL}`. -/
noncomputable def rr (L σ : ℝ) : ℝ := Real.exp (-σ * L)

/-- `D(σ) = 1 − 2 r c + r²`. -/
noncomputable def DD (L c σ : ℝ) : ℝ := 1 - 2 * rr L σ * c + rr L σ ^ 2

/-- Poisson kernel `P(σ) = (1 − r²)/D`. -/
noncomputable def PP (L c σ : ℝ) : ℝ := (1 - rr L σ ^ 2) / DD L c σ

theorem rr_pos (L σ : ℝ) : 0 < rr L σ := Real.exp_pos _

theorem rr_lt_one (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) : rr L σ < 1 := by
  unfold rr; rw [Real.exp_lt_one_iff]; nlinarith

theorem DD_pos (L c σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) (hc : |c| ≤ 1) : 0 < DD L c σ := by
  have h1 := rr_lt_one L σ hL hσ
  have h0 := rr_pos L σ
  have hc1 : c ≤ 1 := (abs_le.mp hc).2
  unfold DD
  nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hc1)]

theorem hasDerivAt_rr (L σ : ℝ) : HasDerivAt (rr L) (-L * rr L σ) σ := by
  unfold rr
  have h : HasDerivAt (fun σ : ℝ => -σ * L) (-L) σ := by
    simpa using ((hasDerivAt_id σ).neg.mul_const L)
  simpa [mul_comm] using h.exp

/-- `|1 − r e^{-iθ}|² = D` with `c = cos θ`. -/
theorem normSq_euler_denominator (r θ : ℝ) :
    Complex.normSq (1 - (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) =
      1 - 2 * r * Real.cos θ + r ^ 2 := by
  have e : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem hasDerivAt_DD (L c σ : ℝ) :
    HasDerivAt (DD L c) ((2 * rr L σ - 2 * c) * (-L * rr L σ)) σ := by
  have hr := hasDerivAt_rr L σ
  have h0 := (((hr.const_mul 2).mul_const c).const_sub 1).add (hr.mul hr)
  have e : DD L c = fun σ => 1 - 2 * rr L σ * c + rr L σ * rr L σ := by
    funext σ; unfold DD; ring
  rw [e]
  exact h0.congr_deriv (by ring)

/-- `∂_σ (−log D) = L (1 − P)`. -/
theorem hasDerivAt_neg_log_D (L c σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) (hc : |c| ≤ 1) :
    HasDerivAt (fun σ => -Real.log (DD L c σ)) (L * (1 - PP L c σ)) σ := by
  have hD := DD_pos L c σ hL hσ hc
  have hr := hasDerivAt_rr L σ
  have hDd := hasDerivAt_DD L c σ
  have := (hDd.log hD.ne').neg
  refine this.congr_deriv ?_
  have hdef : DD L c σ = 1 - 2 * rr L σ * c + rr L σ ^ 2 := rfl
  unfold PP
  field_simp
  rw [hdef]
  ring

/-- **Normalized Poisson score.** -/
theorem hasDerivAt_log_poisson (L c σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) (hc : |c| ≤ 1) :
    HasDerivAt (fun σ => Real.log (PP L c σ))
      (L * (1 - PP L c σ) + 2 * L * rr L σ ^ 2 / (1 - rr L σ ^ 2)) σ := by
  have hD := DD_pos L c σ hL hσ hc
  have h1 := rr_lt_one L σ hL hσ
  have h0 := rr_pos L σ
  have hnum : 0 < 1 - rr L σ ^ 2 := by nlinarith
  have hr := hasDerivAt_rr L σ
  have hn : HasDerivAt (fun σ => 1 - rr L σ ^ 2) (-(2 * rr L σ * (-L * rr L σ))) σ := by
    simpa using (hr.pow 2).const_sub 1
  have hDd := hasDerivAt_DD L c σ
  have hP : HasDerivAt (PP L c) _ σ := hn.div hDd hD.ne'
  have := hP.log (div_pos hnum hD).ne'
  refine this.congr_deriv ?_
  have hdef : DD L c σ = 1 - 2 * rr L σ * c + rr L σ ^ 2 := rfl
  unfold PP
  field_simp
  rw [hdef]
  ring

/-- At `σ = 1/2`, `r² = 1/p` and the counterterm is `2 log p/(p − 1)`. -/
theorem counterterm_half (p : ℝ) (hp : 1 < p) :
    2 * Real.log p * rr (Real.log p) (1 / 2) ^ 2 / (1 - rr (Real.log p) (1 / 2) ^ 2) =
      2 * Real.log p / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have h : rr (Real.log p) (1 / 2) ^ 2 = 1 / p := by
    unfold rr
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(1 / 2) * Real.log p) = -Real.log p := by push_cast; ring
    rw [this, Real.exp_neg, Real.exp_log hp0, one_div]
  rw [h]
  have : p - 1 ≠ 0 := by linarith
  field_simp

end GppPrimeRadialScore
