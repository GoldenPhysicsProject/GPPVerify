import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Mean/variance supplier: Young step, decreasing jump weight, two-channel criterion

Source: Codex/Discovery2, GPP-bridge PR #11 comment 2026-10-31 ("new full completed Weil
all-function positivity, L ≤ 29/100"), `discovery/short_support_mean_variance_weil.md`. Daniel
Toupin / Golden Physics Project, with AI assistance from Codex (statement) and Claude Code
(formalization).

Three exact real-analysis pieces of that argument, stated abstractly:

* `young_sq`: for complex `u, v` and `η > 0`, `‖u+v‖² ≥ (1−η)‖u‖² − (η⁻¹−1)‖v‖²`.
* `pole_lower_bound`: if `C = c₀ + c`, `‖c‖ ≤ d`, `‖S‖ ≤ s`, then (for `0 < η ≤ 1`)
  `2‖C‖² − 2‖S‖² ≥ 2(1−η)‖c₀‖² − 2(η⁻¹−1)d² − 2s²`.
* `jump_weight_bound`: for `w` antitone on `(0, L]` and `h ≥ 0` integrable there,
  `w(L) ∫₀ᴸ h ≤ ∫₀ᴸ w h`.
* `two_channel`: if `Q ≥ M a² + F G²` with `M ≥ κ L`, `F ≥ κ`, and
  `‖f‖² = L a² + G²`, then `Q ≥ κ ‖f‖²`.

**Scope.** These are the scalar inequalities only. The continuous variance identity
`∫∫|f(x+y) − f(x)|² = L‖g‖²`, the Cauchy bounds `‖c‖ ≤ d‖g‖`, the Weil quadratic form itself, and
the Arb-certified endpoint values `B_mean`, `B_fluct` (taken as hypotheses by `two_channel`) are
not formalized. Codex's CI receipts are not checked here. No claim about RH.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace GppMeanVarianceSupplier

/-- Young: `‖u+v‖² ≥ (1−η)‖u‖² − (η⁻¹−1)‖v‖²`. -/
theorem young_sq (u v : ℂ) {η : ℝ} (hη : 0 < η) :
    (1 - η) * ‖u‖ ^ 2 - (η⁻¹ - 1) * ‖v‖ ^ 2 ≤ ‖u + v‖ ^ 2 := by
  have h1 : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * (starRingEnd ℂ u * v).re + ‖v‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add]
    simp [Complex.mul_re]; ring
  have h2 : -(‖u‖ * ‖v‖) ≤ (starRingEnd ℂ u * v).re := by
    have := Complex.abs_re_le_norm (starRingEnd ℂ u * v)
    rw [norm_mul, Complex.norm_conj] at this
    linarith [neg_abs_le ((starRingEnd ℂ u * v).re)]
  have h3 : 2 * (‖u‖ * ‖v‖) ≤ η * ‖u‖ ^ 2 + η⁻¹ * ‖v‖ ^ 2 := by
    have hη' : η * η⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
    have hsq : 0 ≤ η * (‖u‖ - η⁻¹ * ‖v‖) ^ 2 := by positivity
    have e : η * (‖u‖ - η⁻¹ * ‖v‖) ^ 2 = η * ‖u‖ ^ 2 - 2 * (‖u‖ * ‖v‖) + η⁻¹ * ‖v‖ ^ 2 := by
      linear_combination (-2 * ‖u‖ * ‖v‖ + η⁻¹ * ‖v‖ ^ 2) * hη'
    linarith
  nlinarith [h1, h2, h3]

/-- Pole lower bound after Young: `2‖C‖² − 2‖S‖² ≥ 2(1−η)‖c₀‖² − 2(η⁻¹−1)d² − 2s²`. -/
theorem pole_lower_bound (c₀ c S : ℂ) {η d s : ℝ} (hη : 0 < η) (hc : ‖c‖ ≤ d) (hS : ‖S‖ ≤ s)
    (hη1 : η ≤ 1) :
    2 * (1 - η) * ‖c₀‖ ^ 2 - 2 * (η⁻¹ - 1) * d ^ 2 - 2 * s ^ 2 ≤
      2 * ‖c₀ + c‖ ^ 2 - 2 * ‖S‖ ^ 2 := by
  have hy := young_sq c₀ c hη
  have hc2 : ‖c‖ ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have hS2 : ‖S‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
  have h0 : 0 ≤ η⁻¹ - 1 := by
    have := one_le_inv_iff₀.mpr ⟨hη, hη1⟩
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hc2 h0]

/-- Decreasing jump weight: `w(L) ∫₀ᴸ h ≤ ∫₀ᴸ w h`. -/
theorem jump_weight_bound (w h : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (hw : AntitoneOn w (Ioc 0 L))
    (hh0 : ∀ y ∈ Ioc 0 L, 0 ≤ h y) (hhi : IntegrableOn h (Ioc 0 L))
    (hwh : IntegrableOn (fun y => w y * h y) (Ioc 0 L)) :
    w L * ∫ y in Ioc 0 L, h y ≤ ∫ y in Ioc 0 L, w y * h y := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on (hhi.const_mul _) hwh measurableSet_Ioc (fun y hy => ?_)
  exact mul_le_mul_of_nonneg_right (hw hy ⟨hL, le_rfl⟩ hy.2) (hh0 y hy)

/-- Two-channel positivity: mean channel `M a²` and fluctuation channel `F G²` both above
`κ` (per unit of `‖f‖² = L a² + G²`) give `Q ≥ κ‖f‖²`. -/
theorem two_channel {Q M F a G L κ nf : ℝ} (hM : κ * L ≤ M)
    (hF : κ ≤ F) (hQ : M * a ^ 2 + F * G ^ 2 ≤ Q) (hnf : nf = L * a ^ 2 + G ^ 2) :
    κ * nf ≤ Q := by
  rw [hnf]
  nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg a), mul_le_mul_of_nonneg_right hF (sq_nonneg G)]

end GppMeanVarianceSupplier
