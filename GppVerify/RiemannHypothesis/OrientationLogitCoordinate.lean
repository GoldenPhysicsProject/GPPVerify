import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The orientation (logit) coordinate `η = log(s/(1 − s))`

Source: Codex, GPP-bridge PR #11 comment 6145326782, realizing Daniel Toupin's orientation picture
("½ is like 0; 0 is like −∞; 1 is like +∞"). The coordinate is the logarithm of the existing Cayley
reciprocal: `e^{−η} = (1 − s)/s = −β(s)`.

* `re_logit`: `Re η = log|s| − log|1 − s|`.
* `re_logit_eq_zero_iff`: **`Re η = 0 ⟺ Re s = ½`** for `s ∉ {0, 1}`, i.e. the critical line is exactly
  the imaginary `η`-axis.
* `norm_ratio_on_line`: on `Re s = ½` the ratio `s/(1 − s)` is unimodular.
* `ratio_reflect`: `s ↦ 1 − s` inverts the ratio, so `η ↦ −η` on the principal branch away from the
  cut.

RH is thus the statement that the zeta zero `η`-labels are purely imaginary. The functional equation
alone gives only `±η` pairs. That `η` is the additive Haar coordinate, or the generator of a natural
Haar/Tate operator, is **not** claimed. **No RH claim.**
-/

namespace GppOrientationLogit

open Complex

/-- The orientation coordinate. -/
noncomputable def logit (s : ℂ) : ℂ := log (s / (1 - s))

theorem re_logit {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (logit s).re = Real.log ‖s‖ - Real.log ‖1 - s‖ := by
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [logit, log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr h1')]

theorem norm_eq_norm_one_sub_iff (s : ℂ) : ‖s‖ = ‖1 - s‖ ↔ s.re = 1 / 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq,
    normSq_apply, normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im]
  constructor <;> intro h <;> nlinarith

/-- **The critical line is the imaginary `η`-axis.** -/
theorem re_logit_eq_zero_iff {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (logit s).re = 0 ↔ s.re = 1 / 2 := by
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [re_logit h0 h1, sub_eq_zero, ← norm_eq_norm_one_sub_iff]
  constructor
  · intro h
    exact Real.log_injOn_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr h1') h
  · intro h; rw [h]

/-- On the critical line the ratio `s/(1 − s)` is unimodular. -/
theorem norm_ratio_on_line {s : ℂ} (hs : s.re = 1 / 2) : ‖s / (1 - s)‖ = 1 := by
  have h := (norm_eq_norm_one_sub_iff s).mpr hs
  have h1 : (1 : ℂ) - s ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  rw [norm_div, h, div_self (norm_ne_zero_iff.mpr h1)]

/-- The functional reflection `s ↦ 1 − s` inverts the ratio. -/
theorem ratio_reflect (s : ℂ) : (1 - s) / (1 - (1 - s)) = (s / (1 - s))⁻¹ := by
  rw [sub_sub_cancel, inv_div]

/-- The Cayley link: `(s/(1 − s))⁻¹ = −(s − 1)/s`. -/
theorem cayley_link (s : ℂ) : (s / (1 - s))⁻¹ = -((s - 1) / s) := by
  rw [inv_div, ← neg_div, neg_sub]

end GppOrientationLogit
