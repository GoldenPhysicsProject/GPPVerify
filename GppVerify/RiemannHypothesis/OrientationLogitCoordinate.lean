import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

**The logistic squeeze** (Turbo, relaying Daniel, bridge CONVERSATION.md 2026-10-13): the inverse
of `η` is the logistic map, `s = 1/(1 + e^{−η})` (`logistic_logit`). On the real side, the odds map
`x ↦ x/(1 + x)` squeezes `(0, ∞)` into `(0, 1)`:
* it sends `x ↦ 1/x` to `u ↦ 1 − u` (`odds_inv`);
* it fixes `1 ↦ ½` (`odds_one`);
* it carries the Haar density `dx/x` to `du/(u(1 − u))`, because `d/du log(u/(1 − u)) = 1/(u(1 − u))`
  (`hasDerivAt_log_odds`).
Haar measure makes the squeeze a symmetry; it does not shrink the space, whose total Haar mass stays
infinite. A finite volume needs a discrete quotient.

**Double neutrality** (Codex, comment 6145384891, on Daniel's "total t = 0 just like charge"): for
four orientation populations `N_{q,t}`, `q, t ∈ {±1}`, total charge `Q = 0` and total time-orientation
`T = 0` hold **iff** `N_{++} = N_{−−}` and `N_{+−} = N_{−+}` (`double_neutral_iff`). That is exactly the
`(q,t) ↦ (−q,−t)` pair matching. Yet `Σχ = 2(N_{++} − N_{+−})` need not vanish (`chi_total`). As an RH
control, balanced global counts say nothing about individual unitarity: an off-axis quartet is
balanced too.

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

/-- **The logistic squeeze** (Turbo, relaying Daniel, bridge CONVERSATION.md 2026-10-13): the inverse
of `η` is the logistic map, `s = 1/(1 + e^{−η})` (`logistic_logit`). On the real side, the odds map
`x ↦ x/(1 + x)` squeezes `(0, ∞)` into `(0, 1)`:
* it sends `x ↦ 1/x` to `u ↦ 1 − u` (`odds_inv`);
* it fixes `1 ↦ ½` (`odds_one`);
* it carries the Haar density `dx/x` to `du/(u(1 − u))`, because `d/du log(u/(1 − u)) = 1/(u(1 − u))`
  (`hasDerivAt_log_odds`).
Haar measure makes the squeeze a symmetry; it does not shrink the space, whose total Haar mass stays
infinite. A finite volume needs a discrete quotient.

**Double neutrality**: `Q = 0 ∧ T = 0 ⟺ N₊₊ = N₋₋ ∧ N₊₋ = N₋₊`. -/
theorem double_neutral_iff (npp npm nmp nmm : ℤ) :
    (npp + npm - nmp - nmm = 0 ∧ npp - npm + nmp - nmm = 0) ↔ (npp = nmm ∧ npm = nmp) := by
  constructor
  · rintro ⟨hQ, hT⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; subst h1; subst h2; constructor <;> ring

/-- The relational charge `χ = qt` totals `2(N₊₊ − N₊₋)` under double neutrality. -/
theorem chi_total {npp npm nmp nmm : ℤ} (h1 : npp = nmm) (h2 : npm = nmp) :
    npp - npm - nmp + nmm = 2 * (npp - npm) := by
  subst h1; subst h2; ring

/-- **The inverse of `η` is the logistic map**: `s = 1/(1 + e^{−η})` for `s ∉ {0, 1}`. -/
theorem logistic_logit {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : 1 / (1 + exp (-logit s)) = s := by
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [logit, exp_neg, exp_log (div_ne_zero h0 h1'), inv_div]
  field_simp
  ring

/-- The odds squeeze `x ↦ x/(1 + x)`. -/
noncomputable def odds (x : ℝ) : ℝ := x / (1 + x)

/-- The involution `x ↦ 1/x` becomes `u ↦ 1 − u`. -/
theorem odds_inv {x : ℝ} (hx : 0 < x) : odds x⁻¹ = 1 - odds x := by
  unfold odds; field_simp; ring

theorem odds_one : odds 1 = 1 / 2 := by unfold odds; norm_num

/-- **Haar pushforward**: `d/du log(u/(1 − u)) = 1/(u(1 − u))` on `(0, 1)`, i.e. `dx/x ↦ du/(u(1 − u))`. -/
theorem hasDerivAt_log_odds {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt (fun v => Real.log (v / (1 - v))) (1 / (u * (1 - u))) u := by
  have h1' : (1 : ℝ) - u ≠ 0 := by linarith
  have hq : HasDerivAt (fun v => v / (1 - v)) (1 / (1 - u) ^ 2) u := by
    have := (hasDerivAt_id' u).div ((hasDerivAt_id' u).const_sub 1) h1'
    exact this.congr_deriv (by field_simp; ring)
  have hpos : u / (1 - u) ≠ 0 := div_ne_zero h0.ne' h1'
  exact (hq.log hpos).congr_deriv (by field_simp)

end GppOrientationLogit
