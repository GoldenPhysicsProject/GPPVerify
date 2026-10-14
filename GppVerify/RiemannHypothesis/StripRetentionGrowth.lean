import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.Basic

/-!
# Hardy-strip zero retention and the universal scale-growth lower bound

Source: Codex, GPPDiscovery2 `research/2026-09-29_hardy_strip_e_map_zero_retention.md` §§3, 5, 6.

* `retained`: a zero `ρ = σ + iγ` with `0 < σ < 1` has centered coordinate `|σ − ½| < ½`, so it is
  a bounded evaluation on the one width-`½` strip space (§3).
* `eval_norm_eq`: `(1/4) sec(π(σ − ½)) = 1/(4 sin πσ)`, the exact evaluation norm² (§3).
* `weight_ratio_le`: `cosh(2a(ξ + t)) ≤ e^{2a|t|} cosh(2aξ)`. The scale action `e^{itz}`
  (a Fourier shift) has `‖V_t‖ ≤ e^{a|t|}` on the strip space (§5; sharpness is not formalized).
* `growth_lower_bound`: in any normed realization, a nonzero bounded functional `ℓ` with
  `ℓ ∘ V = c ℓ` forces `‖c‖ ≤ ‖V‖` (§6).
* `exponent_bound`: if the two-sided characters `e^{±(½ − β)t}` are `≤ C e^{ωt}` for all `t ≥ 0`, then
  `|β − ½| ≤ ω`. A subexponential scale action would force `β = ½`, but proving that bound for the
  arithmetic quotient is the open, RH-strength step (§7). Not formalized: the reproducing kernel
  `sech` formula (§2) and the E-map quotient (§4, needs the Mellin identity on a test domain).

**No RH claim.**
-/

namespace GppStripRetentionGrowth

open Real

theorem retained {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : |σ - 1 / 2| < 1 / 2 := by
  rw [abs_lt]; constructor <;> linarith

/-- **Exact evaluation norm²** on the width-`½` strip. -/
theorem eval_norm_eq (σ : ℝ) : 1 / 4 / cos (π * (σ - 1 / 2)) = 1 / (4 * sin (π * σ)) := by
  rw [show π * (σ - 1 / 2) = π * σ - π / 2 by ring, cos_sub_pi_div_two]
  ring

/-- **Strip weight ratio**: translation by `t` costs at most `e^{2a|t|}`. -/
theorem weight_ratio_le {a : ℝ} (ha : 0 ≤ a) (ξ t : ℝ) :
    cosh (2 * a * (ξ + t)) ≤ exp (2 * a * |t|) * cosh (2 * a * ξ) := by
  set x := 2 * a * ξ
  set y := 2 * a * t
  have hy : 2 * a * |t| = |y| := by
    simp only [y, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a)]
  rw [show 2 * a * (ξ + t) = x + y by ring, hy, cosh_add]
  have hsx : |sinh x| ≤ cosh x := by
    rw [← abs_of_pos (cosh_pos x)]
    exact sq_le_sq.mp (by nlinarith [cosh_sq x])
  have hsy : sinh x * sinh y ≤ cosh x * |sinh y| := by
    calc sinh x * sinh y ≤ |sinh x * sinh y| := le_abs_self _
      _ = |sinh x| * |sinh y| := abs_mul _ _
      _ ≤ cosh x * |sinh y| := mul_le_mul_of_nonneg_right hsx (abs_nonneg _)
  have he : cosh y + |sinh y| = exp |y| := by
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (sinh_nonneg_iff.mpr h), cosh_add_sinh]
    · rw [abs_of_nonpos h, abs_of_nonpos (sinh_nonpos_iff.mpr h), ← cosh_neg, ← sinh_neg,
        cosh_add_sinh]
  nlinarith [cosh_pos x]

/-- **Universal growth lower bound**: an eigen-functional pins the operator norm from below. -/
theorem growth_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) (V : E →L[ℂ] E) (c : ℂ) (h : ℓ.comp V = c • ℓ) :
    ‖c‖ ≤ ‖V‖ := by
  have hn : 0 < ‖ℓ‖ := lt_of_le_of_ne (norm_nonneg _)
    (fun h0 => hℓ (ContinuousLinearMap.opNorm_zero_iff ℓ |>.mp h0.symm))
  have h1 : ‖c‖ * ‖ℓ‖ ≤ ‖ℓ‖ * ‖V‖ := by
    calc ‖c‖ * ‖ℓ‖ = ‖c • ℓ‖ := (norm_smul c ℓ).symm
      _ = ‖ℓ.comp V‖ := by rw [h]
      _ ≤ ‖ℓ‖ * ‖V‖ := ContinuousLinearMap.opNorm_comp_le ℓ V
  nlinarith

/-- **Growth exponent bound**: two-sided `C e^{ωt}` control forces `|β − ½| ≤ ω`. -/
theorem exponent_bound {β ω C : ℝ}
    (hp : ∀ t : ℝ, 0 ≤ t → exp ((1 / 2 - β) * t) ≤ C * exp (ω * t))
    (hm : ∀ t : ℝ, 0 ≤ t → exp ((β - 1 / 2) * t) ≤ C * exp (ω * t)) :
    |β - 1 / 2| ≤ ω := by
  by_contra hlt
  push Not at hlt
  set d := |β - 1 / 2| - ω with hd
  have hdpos : 0 < d := by linarith
  have key : ∀ t : ℝ, 0 ≤ t → exp (d * t) ≤ C := by
    intro t ht
    have hsel : exp (|β - 1 / 2| * t) ≤ C * exp (ω * t) := by
      rcases abs_choice (β - 1 / 2) with h | h <;> rw [h]
      · exact hm t ht
      · rw [show -(β - 1 / 2) = 1 / 2 - β by ring]; exact hp t ht
    have : exp (d * t) * exp (ω * t) = exp (|β - 1 / 2| * t) := by
      rw [← exp_add]; congr 1; rw [hd]; ring
    have hpos := exp_pos (ω * t)
    nlinarith
  have hC : 1 ≤ C := by simpa using key 0 le_rfl
  have := key (C / d) (by positivity)
  have hlin : d * (C / d) + 1 ≤ exp (d * (C / d)) := add_one_le_exp _
  rw [mul_div_cancel₀ _ hdpos.ne'] at hlin this
  linarith

end GppStripRetentionGrowth
