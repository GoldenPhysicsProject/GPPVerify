import GppVerify.RiemannHypothesis.StripRetentionGrowth

/-!
# Zero survival: unitary or subexponential scale action forces the principal series

Source: Codex, GPP-bridge `research/codex/2026-09-29_zero_survival_and_scale_growth.md` §§3–5.
§8 (a real Casimir `ρ(1 − ρ)` with `γ ≠ 0` forces `β = ½`) is already `CasimirCriticalLine`.

* `principal_of_contraction`: if a nonzero bounded functional carries the character
  `ℓ ∘ V_t = c_t ℓ` with `‖c_t‖ = e^{(½ − β)t}`, and `‖V_t‖ ≤ 1` for all real `t` (unitary), then
  `β = ½` (§3).
* `principal_of_subexp`: the same holds when the bound is only `‖V_t‖ ≤ C_ε e^{ε|t|}` for every
  `ε > 0` (§4).
* `jordan_unbounded`: if `N v ≠ 0`, then `‖v − t • N v‖` is unbounded in `t`. A repeated zero's jet
  quotient `T = (ρ − ½) + N`, even on the critical line, has polynomially growing scale flow. So
  demanding a *unitary* jet realization would also force simplicity, while the subexponential
  criterion allows it (§5).

The hypotheses (a zero survives as a continuous eigen-functional, plus the growth bound) are exactly
the open arithmetic content. **No RH claim.**
-/

namespace GppZeroSurvivalSubexp

open Real GppStripRetentionGrowth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem principal_of_subexp (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) (V : ℝ → E →L[ℂ] E) (c : ℝ → ℂ) (β : ℝ)
    (hcov : ∀ t, ℓ.comp (V t) = c t • ℓ) (hc : ∀ t, ‖c t‖ = exp ((1 / 2 - β) * t))
    (hgrowth : ∀ ε > 0, ∃ C, ∀ t, ‖V t‖ ≤ C * exp (ε * |t|)) : β = 1 / 2 := by
  have hb : ∀ ε > 0, |β - 1 / 2| ≤ ε := by
    intro ε hε
    obtain ⟨C, hC⟩ := hgrowth ε hε
    have key : ∀ t, exp ((1 / 2 - β) * t) ≤ C * exp (ε * |t|) := fun t =>
      (hc t) ▸ (growth_lower_bound ℓ hℓ (V t) (c t) (hcov t)).trans (hC t)
    refine exponent_bound (C := C) (fun t ht => ?_) (fun t ht => ?_)
    · simpa [abs_of_nonneg ht] using key t
    · have := key (-t)
      rw [abs_neg, abs_of_nonneg ht] at this
      rwa [show (1 / 2 - β) * -t = (β - 1 / 2) * t by ring] at this
  have : |β - 1 / 2| = 0 :=
    le_antisymm (le_of_forall_pos_le_add fun ε hε => by simpa using hb ε hε) (abs_nonneg _)
  linarith [abs_eq_zero.mp this]

/-- **Unitary realization forces the principal series.** -/
theorem principal_of_contraction (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) (V : ℝ → E →L[ℂ] E) (c : ℝ → ℂ)
    (β : ℝ) (hcov : ∀ t, ℓ.comp (V t) = c t • ℓ) (hc : ∀ t, ‖c t‖ = exp ((1 / 2 - β) * t))
    (hV : ∀ t, ‖V t‖ ≤ 1) : β = 1 / 2 :=
  principal_of_subexp ℓ hℓ V c β hcov hc fun ε hε =>
    ⟨1, fun t => (hV t).trans (by simpa using one_le_exp (by positivity : 0 ≤ ε * |t|))⟩

/-- **Jordan growth**: a nonzero nilpotent part makes `v − t N v` unbounded. -/
theorem jordan_unbounded (N : E →L[ℂ] E) (v : E) (hN : N v ≠ 0) (M : ℝ) :
    ∃ t : ℝ, M < ‖v - (t : ℂ) • N v‖ := by
  have hn : 0 < ‖N v‖ := norm_pos_iff.mpr hN
  refine ⟨(|M| + ‖v‖ + 1) / ‖N v‖, ?_⟩
  set t : ℝ := (|M| + ‖v‖ + 1) / ‖N v‖
  have ht : t * ‖N v‖ = |M| + ‖v‖ + 1 := div_mul_cancel₀ _ hn.ne'
  have htn : 0 ≤ t := by positivity
  have h1 : ‖(t : ℂ) • N v‖ = t * ‖N v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg htn]
  have h2 : ‖(t : ℂ) • N v‖ - ‖v‖ ≤ ‖v - (t : ℂ) • N v‖ := by
    have := norm_sub_norm_le ((t : ℂ) • N v) v
    rw [norm_sub_rev] at this; linarith
  have := le_abs_self M
  linarith

end GppZeroSurvivalSubexp
