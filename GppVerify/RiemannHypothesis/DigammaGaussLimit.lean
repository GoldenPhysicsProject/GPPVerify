import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Explicit formula, stage E2a (real): Gauss's limit for the digamma function

For real `x > 0`, the logarithmic derivative of `Γ` is

  `ψ(x) = lim_{n → ∞} ( log (x + n) − Σ_{k < n} 1 / (x + k) )`   (`tendsto_digamma_real`).

Proof: the argument Mathlib uses for `Real.deriv_Gamma_nat`, at a general point. With
`f = log ∘ Γ`, the recurrence gives `f'(y + 1) = f'(y) + 1/y`, so
`f'(x + n) = f'(x) + Σ_{k<n} 1/(x+k)`; convexity of `f` (Bohr-Mollerup) squeezes
`log (x + n − 1) ≤ f'(x + n) ≤ log (x + n)`; the gap `log (x+n) − log (x+n−1) → 0`.

This is the real-variable half of stage E2a of the explicit formula (plan: bridge
`MuseResearch/claude-code-note-2026-11-07-explicit-formula-plan.md`). The complex extension
(identity theorem) and the vertical-line bound `ψ(σ + it) = O(log |t|)` (E2b) are not here.
No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

open Real Set Filter Topology

namespace GppDigammaGauss

/-- `S x n = Σ_{k < n} 1/(x + k)`. -/
noncomputable def S (x : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1 / (x + k)

private lemma h_rec {x : ℝ} (hx : 0 < x) :
    (log ∘ Gamma) (x + 1) = (log ∘ Gamma) x + log x := by
  simp only [Function.comp_apply, Gamma_add_one hx.ne',
    log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]

private lemma hder {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ (log ∘ Gamma) x :=
  ((differentiableAt_Gamma (fun m => ne_of_gt (by linarith))).log
    (Gamma_ne_zero (fun m => ne_of_gt (by linarith))))

private lemma hder_rec {x : ℝ} (hx : 0 < x) :
    deriv (log ∘ Gamma) (x + 1) = deriv (log ∘ Gamma) x + 1 / x := by
  rw [← deriv_comp_add_const, one_div, ← deriv_log,
    ← deriv_add (hder hx) (differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy using h_rec hy

private lemma hder_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    deriv (log ∘ Gamma) (x + n) = deriv (log ∘ Gamma) x + S x n := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    have hxn : 0 < x + n := by positivity
    rw [Nat.cast_succ, ← add_assoc, hder_rec hxn, ih, S, S, Finset.sum_range_succ]
    ring

/-- Convexity bounds: `log (y − 1) ≤ f'(y) ≤ log y` for `y > 1`. -/
private lemma deriv_bounds {y : ℝ} (hy : 1 < y) :
    log (y - 1) ≤ deriv (log ∘ Gamma) y ∧ deriv (log ∘ Gamma) y ≤ log y := by
  have hc : ConvexOn ℝ (Ioi 0) (log ∘ Gamma) := convexOn_log_Gamma
  have hy0 : 0 < y := by linarith
  constructor
  · refine (le_of_eq ?_).trans <| hc.slope_le_deriv (mem_Ioi.mpr (by linarith : (0:ℝ) < y - 1))
      (mem_Ioi.mpr hy0) (by linarith : y - 1 < y) (hder hy0)
    have := h_rec (by linarith : (0:ℝ) < y - 1)
    rw [sub_add_cancel] at this
    rw [slope_def_field, show y - (y - 1) = (1 : ℝ) by ring, div_one, this, add_sub_cancel_left]
  · refine (hc.deriv_le_slope hy0 (by linarith : (0:ℝ) < y + 1) (by linarith)
      (hder hy0)).trans (le_of_eq ?_)
    rw [slope_def_field, show y + 1 - y = (1 : ℝ) by ring, div_one, h_rec hy0, add_sub_cancel_left]

/-- **Gauss's limit for the real digamma function.** -/
theorem tendsto_digamma_real {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => log (x + n) - S x n) atTop (𝓝 (deriv (log ∘ Gamma) x)) := by
  set d := deriv (log ∘ Gamma) x
  -- upper: d ≤ a_n ; lower: a_n - (log(x+n) - log(x+n-1)) ≤ d, for n ≥ 2
  have hgap : Tendsto (fun n : ℕ => log (x + n) - log (x + n - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (x + n - 1) / (x + n)) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 - 1 / (x + n)) atTop (𝓝 (1 - 0)) := by
        refine tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop ?_)
        exact tendsto_atTop_add_const_left _ x tendsto_natCast_atTop_atTop
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with n hn
      have : 0 < x + n := by positivity
      field_simp
    have h2 := (continuousAt_log one_ne_zero).tendsto.comp h1
    rw [log_one] at h2
    have h3 := h2.neg
    rw [neg_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply]
    rw [log_div (by linarith) (by positivity)]
    ring
  have hup : ∀ᶠ n : ℕ in atTop, d ≤ log (x + n) - S x n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hb := (deriv_bounds (by linarith : 1 < x + n)).2
    rw [hder_add_nat hx n] at hb
    linarith
  have hlo : ∀ᶠ n : ℕ in atTop,
      log (x + n) - S x n - (log (x + n) - log (x + n - 1)) ≤ d := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hb := (deriv_bounds (by linarith : 1 < x + n)).1
    rw [hder_add_nat hx n] at hb
    linarith
  -- squeeze: d ≤ a_n ≤ d + gap_n
  have hupper : Tendsto (fun n : ℕ => d + (log (x + n) - log (x + n - 1))) atTop (𝓝 d) := by
    simpa using tendsto_const_nhds.add hgap
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hup ?_
  filter_upwards [hlo] with n hn
  linarith

end GppDigammaGauss

#print axioms GppDigammaGauss.tendsto_digamma_real
