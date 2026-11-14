/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import GppVerify.Upstream.LogSubLogBound

/-!
# Gauss's series for the digamma function, and a lower bound on vertical lines

## Main results

* `Real.tendsto_log_add_sub_sum_inv`: Gauss's limit. For `x > 0`,
  `log (x + n) - ∑_{k < n} 1 / (x + k) → (log ∘ Γ)' x`.
* `Complex.hasSum_digamma`: Gauss's series. For `s ∉ {0, -1, -2, …}`,
  `∑_{n ≥ 0} (1 / (n + 1) - 1 / (n + 1 + s)) = ψ(s) + γ + 1 / s`.
* `Complex.digamma_eq_tsum`: the same identity, solved for `ψ(s)`.
* `Complex.log_sub_le_re_digamma`: for `0 ≤ a` and `1/2 ≤ b`,
  `log b - (a + 1/4) / b² ≤ Re ψ(a + b i)`.

## Proof outline

The series converges absolutely off the poles, with terms `O(1/n²)`. On the positive reals its
value is identified with `ψ` through Gauss's limit, which follows from the convexity of
`log ∘ Γ` (Bohr–Mollerup), as in Mathlib's proof of `Real.deriv_Gamma_nat`. Both sides are
analytic on `ℂ ∖ ℤ`, which is connected, so the identity theorem extends the identity off the
real axis. Positive integers are covered by the real case.

The vertical bound follows from the real part of the series. With `φ(x) = x / (x² + b²)`, each
term `1/(n+1) - φ(n+1+a)` is bounded below by a telescoping difference, using the sharp
logarithm bound `Real.two_mul_sub_div_add_le_log_sub_log`. Summing, and using
`harmonic N - log N → γ`, gives the bound.

## TODO

Mathlib's `Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean` lists Gauss's representation
as a `TODO`; this file supplies it.
-/

open Filter Topology Set Finset

/-! ### Gauss's limit on the positive reals -/

namespace Real

private lemma log_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    (log ∘ Gamma) (x + 1) = (log ∘ Gamma) x + log x := by
  simp only [Function.comp_apply, Gamma_add_one hx.ne',
    log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]

private lemma differentiableAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (log ∘ Gamma) x :=
  ((differentiableAt_Gamma (fun _ => ne_of_gt (by linarith))).log
    (Gamma_ne_zero (fun _ => ne_of_gt (by linarith))))

private lemma deriv_log_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    deriv (log ∘ Gamma) (x + 1) = deriv (log ∘ Gamma) x + 1 / x := by
  rw [← deriv_comp_add_const, one_div, ← deriv_log,
    ← deriv_add (differentiableAt_log_Gamma hx) (differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy using log_Gamma_add_one hy

private lemma deriv_log_Gamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    deriv (log ∘ Gamma) (x + n) =
      deriv (log ∘ Gamma) x + ∑ k ∈ Finset.range n, 1 / (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x + n := by positivity
    rw [Nat.cast_succ, ← add_assoc, deriv_log_Gamma_add_one hxn, ih, Finset.sum_range_succ]
    ring

/-- Convexity bounds: `log (y - 1) ≤ (log ∘ Γ)' y ≤ log y` for `y > 1`. -/
private lemma deriv_log_Gamma_bounds {y : ℝ} (hy : 1 < y) :
    log (y - 1) ≤ deriv (log ∘ Gamma) y ∧ deriv (log ∘ Gamma) y ≤ log y := by
  have hc : ConvexOn ℝ (Ioi 0) (log ∘ Gamma) := convexOn_log_Gamma
  have hy0 : 0 < y := by linarith
  constructor
  · refine (le_of_eq ?_).trans <| hc.slope_le_deriv (mem_Ioi.mpr (by linarith : (0:ℝ) < y - 1))
      (mem_Ioi.mpr hy0) (by linarith : y - 1 < y) (differentiableAt_log_Gamma hy0)
    have := log_Gamma_add_one (by linarith : (0:ℝ) < y - 1)
    rw [sub_add_cancel] at this
    rw [slope_def_field, show y - (y - 1) = (1 : ℝ) by ring, div_one, this, add_sub_cancel_left]
  · refine (hc.deriv_le_slope hy0 (by linarith : (0:ℝ) < y + 1) (by linarith)
      (differentiableAt_log_Gamma hy0)).trans (le_of_eq ?_)
    rw [slope_def_field, show y + 1 - y = (1 : ℝ) by ring, div_one, log_Gamma_add_one hy0,
      add_sub_cancel_left]

/-- **Gauss's limit for the real digamma function.** For `x > 0`,
`log (x + n) - ∑_{k < n} 1 / (x + k) → (log ∘ Γ)' x`. -/
theorem tendsto_log_add_sub_sum_inv {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => log (x + n) - ∑ k ∈ Finset.range n, 1 / (x + k)) atTop
      (𝓝 (deriv (log ∘ Gamma) x)) := by
  set d := deriv (log ∘ Gamma) x
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
  have hup : ∀ᶠ n : ℕ in atTop, d ≤ log (x + n) - ∑ k ∈ Finset.range n, 1 / (x + k) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hb := (deriv_log_Gamma_bounds (by linarith : 1 < x + n)).2
    rw [deriv_log_Gamma_add_nat hx n] at hb
    linarith
  have hlo : ∀ᶠ n : ℕ in atTop,
      log (x + n) - ∑ k ∈ Finset.range n, 1 / (x + k) - (log (x + n) - log (x + n - 1)) ≤ d := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hb := (deriv_log_Gamma_bounds (by linarith : 1 < x + n)).1
    rw [deriv_log_Gamma_add_nat hx n] at hb
    linarith
  have hupper : Tendsto (fun n : ℕ => d + (log (x + n) - log (x + n - 1))) atTop (𝓝 d) := by
    simpa using tendsto_const_nhds.add hgap
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hup ?_
  filter_upwards [hlo] with n hn
  linarith

end Real

/-! ### The series -/

namespace Complex

namespace DigammaGauss

/-- The `n`-th term of Gauss's series, `1 / (n + 1) - 1 / (n + 1 + s)`. -/
noncomputable def term (s : ℂ) (n : ℕ) : ℂ := ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + 1 + s)⁻¹

/-- The full right-hand side `-γ - 1/s + ∑ term s n`. -/
noncomputable def series (s : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) - s⁻¹ + ∑' n : ℕ, term s n

lemma natCast_add_one_ne_zero (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h]
  exact_mod_cast Nat.succ_ne_zero n

lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h, _root_.norm_natCast]
  push_cast
  ring

lemma term_eq {s : ℂ} {n : ℕ} (h : (n : ℂ) + 1 + s ≠ 0) :
    term s n = s / (((n : ℂ) + 1) * ((n : ℂ) + 1 + s)) := by
  have hn : ((n : ℂ) + 1) ≠ 0 := natCast_add_one_ne_zero n
  simp only [term]
  field_simp
  ring

lemma norm_lower {R : ℝ} {w : ℂ} {k : ℕ} (hw : ‖w‖ ≤ R) (hk : 2 * R ≤ k) :
    ((k : ℝ) + 1) / 2 ≤ ‖(k : ℂ) + 1 + w‖ := by
  have h : ‖(k : ℂ) + 1‖ ≤ ‖(k : ℂ) + 1 + w‖ + ‖w‖ := by
    simpa using norm_sub_le ((k : ℂ) + 1 + w) w
  rw [norm_natCast_add_one] at h
  linarith

lemma ne_zero_of_norm_le {R : ℝ} {w : ℂ} {k : ℕ} (hw : ‖w‖ ≤ R) (hk : 2 * R ≤ k) :
    (k : ℂ) + 1 + w ≠ 0 := by
  have hl := norm_lower hw hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  intro h
  rw [h, norm_zero] at hl
  linarith

lemma norm_term_le {R : ℝ} {w : ℂ} {k : ℕ} (hw : ‖w‖ ≤ R) (hk : 2 * R ≤ k) :
    ‖term w k‖ ≤ 2 * R / ((k : ℝ) + 1) ^ 2 := by
  have hl := norm_lower hw hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hw
  have hpos : 0 < ‖(k : ℂ) + 1 + w‖ := by linarith
  rw [term_eq (ne_zero_of_norm_le hw hk), norm_div, norm_mul, norm_natCast_add_one,
    div_le_div_iff₀ (mul_pos hk1 hpos) (by positivity)]
  have h1 : 2 * R * (((k : ℝ) + 1) * (((k : ℝ) + 1) / 2))
      ≤ 2 * R * (((k : ℝ) + 1) * ‖(k : ℂ) + 1 + w‖) := by gcongr
  have h2 : ‖w‖ * ((k : ℝ) + 1) ^ 2 ≤ R * ((k : ℝ) + 1) ^ 2 := by gcongr
  have h3 : 2 * R * (((k : ℝ) + 1) * (((k : ℝ) + 1) / 2)) = R * ((k : ℝ) + 1) ^ 2 := by ring
  linarith

lemma summable_one_div_add_one_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
  simpa using h

/-- The series converges absolutely for every `s` (at a pole, Lean's `0⁻¹ = 0` makes the
offending term finite). -/
lemma summable_term (s : ℂ) : Summable (term s) := by
  refine Summable.of_norm_bounded_eventually_nat
    (summable_one_div_add_one_sq.mul_left (2 * ‖s‖)) ?_
  filter_upwards [eventually_ge_atTop (⌈2 * ‖s‖⌉₊)] with n hn
  have hbig : 2 * ‖s‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  refine (norm_term_le le_rfl hbig).trans (le_of_eq ?_)
  ring

/-! #### The integer complement -/

lemma isOpen_integerComplement : IsOpen integerComplement := by
  have h : Set.range ((↑) : ℤ → ℂ) = ofReal '' Set.range ((↑) : ℤ → ℝ) := by
    ext z
    simp
  unfold integerComplement
  rw [isOpen_compl_iff, h]
  exact isometry_ofReal.isClosedEmbedding.isClosedMap _
    Int.isClosedEmbedding_coe_real.isClosed_range

lemma isPreconnected_integerComplement : IsPreconnected integerComplement :=
  (Set.Countable.isPathConnected_compl_of_one_lt_rank
    (rank_real_complex ▸ Nat.one_lt_ofNat) (Set.countable_range _)).isConnected.isPreconnected

lemma ne_neg_nat_of_mem {z : ℂ} (hz : z ∈ integerComplement) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro h
  exact hz ⟨-(m : ℤ), by push_cast; exact h.symm⟩

lemma add_ne_zero_of_mem {z : ℂ} (hz : z ∈ integerComplement) (n : ℕ) :
    (n : ℂ) + 1 + z ≠ 0 := by
  intro h
  exact hz ⟨-((n : ℤ) + 1), by push_cast; linear_combination -h⟩

/-! #### Analyticity -/

lemma analyticAt_Gamma_of_mem {z : ℂ} (hz : z ∈ integerComplement) : AnalyticAt ℂ Gamma z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_integerComplement.mem_nhds hz] with w hw
  exact differentiableAt_Gamma w (ne_neg_nat_of_mem hw)

lemma analyticAt_digamma_of_mem {z : ℂ} (hz : z ∈ integerComplement) :
    AnalyticAt ℂ digamma z := by
  have h : digamma = fun w => deriv Gamma w / Gamma w := by
    funext w
    rw [digamma_def, logDeriv_apply]
  rw [h]
  exact (analyticAt_Gamma_of_mem hz).deriv.div (analyticAt_Gamma_of_mem hz)
    (Gamma_ne_zero (ne_neg_nat_of_mem hz))

lemma differentiableAt_series {z : ℂ} (hz : z ∈ integerComplement) :
    DifferentiableAt ℂ series z := by
  set R : ℝ := ‖z‖ + 1 with hRdef
  set N : ℕ := ⌈2 * R⌉₊ with hNdef
  have hN : 2 * R ≤ (N : ℝ) := Nat.le_ceil _
  have hR : 0 ≤ R := by positivity
  have hball : ∀ w ∈ Metric.ball z 1, ‖w‖ ≤ R := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := norm_sub_norm_le w z
    linarith
  have hk : ∀ n : ℕ, 2 * R ≤ ((n + N : ℕ) : ℝ) := by
    intro n
    push_cast
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hu := summable_one_div_add_one_sq.mul_left (2 * R)
  have hle : ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball z 1 →
      ‖term w (n + N)‖ ≤ 2 * R * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n w hw
    refine (norm_term_le (hball w hw) (hk n)).trans ?_
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (n : ℝ) ≤ ((n + N : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    gcongr
  have hdiffterm : ∀ (k : ℕ) (w : ℂ), (k : ℂ) + 1 + w ≠ 0 →
      DifferentiableAt ℂ (fun w => term w k) w := by
    intro k w hne
    unfold term
    exact (differentiableAt_const _).sub ((differentiableAt_const _).add differentiableAt_id
      |>.inv hne)
  have hT : DifferentiableOn ℂ (fun w => ∑' n : ℕ, term w (n + N)) (Metric.ball z 1) := by
    refine differentiableOn_tsum_of_summable_norm hu (fun n w hw => ?_) Metric.isOpen_ball hle
    exact (hdiffterm _ w (ne_zero_of_norm_le (hball w hw) (hk n))).differentiableWithinAt
  have hz0 : z ≠ 0 := by simpa using ne_neg_nat_of_mem hz 0
  set G : ℂ → ℂ := fun w => -(Real.eulerMascheroniConstant : ℂ) - w⁻¹
    + ((∑ n ∈ Finset.range N, term w n) + ∑' n : ℕ, term w (n + N)) with hG
  have hGd : DifferentiableAt ℂ G z := by
    refine ((differentiableAt_const _).sub (differentiableAt_id.inv hz0)).add
      ((DifferentiableAt.fun_sum fun n _ => hdiffterm n z (add_ne_zero_of_mem hz n)).add
        (hT.differentiableAt (Metric.ball_mem_nhds z one_pos)))
  refine hGd.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds z one_pos] with w hw
  have htail : Summable (fun n : ℕ => term w (n + N)) :=
    Summable.of_norm_bounded hu (fun n => hle n w hw)
  have hsum : Summable (term w) := (summable_nat_add_iff N).mp htail
  simp only [hG, series]
  rw [hsum.sum_add_tsum_nat_add N]

lemma analyticAt_series {z : ℂ} (hz : z ∈ integerComplement) : AnalyticAt ℂ series z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_integerComplement.mem_nhds hz] with w hw
  exact differentiableAt_series hw

/-! #### The real axis -/

lemma ne_neg_nat_real {x : ℝ} (hx : 0 < x) (m : ℕ) : x ≠ -(m : ℝ) := by
  intro h
  rw [h] at hx
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- At a positive real point, `ψ` is the derivative of `log ∘ Γ`. -/
lemma digamma_ofReal_of_pos {x : ℝ} (hx : 0 < x) :
    digamma (x : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  have hcx : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m h
    exact ne_neg_nat_real hx m (by exact_mod_cast h)
  have hf : DifferentiableAt ℂ Gamma (x : ℂ) := differentiableAt_Gamma _ hcx
  have hg : HasDerivAt Real.Gamma (deriv Real.Gamma x) x :=
    (Real.differentiableAt_Gamma (ne_neg_nat_real hx)).hasDerivAt
  have hfg : ∀ s : ℝ, Gamma (s : ℂ) = ((Real.Gamma s : ℝ) : ℂ) := fun s => Gamma_ofReal s
  have hderiv : HasDerivAt Gamma ((deriv Real.Gamma x : ℝ) : ℂ) (x : ℂ) := by
    refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
    rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
    exact hg.ofReal_comp.deriv
  have hGne : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hlog : deriv (Real.log ∘ Real.Gamma) x = deriv Real.Gamma x / Real.Gamma x :=
    (hg.log hGne).deriv
  rw [digamma_def, logDeriv_apply, hderiv.deriv, hfg, hlog]
  push_cast
  rfl

/-- The real terms `1/(n+1) − 1/(n+1+x)`. -/
noncomputable def realTerm (x : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 1 + x)⁻¹

lemma realTerm_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 ≤ realTerm x n := by
  unfold realTerm
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [sub_nonneg]
  exact inv_anti₀ h1 (by linarith)

lemma sum_realTerm {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ Finset.range N, realTerm x n
      = (harmonic N : ℝ) - ∑ k ∈ Finset.range (N + 1), 1 / (x + k) + x⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ, Finset.sum_range_succ (n := N + 1)]
    unfold realTerm
    push_cast
    have h1 : x + ((N : ℝ) + 1) ≠ 0 := by positivity
    rw [one_div]
    ring_nf

lemma hasSum_realTerm {x : ℝ} (hx : 0 < x) :
    HasSum (realTerm x)
      (deriv (Real.log ∘ Real.Gamma) x + Real.eulerMascheroniConstant + x⁻¹) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (realTerm_nonneg hx)]
  have T1 := Real.tendsto_harmonic_sub_log_add_one
  have T2 : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log (x + ((N + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_log_comp_add_sub_log x).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    have h' := h.neg
    rw [neg_zero] at h'
    refine h'.congr (fun N => ?_)
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  have T3 := (Real.tendsto_log_add_sub_sum_inv hx).comp (tendsto_add_atTop_nat 1)
  have hsum := ((T1.add T2).add T3).add (tendsto_const_nhds (x := x⁻¹))
  rw [add_zero, show Real.eulerMascheroniConstant + deriv (Real.log ∘ Real.Gamma) x + x⁻¹
    = deriv (Real.log ∘ Real.Gamma) x + Real.eulerMascheroniConstant + x⁻¹ by ring] at hsum
  refine hsum.congr (fun N => ?_)
  rw [sum_realTerm hx N]
  simp only [Function.comp_apply]
  ring

lemma series_ofReal {x : ℝ} (hx : 0 < x) : series (x : ℂ) = digamma (x : ℂ) := by
  have h : HasSum (term (x : ℂ))
      (((deriv (Real.log ∘ Real.Gamma) x + Real.eulerMascheroniConstant + x⁻¹ : ℝ)) : ℂ) := by
    have h0 := hasSum_ofReal.mpr (hasSum_realTerm hx)
    refine h0.congr_fun (fun n => ?_)
    simp [term, realTerm]
  rw [series, h.tsum_eq, digamma_ofReal_of_pos hx]
  push_cast
  ring

/-! #### The identity -/

lemma half_mem_integerComplement : ((1 / 2 : ℝ) : ℂ) ∈ integerComplement := by
  rintro ⟨n, hn⟩
  have h : ((n : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by exact_mod_cast hn
  have h2 : (n : ℝ) * 2 = 1 := by
    have := ofReal_injective h
    rw [this]; norm_num
  have h3 : n * 2 = 1 := by exact_mod_cast h2
  omega

lemma eqOn_integerComplement : EqOn series digamma integerComplement := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (fun z hz => analyticAt_series hz) (fun z hz => analyticAt_digamma_of_mem hz)
    isPreconnected_integerComplement half_mem_integerComplement ?_
  have hreal : ∀ᶠ x : ℝ in 𝓝[≠] (1 / 2 : ℝ), series (x : ℂ) = digamma (x : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with x hx
    exact series_ofReal hx
  have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 / 2 : ℝ)) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact fun h => hx (ofReal_injective h)
  exact htend.frequently hreal.frequently

lemma series_eq_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) : series s = digamma s := by
  by_cases hmem : s ∈ integerComplement
  · exact eqOn_integerComplement hmem
  · have hmem' : ∃ n : ℤ, (n : ℂ) = s := by
      simpa [integerComplement] using hmem
    obtain ⟨n, hn⟩ := hmem'
    rcases lt_or_ge 0 n with hpos | hneg
    · have hs' : s = ((n : ℝ) : ℂ) := by rw [← hn]; push_cast; rfl
      rw [hs']
      exact series_ofReal (by exact_mod_cast hpos)
    · exfalso
      apply hs (-n).toNat
      have h1 : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      have h2 : (((-n).toNat : ℕ) : ℂ) = ((-n : ℤ) : ℂ) := by exact_mod_cast h1
      rw [← hn, h2]
      push_cast
      ring

end DigammaGauss

open DigammaGauss in
/-- **Gauss's series for the digamma function.** For `s ∉ {0, -1, -2, …}`,
`∑_{n ≥ 0} (1 / (n + 1) - 1 / (n + 1 + s)) = ψ(s) + γ + 1 / s`. -/
theorem hasSum_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s))
      (digamma s + Real.eulerMascheroniConstant + 1 / s) := by
  have hsum := summable_term s
  have h := series_eq_digamma hs
  rw [series] at h
  have heq : (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s)) = term s := by
    funext n; simp [term]
  rw [heq, ← h, one_div]
  convert hsum.hasSum using 1
  ring

/-- **Gauss's series, solved for `ψ`.** For `s ∉ {0, -1, -2, …}`,
`ψ(s) = -γ - 1/s + ∑_{n ≥ 0} (1 / (n + 1) - 1 / (n + 1 + s))`. -/
theorem digamma_eq_tsum {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = -Real.eulerMascheroniConstant - 1 / s +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + s)) := by
  rw [(hasSum_digamma hs).tsum_eq]
  ring

/-! ### A lower bound for `Re ψ` on vertical lines -/

namespace DigammaGauss

/-- `φ_b(x) = x / (x² + b²)`, the real part of `1 / (x + b i)`. -/
noncomputable def phi (b x : ℝ) : ℝ := x / (x ^ 2 + b ^ 2)

/-- `F_b(y) = log (y² + b²) / 2`, an antiderivative of `φ_b`. -/
noncomputable def logPot (b y : ℝ) : ℝ := Real.log (y ^ 2 + b ^ 2) / 2

/-- `H_b(y) = 1 / (y² + b²)`. -/
noncomputable def invQuad (b y : ℝ) : ℝ := 1 / (y ^ 2 + b ^ 2)

/-- Per-term telescoping bound: for `x > 0` and `b² ≥ 1/4`,
`φ(x) ≤ F(x + 1/2) - F(x - 1/2) + (H(x - 1/2) - H(x + 1/2)) / 4`. -/
lemma phi_le (b x : ℝ) (hx : 0 < x) (hb : 1 / 4 ≤ b ^ 2) :
    phi b x ≤ (logPot b (x + 1 / 2) - logPot b (x - 1 / 2))
      + (invQuad b (x - 1 / 2) - invQuad b (x + 1 / 2)) / 4 := by
  unfold phi logPot invQuad
  set A : ℝ := (x + 1 / 2) ^ 2 + b ^ 2 with hA
  set B : ℝ := (x - 1 / 2) ^ 2 + b ^ 2 with hB
  set P : ℝ := x ^ 2 + b ^ 2 with hP
  have hP0 : 1 / 4 ≤ P := by nlinarith
  have hB0 : 0 < B := by positivity
  have hA0 : 0 < A := by positivity
  have hBA : B < A := by rw [hA, hB]; nlinarith
  have hlog := Real.two_mul_sub_div_add_le_log_sub_log hB0 hBA
  have hsumAB : A + B = 2 * (P + 1 / 4) := by rw [hA, hB, hP]; ring
  have hdiffAB : A - B = 2 * x := by rw [hA, hB]; ring
  have hlog' : x / (P + 1 / 4) ≤ (Real.log A - Real.log B) / 2 := by
    have : 2 * (A - B) / (A + B) = 2 * (x / (P + 1 / 4)) := by
      rw [hsumAB, hdiffAB]; field_simp
    linarith
  have halg : x / P ≤ x / (P + 1 / 4) + (1 / B - 1 / A) / 4 := by
    have hPpos : 0 < P := by linarith
    have hP4 : 0 < P + 1 / 4 := by linarith
    have e1 : x / P - x / (P + 1 / 4) = x / (4 * P * (P + 1 / 4)) := by
      field_simp; ring
    have e2 : (1 / B - 1 / A) / 4 = x / (2 * (A * B)) := by
      field_simp; rw [hA, hB]; ring
    have hABpos : 0 < A * B := mul_pos hA0 hB0
    have hle : 2 * (A * B) ≤ 4 * P * (P + 1 / 4) := by nlinarith
    have : x / (4 * P * (P + 1 / 4)) ≤ x / (2 * (A * B)) :=
      div_le_div_of_nonneg_left hx.le (by positivity) hle
    linarith
  linarith

lemma re_term (a b : ℝ) (n : ℕ) :
    (term ⟨a, b⟩ n).re = 1 / ((n : ℝ) + 1) - phi b ((n : ℝ) + 1 + a) := by
  have h1 : (((n : ℂ) + 1)⁻¹).re = 1 / ((n : ℝ) + 1) := by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← ofReal_inv, ofReal_re, one_div]
  have h2 : (((n : ℂ) + 1 + ⟨a, b⟩)⁻¹).re = phi b ((n : ℝ) + 1 + a) := by
    rw [inv_re, normSq_apply]
    simp [phi]
    ring
  simp only [term, sub_re, h1, h2]

lemma sum_phi_le (a b : ℝ) (ha : 0 ≤ a) (hb : 1 / 4 ≤ b ^ 2) (N : ℕ) :
    ∑ k ∈ range N, phi b ((k : ℝ) + 1 + a)
      ≤ logPot b ((N : ℝ) + a + 1 / 2) - logPot b (a + 1 / 2) + invQuad b (a + 1 / 2) / 4 := by
  set g : ℕ → ℝ := fun k =>
    logPot b ((k : ℝ) + a + 1 / 2) - invQuad b ((k : ℝ) + a + 1 / 2) / 4 with hg
  have hstep : ∀ k ∈ range N, phi b ((k : ℝ) + 1 + a) ≤ g (k + 1) - g k := by
    intro k _
    have hx : 0 < (k : ℝ) + 1 + a := by positivity
    have := phi_le b ((k : ℝ) + 1 + a) hx hb
    simp only [hg]
    push_cast
    have e2 : (k : ℝ) + 1 + a - 1 / 2 = (k : ℝ) + a + 1 / 2 := by ring
    rw [e2] at this
    linarith
  have htel := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub] at htel
  have hH : 0 ≤ invQuad b ((N : ℝ) + a + 1 / 2) := by unfold invQuad; positivity
  simp only [hg, Nat.cast_zero, zero_add] at htel
  linarith

lemma tendsto_logPot_sub_log (b c : ℝ) :
    Tendsto (fun N : ℕ => logPot b ((N : ℝ) + c) - Real.log N) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hq : Tendsto (fun N : ℕ => (1 + c * ((N : ℝ))⁻¹) ^ 2 + b ^ 2 * (((N : ℝ))⁻¹) ^ 2)
      atTop (𝓝 ((1 + c * 0) ^ 2 + b ^ 2 * 0 ^ 2)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).pow 2).add
      (tendsto_const_nhds.mul (hinv.pow 2))
  simp only [mul_zero, add_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hq
  have hlog : Tendsto (fun N : ℕ => Real.log ((1 + c * ((N : ℝ))⁻¹) ^ 2
      + b ^ 2 * (((N : ℝ))⁻¹) ^ 2) / 2) atTop (𝓝 (Real.log 1 / 2)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto.comp hq).div_const 2
  rw [Real.log_one, zero_div] at hlog
  refine hlog.congr' ?_
  obtain ⟨M, hM⟩ := exists_nat_gt |c|
  filter_upwards [eventually_gt_atTop (max M 0)] with N hN
  have hNM : (M : ℝ) < N := by exact_mod_cast (le_max_left M 0).trans_lt hN
  have hN' : (0 : ℝ) < N := lt_of_le_of_lt (Nat.cast_nonneg M) hNM
  have hNc : 0 < (N : ℝ) + c := by
    have := neg_abs_le c; linarith
  have hpos : 0 < ((N : ℝ) + c) ^ 2 + b ^ 2 := by positivity
  have hq' : (1 + c * ((N : ℝ))⁻¹) ^ 2 + b ^ 2 * (((N : ℝ))⁻¹) ^ 2
      = (((N : ℝ) + c) ^ 2 + b ^ 2) / (N : ℝ) ^ 2 := by
    field_simp
  unfold logPot
  rw [hq', Real.log_div hpos.ne' (by positivity), Real.log_pow]
  push_cast; ring

lemma re_digamma_ge_aux (a b : ℝ) (ha : 0 ≤ a) (hb : 1 / 4 ≤ b ^ 2) :
    -a / (a ^ 2 + b ^ 2) + logPot b (a + 1 / 2) - invQuad b (a + 1 / 2) / 4
      ≤ (digamma ⟨a, b⟩).re := by
  set s : ℂ := ⟨a, b⟩ with hs
  have hb0 : b ≠ 0 := by rintro rfl; norm_num at hb
  have hnp : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.im h
    simp [hs] at this
    exact hb0 this
  rw [← series_eq_digamma hnp]
  have hsumm := summable_term s
  have hre : HasSum (fun n => (term s n).re) (∑' n, term s n).re := hasSum_re hsumm.hasSum
  have hlim := hre.tendsto_sum_nat
  have hlow : ∀ N : ℕ, ((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + (a + 1 / 2))
      + logPot b (a + 1 / 2) - invQuad b (a + 1 / 2) / 4
      ≤ ∑ n ∈ range N, (term s n).re := by
    intro N
    have hbound := sum_phi_le a b ha hb N
    simp only [hs, re_term, Finset.sum_sub_distrib]
    have hharm : ((harmonic N : ℚ) : ℝ) = ∑ n ∈ range N, 1 / ((n : ℝ) + 1) := by
      rw [harmonic]; push_cast; simp
    rw [hharm]
    have : (N : ℝ) + (a + 1 / 2) = (N : ℝ) + a + 1 / 2 := by ring
    rw [this]
    linarith
  have hlowlim : Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + (a + 1 / 2))
      + logPot b (a + 1 / 2) - invQuad b (a + 1 / 2) / 4) atTop
      (𝓝 (Real.eulerMascheroniConstant - 0 + logPot b (a + 1 / 2)
        - invQuad b (a + 1 / 2) / 4)) := by
    have := (Real.tendsto_harmonic_sub_log.sub (tendsto_logPot_sub_log b (a + 1 / 2))).add_const
      (logPot b (a + 1 / 2))
    refine (this.sub_const (invQuad b (a + 1 / 2) / 4)).congr (fun N => ?_)
    ring
  have hle := le_of_tendsto_of_tendsto' hlowlim hlim hlow
  have hre_s : (s⁻¹).re = a / (a ^ 2 + b ^ 2) := by
    rw [inv_re, normSq_apply]; simp [hs]; ring
  have hre_tot : (series s).re
      = -Real.eulerMascheroniConstant - a / (a ^ 2 + b ^ 2) + (∑' n, term s n).re := by
    simp only [series, add_re, sub_re, neg_re, ofReal_re, hre_s]
  rw [hre_tot]
  have : -a / (a ^ 2 + b ^ 2) = -(a / (a ^ 2 + b ^ 2)) := by ring
  rw [this]
  linarith

end DigammaGauss

open DigammaGauss in
/-- **A lower bound for `Re ψ` on vertical lines.** For `0 ≤ a` and `1/2 ≤ b`,
`log b - (a + 1/4) / b² ≤ Re ψ(a + b i)`. -/
theorem log_sub_le_re_digamma {a b : ℝ} (ha : 0 ≤ a) (hb : 1 / 2 ≤ b) :
    Real.log b - (a + 1 / 4) / b ^ 2 ≤ (digamma ⟨a, b⟩).re := by
  have hb0 : 0 < b := by linarith
  have hb2 : 1 / 4 ≤ b ^ 2 := by nlinarith
  refine le_trans ?_ (re_digamma_ge_aux a b ha hb2)
  have hbsq : 0 < b ^ 2 := by positivity
  have hF : Real.log b ≤ logPot b (a + 1 / 2) := by
    unfold logPot
    have : Real.log b = Real.log (b ^ 2) / 2 := by
      rw [Real.log_pow]; push_cast; ring
    rw [this]
    have := Real.log_le_log hbsq (by nlinarith : b ^ 2 ≤ (a + 1 / 2) ^ 2 + b ^ 2)
    linarith
  have h1 : a / (a ^ 2 + b ^ 2) ≤ a / b ^ 2 :=
    div_le_div_of_nonneg_left ha hbsq (by nlinarith)
  have h2 : invQuad b (a + 1 / 2) ≤ 1 / b ^ 2 := by
    unfold invQuad
    exact div_le_div_of_nonneg_left zero_le_one hbsq (by nlinarith)
  have e : (a + 1 / 4) / b ^ 2 = a / b ^ 2 + (1 / b ^ 2) / 4 := by ring
  rw [e]
  have : -a / (a ^ 2 + b ^ 2) = -(a / (a ^ 2 + b ^ 2)) := by ring
  rw [this]
  linarith

end Complex
