/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (D3 seat), 2026-11-13, takeover shift for Claude Code's lane.

# Continuity of the translate kernel `Kpsi`

Krein's representation theorem (the primary behind the named premise `KreinDecomp`)
takes a **continuous** Hermitian kernel as its input. This file proves the continuity
of `Kpsi = poleTerm - primeTerm + archTerm` (definitions in `KreinHPsi.lean`) as far
as elementary arguments reach, and isolates the remaining analytic inputs as named
Props with their exact statements.

PROVED here (no hypotheses):
* `continuous_triG` — via the closed form
  `triG y = (max 0 (2 - |y|))^3 / 6 - (2/3) * (max 0 (1 - |y|))^3` (`triG_eq`),
  which also makes the support in `[-2, 2]` and the values at `|y| = 1` manifest.
* `continuous_poleTerm` — `cosh` is continuous.
* `continuous_primeTerm` — the `tsum` is locally finite: on `(-A, A)` it equals the
  finite sum over `n ≤ exp (A + 2)`, since `triG` vanishes off `[-2, 2]`
  (`primeTerm_eq_finite_sum`).

CONDITIONAL (proved modulo the two named Props below): `continuous_archTerm`,
hence `continuous_Kpsi`. The named obligations are exactly:
* `ArchGammaFactorContinuous`: continuity on `(0, ∞)` of the digamma factor
  `t ↦ Re (logDeriv Γ (1/4 + it/2)) - log π`. Expected routine (Γ is analytic and
  nonzero where `Re s = 1/4`), but unproved in-tree.
* `ArchEnvelopeIntegrable`: integrability on `(0, ∞)` of the `d`-independent
  envelope `t ↦ bigPsi t ^ 2 * |Re (logDeriv Γ (1/4 + it/2)) - log π|`. This is
  the analytic content: a growth bound on `Re ψ(1/4 + it/2)` against the `t^{-4}`
  decay of `bigPsi t ^ 2`.

No `sorry` appears in this file; the obligations are hypotheses of the conditional
theorems, stated as Props carrying their exact content.
-/
import GppVerify.RiemannHypothesis.KreinHPsi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace GppKreinKpsiContinuous

open GppKreinHPsi MeasureTheory Set Filter Topology

/-- `triG` vanishes off `[-2, 2]`. -/
theorem triG_eq_zero_of (h : 2 < |y|) : triG y = 0 := by
  unfold triG
  rw [if_neg (by linarith : ¬ |y| ≤ 1), if_neg (not_le.mpr h)]

/-- Closed form of `triG`: a difference of two truncated cubes. The first cube is
`(2 - |y|)^3 / 6` on `[-2, 2]`; the correction `(2/3)(1 - |y|)^3` on `[-1, 1]`
turns it into `2/3 - y^2 + |y|^3 / 2` there. -/
theorem triG_eq (y : ℝ) :
    triG y = (max 0 (2 - |y|)) ^ 3 / 6 - (2 / 3) * (max 0 (1 - |y|)) ^ 3 := by
  unfold triG
  by_cases h1 : |y| ≤ 1
  · rw [if_pos h1]
    have h2 : max 0 (2 - |y|) = 2 - |y| := max_eq_right (by linarith)
    have h3 : max 0 (1 - |y|) = 1 - |y| := max_eq_right (by linarith)
    rw [h2, h3, (sq_abs y).symm]
    ring
  · by_cases h2 : |y| ≤ 2
    · rw [if_neg h1, if_pos h2]
      have h3 : max 0 (2 - |y|) = 2 - |y| := max_eq_right (by linarith)
      have h4 : max 0 (1 - |y|) = 0 := max_eq_left (by linarith)
      rw [h3, h4]
      simp
    · rw [if_neg h1, if_neg h2]
      have h3 : max 0 (2 - |y|) = 0 := max_eq_left (by linarith)
      have h4 : max 0 (1 - |y|) = 0 := max_eq_left (by linarith)
      rw [h3, h4]
      simp

theorem continuous_triG : Continuous triG := by
  have he : triG = fun y => (max 0 (2 - |y|)) ^ 3 / 6 - (2 / 3) * (max 0 (1 - |y|)) ^ 3 :=
    funext triG_eq
  rw [he]
  have h1 : Continuous (fun y : ℝ => max (0 : ℝ) (2 - |y|)) :=
    continuous_const.max (continuous_const.sub continuous_abs)
  have h2 : Continuous (fun y : ℝ => max (0 : ℝ) (1 - |y|)) :=
    continuous_const.max (continuous_const.sub continuous_abs)
  exact ((h1.pow 3).div_const 6).sub (continuous_const.mul (h2.pow 3))

theorem continuous_poleTerm : Continuous poleTerm := by
  unfold poleTerm
  exact continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))

/-- On `(-A, A)` the prime term is a finite sum: terms with `log n ≥ A + 2`
vanish because `triG` is supported in `[-2, 2]`. -/
theorem primeTerm_eq_finite_sum {A : ℝ} {d : ℝ} (hd : d ∈ Set.Ioo (-A) A) :
    primeTerm d =
      ∑ n ∈ Finset.range (⌈Real.exp (A + 2)⌉₊ + 1),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (triG (Real.log n + d) + triG (-Real.log n + d)) := by
  have hdA : |d| < A := abs_lt.mpr hd
  unfold primeTerm
  rw [tsum_eq_sum]
  intro n hn
  have hn : ⌈Real.exp (A + 2)⌉₊ + 1 ≤ n :=
    Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
  have hn1 : 1 ≤ n := by
    have : 0 < ⌈Real.exp (A + 2)⌉₊ + 1 := Nat.succ_pos _
    omega
  have hexp : Real.exp (A + 2) < (n : ℝ) := by
    have h2 : (⌈Real.exp (A + 2)⌉₊ + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h6 : Real.exp (A + 2) ≤ (⌈Real.exp (A + 2)⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlog : A + 2 < Real.log (n : ℝ) := (Real.lt_log_iff_exp_lt hn0).mpr hexp
  have h1 : triG (Real.log (n : ℝ) + d) = 0 := by
    apply triG_eq_zero_of
    have : Real.log (n : ℝ) + d > 2 := by linarith [abs_lt.mp hdA]
    linarith [le_abs_self (Real.log (n : ℝ) + d)]
  have h2 : triG (-Real.log (n : ℝ) + d) = 0 := by
    apply triG_eq_zero_of
    have : -Real.log (n : ℝ) + d < -2 := by linarith [abs_lt.mp hdA]
    have : |(-Real.log (n : ℝ) + d)| = -(-Real.log (n : ℝ) + d) :=
      abs_of_neg (by linarith)
    linarith
  rw [h1, h2, add_zero, mul_zero]

theorem continuous_primeTerm : Continuous primeTerm := by
  rw [continuous_iff_continuousAt]
  intro d₀
  set A := |d₀| + 1 with hAdef
  have hd₀ : d₀ ∈ Set.Ioo (-A) A := by
    rw [Set.mem_Ioo]
    constructor
    · linarith [hAdef, neg_abs_le d₀]
    · linarith [hAdef, le_abs_self d₀]
  have hEq : (primeTerm : ℝ → ℝ) =ᶠ[𝓝 d₀]
      fun d => ∑ n ∈ Finset.range (⌈Real.exp (A + 2)⌉₊ + 1),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (triG (Real.log n + d) + triG (-Real.log n + d)) := by
    apply eventually_of_mem (Ioo_mem_nhds hd₀.1 hd₀.2)
    intro d hd
    exact primeTerm_eq_finite_sum hd
  have hF : ContinuousAt
      (fun d => ∑ n ∈ Finset.range (⌈Real.exp (A + 2)⌉₊ + 1),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (triG (Real.log n + d) + triG (-Real.log n + d))) d₀ := by
    apply Continuous.continuousAt
    apply continuous_finsetSum
    intro n _
    exact continuous_const.mul
      ((continuous_triG.comp (continuous_const.add continuous_id)).add
        (continuous_triG.comp (continuous_const.add continuous_id)))
  have hval : primeTerm d₀ =
      ∑ n ∈ Finset.range (⌈Real.exp (A + 2)⌉₊ + 1),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (triG (Real.log n + d₀) + triG (-Real.log n + d₀)) :=
    primeTerm_eq_finite_sum hd₀
  have htend : Tendsto primeTerm (𝓝 d₀) (𝓝 (primeTerm d₀)) := by
    rw [hval]
    exact Filter.Tendsto.congr' hEq.symm hF
  exact htend

/-- The digamma factor of `archTerm`, as it appears in the definition. -/
noncomputable def archFactor (t : ℝ) : ℝ :=
  (logDeriv Complex.Gamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re - Real.log Real.pi

/-- **Named obligation (OPEN)**: the digamma factor of `archTerm` is continuous
on `(0, ∞)`. -/
def ArchGammaFactorContinuous : Prop :=
  ContinuousOn archFactor (Set.Ioi 0)

/-- **Named obligation (OPEN)**: the `d`-independent envelope of the `archTerm`
integrand is integrable on `(0, ∞)`. -/
def ArchEnvelopeIntegrable : Prop :=
  IntegrableOn (fun t => bigPsi t ^ 2 * |archFactor t|) (Set.Ioi 0) volume

theorem continuousOn_bigPsi : ContinuousOn bigPsi (Set.Ioi 0) := by
  have h : ContinuousOn (fun t => (Real.sin (t / 2) / (t / 2)) ^ 2) (Set.Ioi 0) := by
    apply ContinuousOn.pow
    apply ContinuousOn.div
    · exact (Real.continuous_sin.comp (continuous_id.div_const 2)).continuousOn
    · exact (continuous_id.div_const 2).continuousOn
    · intro t ht
      simp only [Set.mem_Ioi] at ht
      positivity
  apply h.congr
  intro t ht
  simp only [Set.mem_Ioi] at ht
  unfold bigPsi
  rw [if_neg (ne_of_gt ht)]

/-- Continuity of `archTerm`, modulo the two named obligations. The only
`d`-dependence of the integrand is the cosine factor, so dominated convergence
with the envelope of `ArchEnvelopeIntegrable` gives continuity at every point. -/
theorem continuous_archTerm (hC : ArchGammaFactorContinuous)
    (hE : ArchEnvelopeIntegrable) : Continuous archTerm := by
  rw [continuous_iff_continuousAt]
  intro d₀
  have hmeas : ∀ d : ℝ, AEStronglyMeasurable
      (fun t => bigPsi t ^ 2 * Real.cos (t * d) * archFactor t)
      (volume.restrict (Set.Ioi 0)) := by
    intro d
    have h1 : ContinuousOn (fun t => bigPsi t ^ 2 * Real.cos (t * d)) (Set.Ioi 0) :=
      (continuousOn_bigPsi.pow 2).mul
        ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).continuousOn)
    exact (h1.mul hC).aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ d : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      ‖bigPsi t ^ 2 * Real.cos (t * d) * archFactor t‖ ≤ bigPsi t ^ 2 * |archFactor t| := by
    intro d
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hcos : |Real.cos (t * d)| ≤ 1 := Real.abs_cos_le_one _
    have hnn : (0 : ℝ) ≤ |bigPsi t ^ 2| := abs_nonneg _
    calc |bigPsi t ^ 2| * |Real.cos (t * d)| * |archFactor t|
        ≤ |bigPsi t ^ 2| * 1 * |archFactor t| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hcos hnn
      _ = bigPsi t ^ 2 * |archFactor t| := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ bigPsi t ^ 2)]; ring
  have hlim : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun d => bigPsi t ^ 2 * Real.cos (t * d) * archFactor t)
        (𝓝 d₀) (𝓝 (bigPsi t ^ 2 * Real.cos (t * d₀) * archFactor t)) := by
    apply Filter.Eventually.of_forall
    intro t
    have hc : ContinuousAt (fun d => Real.cos (t * d)) d₀ :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt
    exact ((continuousAt_const (x := d₀)).mul hc).mul continuousAt_const
  have h := tendsto_integral_filter_of_dominated_convergence
    (bound := fun t => bigPsi t ^ 2 * |archFactor t|)
    (μ := volume.restrict (Set.Ioi 0))
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound) hE hlim
  have harch : ContinuousAt (fun d => ∫ t in Set.Ioi (0 : ℝ),
      bigPsi t ^ 2 * Real.cos (t * d) * archFactor t) d₀ := h
  have heq : archTerm = fun d => (1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ),
      bigPsi t ^ 2 * Real.cos (t * d) * archFactor t := by
    funext d
    rfl
  rw [heq]
  exact (continuousAt_const.mul harch)

/-- Continuity of `Kpsi`, modulo the two named archimedean obligations.
The pole and prime terms are continuous unconditionally. -/
theorem continuous_Kpsi (hC : ArchGammaFactorContinuous)
    (hE : ArchEnvelopeIntegrable) : Continuous Kpsi := by
  unfold Kpsi
  exact (continuous_poleTerm.sub continuous_primeTerm).add
    (continuous_archTerm hC hE)

end GppKreinKpsiContinuous
