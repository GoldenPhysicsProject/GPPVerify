import GppVerify.RiemannHypothesis.DigammaSeries
import GppVerify.RiemannHypothesis.DigammaGaussLimit
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Gauss's series for the digamma function (complex), closing `open_digamma_series_form`

For every `s ∈ ℂ` that is not `0, -1, -2, …`,

  `ψ(s) = Γ'(s)/Γ(s) = -γ - 1/s + Σ_{n ≥ 1} (1/n - 1/(n+s))`   (`digammaSeries_eq_digamma`).

Mathlib 4.33.1 defines `Complex.digamma = logDeriv Gamma` and lists Gauss' representation under
`TODO`; this module supplies it. Route:

1. **Real axis.** For `x > 0` the series' partial sums are
   `(H_N − log(N+1)) + (log(N+1) − log(x+N+1)) + (log(x+N+1) − Σ_{k≤N} 1/(x+k)) + 1/x`;
   the three brackets tend to `γ`, `0` and `ψ(x)` (Euler–Mascheroni, `log` asymptotics, and
   `GppDigammaGauss.tendsto_digamma_real`, Gauss's limit from Bohr–Mollerup convexity).
2. **Analyticity off the integers.** `ψ = Γ'/Γ` with `Γ` holomorphic and nonvanishing there;
   the series is a finite sum plus a tail that converges uniformly on a ball (Weierstrass
   M-test, `differentiableOn_tsum_of_summable_norm`).
3. **Identity theorem** on `ℂ ∖ ℤ` (connected: complement of a countable set in `ℂ`), from
   agreement on real points accumulating at `1/2`. Positive integers are covered by step 1.

This is the uniqueness step `DigammaSeries.lean` named as the remaining library gap. It is
stage E2a (complex) of the explicit-formula plan. No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppDigammaGaussSeries

open Complex Filter Topology Set GppDigammaSeries

/-! ### The integer complement -/

theorem isOpen_integerComplement : IsOpen Complex.integerComplement := by
  have h : Set.range ((↑) : ℤ → ℂ) = Complex.ofReal '' Set.range ((↑) : ℤ → ℝ) := by
    ext z
    simp
  unfold Complex.integerComplement
  rw [isOpen_compl_iff, h]
  exact Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _
    Int.isClosedEmbedding_coe_real.isClosed_range

theorem isPreconnected_integerComplement : IsPreconnected Complex.integerComplement :=
  (Set.Countable.isPathConnected_compl_of_one_lt_rank
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (Set.countable_range _)).isConnected.isPreconnected

theorem ne_neg_nat_of_mem {z : ℂ} (hz : z ∈ Complex.integerComplement) (m : ℕ) :
    z ≠ -(m : ℂ) := by
  intro h
  exact hz ⟨-(m : ℤ), by push_cast; exact h.symm⟩

theorem offPoles_of_mem {z : ℂ} (hz : z ∈ Complex.integerComplement) : OffPoles z := by
  intro n h
  exact hz ⟨-((n : ℤ) + 1), by push_cast; linear_combination -h⟩

/-! ### Analyticity of `ψ` -/

theorem analyticAt_Gamma {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    AnalyticAt ℂ Gamma z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_integerComplement.mem_nhds hz] with w hw
  exact differentiableAt_Gamma w (ne_neg_nat_of_mem hw)

theorem analyticAt_digamma {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    AnalyticAt ℂ digamma z := by
  have h : digamma = fun w => deriv Gamma w / Gamma w := by
    funext w
    rw [digamma_def, logDeriv_apply]
  rw [h]
  exact (analyticAt_Gamma hz).deriv.div (analyticAt_Gamma hz)
    (Gamma_ne_zero (ne_neg_nat_of_mem hz))

/-! ### Analyticity of the series -/

theorem norm_lower {R : ℝ} {w : ℂ} {k : ℕ} (hw : ‖w‖ ≤ R) (hk : 2 * R ≤ k) :
    ((k : ℝ) + 1) / 2 ≤ ‖(k : ℂ) + 1 + w‖ := by
  have h : ‖(k : ℂ) + 1‖ ≤ ‖(k : ℂ) + 1 + w‖ + ‖w‖ := by
    simpa using norm_sub_le ((k : ℂ) + 1 + w) w
  rw [norm_natCast_add_one] at h
  linarith

theorem ne_zero_of_norm_le {R : ℝ} {w : ℂ} {k : ℕ} (hw : ‖w‖ ≤ R) (hk : 2 * R ≤ k) :
    (k : ℂ) + 1 + w ≠ 0 := by
  have hl := norm_lower hw hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  intro h
  rw [h, norm_zero] at hl
  linarith

theorem norm_term_le {R : ℝ} {w : ℂ} {k : ℕ} (hw : ‖w‖ ≤ R) (hk : 2 * R ≤ k) :
    ‖digammaSeriesTerm w k‖ ≤ 2 * R / ((k : ℝ) + 1) ^ 2 := by
  have hl := norm_lower hw hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hw
  have hpos : 0 < ‖(k : ℂ) + 1 + w‖ := by linarith
  rw [digammaSeriesTerm_eq (ne_zero_of_norm_le hw hk), norm_div, norm_mul, norm_natCast_add_one,
    div_le_div_iff₀ (mul_pos hk1 hpos) (by positivity)]
  have h1 : 2 * R * (((k : ℝ) + 1) * (((k : ℝ) + 1) / 2))
      ≤ 2 * R * (((k : ℝ) + 1) * ‖(k : ℂ) + 1 + w‖) := by gcongr
  have h2 : ‖w‖ * ((k : ℝ) + 1) ^ 2 ≤ R * ((k : ℝ) + 1) ^ 2 := by gcongr
  have h3 : 2 * R * (((k : ℝ) + 1) * (((k : ℝ) + 1) / 2)) = R * ((k : ℝ) + 1) ^ 2 := by ring
  linarith

theorem differentiableAt_digammaSeries {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    DifferentiableAt ℂ digammaSeries z := by
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
  have hsq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    simpa using h
  have hu := hsq.mul_left (2 * R)
  have hle : ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball z 1 →
      ‖digammaSeriesTerm w (n + N)‖ ≤ 2 * R * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n w hw
    refine (norm_term_le (hball w hw) (hk n)).trans ?_
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (n : ℝ) ≤ ((n + N : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    gcongr
  have hdiffterm : ∀ (k : ℕ) (w : ℂ), (k : ℂ) + 1 + w ≠ 0 →
      DifferentiableAt ℂ (fun w => digammaSeriesTerm w k) w := by
    intro k w hne
    unfold digammaSeriesTerm
    exact (differentiableAt_const _).sub ((differentiableAt_const _).add differentiableAt_id
      |>.inv hne)
  have hT : DifferentiableOn ℂ (fun w => ∑' n : ℕ, digammaSeriesTerm w (n + N))
      (Metric.ball z 1) := by
    refine differentiableOn_tsum_of_summable_norm hu (fun n w hw => ?_) Metric.isOpen_ball hle
    exact (hdiffterm _ w (ne_zero_of_norm_le (hball w hw) (hk n))).differentiableWithinAt
  have hz0 : z ≠ 0 := by simpa using ne_neg_nat_of_mem hz 0
  set G : ℂ → ℂ := fun w => -(Real.eulerMascheroniConstant : ℂ) - w⁻¹
    + ((∑ n ∈ Finset.range N, digammaSeriesTerm w n) + ∑' n : ℕ, digammaSeriesTerm w (n + N))
    with hG
  have hGd : DifferentiableAt ℂ G z := by
    refine ((differentiableAt_const _).sub (differentiableAt_id.inv hz0)).add
      ((DifferentiableAt.fun_sum fun n _ => hdiffterm n z (offPoles_of_mem hz n)).add
        (hT.differentiableAt (Metric.ball_mem_nhds z one_pos)))
  refine hGd.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds z one_pos] with w hw
  have htail : Summable (fun n : ℕ => digammaSeriesTerm w (n + N)) :=
    Summable.of_norm_bounded hu (fun n => hle n w hw)
  have hsum : Summable (digammaSeriesTerm w) := (summable_nat_add_iff N).mp htail
  simp only [hG, digammaSeries]
  rw [hsum.sum_add_tsum_nat_add N]

theorem analyticAt_digammaSeries {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    AnalyticAt ℂ digammaSeries z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_integerComplement.mem_nhds hz] with w hw
  exact differentiableAt_digammaSeries hw

/-! ### The real axis -/

private lemma ne_neg_nat_real {x : ℝ} (hx : 0 < x) (m : ℕ) : x ≠ -(m : ℝ) := by
  intro h
  rw [h] at hx
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- At a positive real point, `ψ` is the derivative of `log ∘ Γ`. -/
theorem digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  have hcx : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m h
    exact ne_neg_nat_real hx m (by exact_mod_cast h)
  have hf : DifferentiableAt ℂ Gamma (x : ℂ) := differentiableAt_Gamma _ hcx
  have hg : HasDerivAt Real.Gamma (deriv Real.Gamma x) x :=
    (Real.differentiableAt_Gamma (ne_neg_nat_real hx)).hasDerivAt
  have hfg : ∀ s : ℝ, Gamma (s : ℂ) = ((Real.Gamma s : ℝ) : ℂ) := fun s => Complex.Gamma_ofReal s
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
private noncomputable def r (x : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 1 + x)⁻¹

private lemma r_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 ≤ r x n := by
  unfold r
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [sub_nonneg]
  exact inv_anti₀ h1 (by linarith)

private lemma partial_r {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ Finset.range N, r x n
      = (harmonic N : ℝ) - GppDigammaGauss.S x (N + 1) + x⁻¹ := by
  induction N with
  | zero =>
    simp [GppDigammaGauss.S]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ, GppDigammaGauss.S, GppDigammaGauss.S,
      Finset.sum_range_succ (n := N + 1)]
    unfold r
    push_cast
    have h1 : x + ((N : ℝ) + 1) ≠ 0 := by positivity
    rw [one_div]
    ring_nf

theorem hasSum_r {x : ℝ} (hx : 0 < x) :
    HasSum (r x) (deriv (Real.log ∘ Real.Gamma) x + Real.eulerMascheroniConstant + x⁻¹) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (r_nonneg hx)]
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
  have T3 := (GppDigammaGauss.tendsto_digamma_real hx).comp (tendsto_add_atTop_nat 1)
  have hsum := ((T1.add T2).add T3).add (tendsto_const_nhds (x := x⁻¹))
  rw [add_zero, show Real.eulerMascheroniConstant + deriv (Real.log ∘ Real.Gamma) x + x⁻¹
    = deriv (Real.log ∘ Real.Gamma) x + Real.eulerMascheroniConstant + x⁻¹ by ring] at hsum
  refine hsum.congr (fun N => ?_)
  rw [partial_r hx N]
  simp only [Function.comp_apply]
  ring

theorem digammaSeries_ofReal {x : ℝ} (hx : 0 < x) :
    digammaSeries (x : ℂ) = Complex.digamma (x : ℂ) := by
  have h : HasSum (digammaSeriesTerm (x : ℂ))
      (((deriv (Real.log ∘ Real.Gamma) x + Real.eulerMascheroniConstant + x⁻¹ : ℝ)) : ℂ) := by
    have h0 := Complex.hasSum_ofReal.mpr (hasSum_r hx)
    refine h0.congr_fun (fun n => ?_)
    simp [digammaSeriesTerm, r]
  rw [digammaSeries, h.tsum_eq, digamma_ofReal hx]
  push_cast
  ring

/-! ### The identity -/

theorem half_mem_integerComplement : ((1 / 2 : ℝ) : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have h : ((n : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by exact_mod_cast hn
  have h2 : (n : ℝ) * 2 = 1 := by
    have := Complex.ofReal_injective h
    rw [this]; norm_num
  have h3 : n * 2 = 1 := by exact_mod_cast h2
  omega

theorem eqOn_integerComplement :
    EqOn digammaSeries Complex.digamma Complex.integerComplement := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (fun z hz => analyticAt_digammaSeries hz) (fun z hz => analyticAt_digamma hz)
    isPreconnected_integerComplement half_mem_integerComplement ?_
  have hreal : ∀ᶠ x : ℝ in 𝓝[≠] (1 / 2 : ℝ), digammaSeries (x : ℂ) = Complex.digamma (x : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with x hx
    exact digammaSeries_ofReal hx
  have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 / 2 : ℝ)) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact fun h => hx (Complex.ofReal_injective h)
  exact htend.frequently hreal.frequently

/-- **Gauss's series for the digamma function.** For `s ∉ {0, -1, -2, …}`,
`ψ(s) = -γ - 1/s + Σ_{n≥0} (1/(n+1) - 1/(n+1+s))`. Retires
`GppSpectralWeil.open_digamma_series_form`. -/
theorem digammaSeries_eq_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digammaSeries s = Complex.digamma s := by
  by_cases hmem : s ∈ Complex.integerComplement
  · exact eqOn_integerComplement hmem
  · have hmem' : ∃ n : ℤ, (n : ℂ) = s := by
      simpa [Complex.integerComplement] using hmem
    obtain ⟨n, hn⟩ := hmem'
    rcases lt_or_ge 0 n with hpos | hneg
    · have hs' : s = ((n : ℝ) : ℂ) := by rw [← hn]; push_cast; rfl
      rw [hs']
      exact digammaSeries_ofReal (by exact_mod_cast hpos)
    · exfalso
      apply hs (-n).toNat
      have h1 : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      have h2 : (((-n).toNat : ℕ) : ℂ) = ((-n : ℤ) : ℂ) := by exact_mod_cast h1
      rw [← hn, h2]
      push_cast
      ring

end GppDigammaGaussSeries

#print axioms GppDigammaGaussSeries.digammaSeries_eq_digamma
