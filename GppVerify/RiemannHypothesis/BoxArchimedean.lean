import GppVerify.RiemannHypothesis.BoxCurvature

/-!
# The box archimedean term is `C∞ L + 2 ∫₀^L Gcl`

`BoxCurvature.lean` proved the curvature of a *model* whose archimedean part used `∫₁^L Gcl`.  Here the
archimedean integral itself is identified: with `w(t) = e^{−t/2}/(1 − e^{−2t})`,

* `∫_{t}^∞ w = Gcl t` for `t > 0` (`integral_wk_Ioi`);
* `∫₀^∞ w(t) min(t, L) dt = ∫₀^L Gcl` (`integral_wk_mul_min`), by Fubini, with the integrability coming
  from `t·w(t) ≤ (1 + 2t) e^{−t/2}/2` (`mul_wk_le`).

So the model's archimedean part differs from the true box archimedean term `C∞ L + 2∫₀^∞ w·min(t, L)` by exactly
`2∫₀^1 Gcl`, a constant (`archBox_eq`, `smoothBox_eq`).

**Scope.** This identifies the archimedean *integral*.  That the box Weil form *is* pole + archimedean + prime
with this normalisation is the explicit formula, taken as the definition (not identified with `weilForm`,
the box not being `C^∞`).  No positivity claim.

No `sorry`, no axiom.
-/

open Real Set MeasureTheory Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GppBoxArchimedean

open GppBoxCurvature

theorem wk_pos {t : ℝ} (ht : 0 < t) : 0 < wk t := by
  unfold wk
  have : Real.exp (-2 * t) < 1 := by
    have := Real.exp_lt_exp.mpr (show -2 * t < 0 by linarith)
    simpa using this
  exact div_pos (Real.exp_pos _) (by linarith)

theorem tendsto_Gcl : Tendsto Gcl atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h2 : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    refine (tendsto_neg_atTop_atBot.comp h2).congr (fun t => ?_)
    simp [neg_div]
  have hF : ContinuousAt (fun u : ℝ => (1 / 2) * Real.log ((1 + u) / (1 - u)) + Real.arctan u) 0 := by
    apply ContinuousAt.add
    · apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.log
      · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      · norm_num
    · exact Real.continuous_arctan.continuousAt
  have h := hF.tendsto.comp hu
  convert h using 2
  · funext t; simp [Gcl]
  · simp

theorem integrableOn_wk {a : ℝ} (ha : 0 < a) : IntegrableOn wk (Ioi a) := by
  have hd : ∀ x ∈ Ici a, HasDerivAt Gcl (-wk x) x := fun x hx =>
    hasDerivAt_Gcl (lt_of_lt_of_le ha hx)
  have := integrableOn_Ioi_deriv_of_nonpos' hd
    (fun x hx => by have := wk_pos (lt_trans ha hx); linarith) tendsto_Gcl
  simpa using this.neg

/-- `∫_a^∞ w = Gcl a`. -/
theorem integral_wk_Ioi {a : ℝ} (ha : 0 < a) : ∫ t in Ioi a, wk t = Gcl a := by
  have hd : ∀ x ∈ Ici a, HasDerivAt Gcl (-wk x) x := fun x hx =>
    hasDerivAt_Gcl (lt_of_lt_of_le ha hx)
  have hint : IntegrableOn (fun x => -wk x) (Ioi a) := (integrableOn_wk ha).neg
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint tendsto_Gcl
  rw [integral_neg] at this
  linarith

theorem measurable_wk : Measurable wk := by
  unfold wk
  fun_prop

/-- `t · w(t) ≤ (1 + 2t) e^{−t/2} / 2`, from `1 − e^{−2t} ≥ 2t/(1 + 2t)`. -/
theorem mul_wk_le {t : ℝ} (ht : 0 < t) : wk t * t ≤ (1 / 2) * Real.exp (-t / 2) + t * Real.exp (-t / 2) := by
  have h1 : 1 + 2 * t ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t); linarith
  have h2 : Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hx : 0 < 1 - Real.exp (-2 * t) := by
    have := Real.exp_lt_exp.mpr (show -2 * t < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have h3 : 2 * t ≤ (1 - Real.exp (-2 * t)) * (1 + 2 * t) := by
    have hp := Real.exp_pos (-2 * t)
    nlinarith [mul_le_mul_of_nonneg_left h1 hp.le]
  unfold wk
  rw [div_mul_eq_mul_div, div_le_iff₀ hx]
  have he := Real.exp_pos (-t / 2)
  nlinarith [mul_le_mul_of_nonneg_left h3 he.le]

theorem integrableOn_bound : IntegrableOn
    (fun t : ℝ => (1 / 2) * Real.exp (-t / 2) + t * Real.exp (-t / 2)) (Ioi 0) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := 1 / 2)
    (by norm_num) one_pos (by norm_num)
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1 / 2)
    (by norm_num) one_pos (by norm_num)
  have e : ∀ t : ℝ, Real.exp (-(1 / 2) * t) = Real.exp (-t / 2) := fun t => by congr 1; ring
  simp only [Real.rpow_one, Real.rpow_zero, one_mul, e] at h0 h1
  exact (h0.const_mul (1 / 2)).add h1

/-- The Fubini kernel `F(s, t) = w(t)` if `s < t`, else `0`. -/
def Fk (p : ℝ × ℝ) : ℝ := if p.1 < p.2 then wk p.2 else 0

theorem measurable_Fk : Measurable Fk :=
  Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
    (measurable_wk.comp measurable_snd) measurable_const

theorem Fk_nonneg {p : ℝ × ℝ} (hp : 0 < p.2) : 0 ≤ Fk p := by
  unfold Fk
  split_ifs
  · exact (wk_pos hp).le
  · exact le_rfl

/-- The inner integral in `s`: `∫_{(0,L]} F(s, t) ds = w(t) · min(t, L)` for `t > 0`. -/
theorem inner_s {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    ∫ s in Ioc 0 L, Fk (s, t) = wk t * min t L := by
  have hF : (fun s : ℝ => Fk (s, t)) = Set.indicator (Iio t) (fun _ => wk t) := by
    funext s; simp [Fk, Set.indicator]
  rw [hF, integral_indicator measurableSet_Iio, setIntegral_const, smul_eq_mul]
  have hv : volume.real (Ioc 0 L ∩ Iio t) = min t L := by
    rcases le_total t L with h | h
    · have : Ioc 0 L ∩ Iio t = Ioo 0 t := by
        ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
        constructor
        · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
        · rintro ⟨a, b⟩; exact ⟨⟨a, by linarith⟩, b⟩
      rw [this, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), min_eq_left h]
      ring
    · rcases h.eq_or_lt with h' | h'
      · subst h'
        have : Ioc 0 L ∩ Iio L = Ioo 0 L := by
          ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
          constructor
          · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
          · rintro ⟨a, b⟩; exact ⟨⟨a, b.le⟩, b⟩
        rw [this, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
        simp
      · have : Ioc 0 L ∩ Iio t = Ioc 0 L := by
          ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iio]
          constructor
          · rintro ⟨a, _⟩; exact a
          · rintro ⟨a, b⟩; exact ⟨⟨a, b⟩, by linarith⟩
        rw [this, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
          min_eq_right h]
        ring
  rw [measureReal_restrict_apply measurableSet_Iio, inter_comm, hv]
  ring

/-- The inner integral in `t`: `∫_{(0,∞)} F(s, t) dt = Gcl s` for `s > 0`. -/
theorem inner_t {s : ℝ} (hs : 0 < s) : ∫ t in Ioi 0, Fk (s, t) = Gcl s := by
  have hF : (fun t : ℝ => Fk (s, t)) = Set.indicator (Ioi s) wk := by
    funext t; simp [Fk, Set.indicator]
  rw [hF, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr hs.le]
  exact integral_wk_Ioi hs

theorem integrable_inner {L : ℝ} (hL : 0 < L) :
    Integrable (fun t : ℝ => wk t * min t L) (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' integrableOn_bound ?_ ?_
  · exact (measurable_wk.mul (measurable_id.min measurable_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : 0 < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wk_pos ht).le (le_min ht.le hL.le))]
    calc wk t * min t L ≤ wk t * t :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (wk_pos ht).le
      _ ≤ _ := mul_wk_le ht

theorem integrable_Fk {L : ℝ} (hL : 0 < L) :
    Integrable Fk ((volume.restrict (Ioc 0 L)).prod (volume.restrict (Ioi 0))) := by
  rw [integrable_prod_iff' measurable_Fk.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hF : (fun s : ℝ => Fk (s, t)) = Set.indicator (Iio t) (fun _ => wk t) := by
      funext s; simp [Fk, Set.indicator]
    rw [hF]
    exact (integrable_const _).indicator measurableSet_Iio
  · refine (integrable_inner hL).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : 0 < t := ht
    have : ∀ s : ℝ, ‖Fk (s, t)‖ = Fk (s, t) := fun s =>
      by rw [Real.norm_eq_abs, abs_of_nonneg (Fk_nonneg ht)]
    simp only [this]
    exact (inner_s hL ht).symm

theorem integrableOn_Gcl {L : ℝ} (hL : 0 < L) : IntegrableOn Gcl (Ioc 0 L) := by
  have h := (integrable_Fk hL).integral_norm_prod_left
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hnn : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ‖Fk (s, t)‖ = Fk (s, t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Fk_nonneg (show 0 < t from ht))]
  rw [integral_congr_ae hnn]
  exact inner_t hs.1

theorem intervalIntegrable_Gcl {L : ℝ} (hL : 0 < L) : IntervalIntegrable Gcl volume 0 L :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).mpr (integrableOn_Gcl hL)

/-- **Fubini.** `∫₀^∞ w(t) min(t, L) dt = ∫₀^L Gcl`. -/
theorem integral_wk_mul_min {L : ℝ} (hL : 0 < L) :
    ∫ t in Ioi 0, wk t * min t L = ∫ s in Ioc 0 L, Gcl s := by
  have hswap := integral_integral_swap (μ := volume.restrict (Ioc 0 L))
    (ν := volume.restrict (Ioi 0)) (f := fun s t => Fk (s, t)) (integrable_Fk hL)
  have h1 : ∫ s in Ioc 0 L, ∫ t in Ioi 0, Fk (s, t) = ∫ s in Ioc 0 L, Gcl s :=
    setIntegral_congr_fun measurableSet_Ioc (fun s hs => inner_t hs.1)
  have h2 : ∫ t in Ioi 0, ∫ s in Ioc 0 L, Fk (s, t) = ∫ t in Ioi 0, wk t * min t L :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => inner_s hL ht)
  rw [← h1, ← h2]
  exact hswap.symm

/-- The box archimedean term `C∞ L + 2 ∫₀^∞ w(t) min(t, L) dt`. -/
def archBox (L : ℝ) : ℝ :=
  GppArchimedeanFloor.archimedeanFloor * L + 2 * ∫ t in Ioi 0, wk t * min t L

theorem archBox_eq {L : ℝ} (hL : 0 < L) :
    archBox L = GppArchimedeanFloor.archimedeanFloor * L + 2 * ∫ s in (0 : ℝ)..L, Gcl s := by
  rw [archBox, integral_wk_mul_min hL, intervalIntegral.integral_of_le hL.le]

/-- The `BoxCurvature` model's archimedean part differs from the true box term by the constant
`2 ∫₀^1 Gcl`. -/
theorem smoothBox_eq {L : ℝ} (hL : 0 < L) :
    smoothBox L = 16 * (Real.cosh (L / 2) - 1) + archBox L - 2 * ∫ s in (0 : ℝ)..1, Gcl s := by
  have h01 : IntervalIntegrable Gcl volume 0 1 := intervalIntegrable_Gcl one_pos
  have h1L : IntervalIntegrable Gcl volume 1 L := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_Gcl.mono ?_
    intro x hx
    exact (lt_min one_pos hL).trans_le hx.1
  have hadd := intervalIntegral.integral_add_adjacent_intervals h01 h1L
  have h0L : ∫ s in (0 : ℝ)..L, Gcl s = (∫ s in (0 : ℝ)..1, Gcl s) + ∫ s in (1 : ℝ)..L, Gcl s :=
    hadd.symm
  rw [smoothBox, archBox_eq hL, h0L]
  ring

end GppBoxArchimedean

#print axioms GppBoxArchimedean.integral_wk_Ioi
#print axioms GppBoxArchimedean.integral_wk_mul_min
#print axioms GppBoxArchimedean.smoothBox_eq
