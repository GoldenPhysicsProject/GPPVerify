/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6827581325 / 6827583106, the
`ArchMatch` half: "state whether the same three lemmas also close `ArchMatch` through
`transform`'s identity `ĝ_d(1/2 + it) = Ψ(t)² cos(td)`, as a proved reduction if it is one."

# `ArchMatch` reduced to `ArchLimit`

Built on `RegularitySplit` (same mollifier `g_{d,n} = φ_n ⋆ g_d`, same `stripConv`,
`phiHat_tendsto`). For each `n`, the in-tree `archimedean_identification` holds for the test
function `g_{d,n}`:
`(1/2π) ∫ ĝ_{d,n}(1/2 + ir) ψ(1/4 + ir/2) dr = A∞(g_{d,n}) + g_{d,n}(0) log π`.
Let `n → ∞`. Left: dominated convergence on the critical line, `ĝ_{d,n} = ĝ_d φ̂_n`
(`stripConv`, `Re s = 1/2`), `|φ̂_n| ≤ e^{1/2}`, `φ̂_n → 1`, domination
`|ĝ_d(1/2 + ir)| |ψ(1/4 + ir/2)| ≤ 144² C (1+|r|)^{−3}` (`norm_triPsi_le` +
`GppShiftContour.norm_digamma_strip_le`). Right: `ArchLimit` and `g_{d,n}(0) → g_d(0)`.
Fourier inversion at `0` for `g_d` (`∫ ĝ_d(1/2 + ir) dr = 2π g_d(0)`) by the same limit from
the in-tree `integral_hline`, unconditionally. Then `ĝ_d(1/2 + ir) = Ψ(r)² cos(rd)` (`r ≠ 0`,
`integral_gd_exp` + `triFourier`), `Re ψ(1/4 − ir/2) = Re ψ(1/4 + ir/2)`
(`GppDigammaQuarterSech.digamma_conj`) and the even fold `integral_comp_abs` give
`A∞(g_d) = (1/π) ∫_0^∞ Ψ(t)² cos(td) (Re ψ(1/4 + it/2) − log π) dt = archTerm d`.

PROVED (std axioms, 0 sorry): `archMatch_of_archLimit : ArchLimit → ArchMatch`,
`hefIdent_of_archLimit' : ArchLimit → HEFIdent`,
`hPsiArchLimitChain : HPsi → ArchLimit → KreinDecomp → IdentityStep → RiemannHypothesis`,
and the unconditional `integral_hline_gd`, `hline_gd`, `norm_hline_gd_le`, `dig_neg`.
Named premise, NOT proved: `ArchLimit` (RegularitySplit). H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.RegularitySplit
import GppVerify.RiemannHypothesis.ArchimedeanIdentification
import GppVerify.RiemannHypothesis.ShiftContour
import GppVerify.RiemannHypothesis.DigammaQuarterSech
import GppVerify.RiemannHypothesis.DigammaGaussSeries

namespace GppArchMatchSplit

open MeasureTheory Filter Topology GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit
  GppKreinHEFSplit GppHEFIdentSplit GppKreinRepSplit GppArchimedeanId

/-- `φ̂_n(1/2 + ir)`. -/
noncomputable def phat (n : ℕ) (r : ℝ) : ℂ :=
  GppMeyerSpectralWeil.spectralTransform (GppRegularitySplit.phiN n) ((1 / 2 : ℂ) + r * Complex.I)



/-- `ψ(1/4 + i r/2)`. -/
noncomputable def dig (r : ℝ) : ℂ := Complex.digamma ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I)

theorem dig_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ‖dig r‖ ≤ C * (1 + |r|) := by
  obtain ⟨C, hC⟩ := GppShiftContour.norm_digamma_strip_le
  refine ⟨max C 0, le_max_right _ _, fun r => ?_⟩
  have h := hC (1 / 2) r ⟨by norm_num, by norm_num⟩
  have e : (((1 / 2 : ℝ) : ℂ) + r * Complex.I) / 2 = (1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I := by
    push_cast; ring
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

theorem not_neg_nat (r : ℝ) : ∀ m : ℕ, (1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I ≠ -m := by
  intro m hm
  have h := congrArg Complex.re hm
  simp at h
  have h' : (4 : ℝ) * m = -1 := by linarith
  have : (0 : ℝ) ≤ 4 * m := by positivity
  linarith

theorem dig_continuous : Continuous dig := by
  refine continuous_iff_continuousAt.2 fun r => ?_
  have hz : (1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have h := congrArg Complex.re hn
    simp at h
    have h' : (4 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (4 : ℝ) * n = 1)
    omega
  unfold dig
  exact (GppDigammaGaussSeries.analyticAt_digamma hz).continuousAt.comp
    (f := fun r : ℝ => (1 / 4 : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I) (by fun_prop)

theorem dig_neg (r : ℝ) : (dig (-r)).re = (dig r).re := by
  unfold dig
  have e : (1 / 4 : ℂ) + ((-r / 2 : ℝ) : ℂ) * Complex.I =
      (starRingEnd ℂ) ((1 / 4 : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]
    push_cast; ring
  rw [e, GppDigammaQuarterSech.digamma_conj (not_neg_nat r), Complex.conj_re]

/-- `ĝ_d(1/2 + ir) = Ψ(r)Ψ(−r) cos(rd)` for real `r ≠ 0` (`integral_gd_exp` + `triFourier`). -/
theorem hline_gd' (d : ℝ) {r : ℝ} (hr : r ≠ 0) :
    hline (gd d) r = efCoeff r * Complex.cos (r * d) := by
  unfold hline GppMeyerSpectralWeil.spectralTransform
  have hz : (1 / 2 : ℂ) + r * Complex.I - 1 / 2 = Complex.I * (r : ℂ) := by ring
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [hz, integral_gd_exp, triFourier _ hr', Complex.cos]
  ring_nf

theorem bigPsi_eq {r : ℝ} (hr : r ≠ 0) : bigPsi r = (Real.sin (r / 2) / (r / 2)) ^ 2 := by
  unfold bigPsi; rw [if_neg hr]

/-- `ĝ_d(1/2 + ir) = Ψ(r)² cos(rd)` for real `r ≠ 0`. -/
theorem hline_gd (d : ℝ) {r : ℝ} (hr : r ≠ 0) :
    hline (gd d) r = ((bigPsi r ^ 2 * Real.cos (r * d) : ℝ) : ℂ) := by
  rw [hline_gd' d hr, bigPsi_eq hr]
  unfold efCoeff GppKreinLaplace.triPsi
  push_cast
  rw [neg_div, Complex.sin_neg, neg_div_neg_eq]
  ring

theorem bigPsi_neg (r : ℝ) : bigPsi (-r) = bigPsi r := by
  by_cases hr : r = 0
  · rw [hr, neg_zero]
  · rw [bigPsi_eq hr, bigPsi_eq (neg_ne_zero.2 hr), neg_div, Real.sin_neg, neg_div_neg_eq]

theorem bigPsi_measurable : Measurable bigPsi := by
  unfold bigPsi
  exact Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const (by fun_prop)

theorem norm_hline_gd_le (d : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ‖hline (gd d) r‖ ≤ 144 ^ 2 / (1 + |r|) ^ 4 := by
  rw [hline_gd' d hr, norm_mul]
  have h1 := norm_triPsi_le (γ := (r : ℂ)) (by norm_num)
  have h2 := norm_triPsi_le (γ := -(r : ℂ)) (by norm_num)
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at h2
  have hc : ‖Complex.cos (r * d)‖ ≤ 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  unfold efCoeff
  rw [norm_mul]
  calc ‖GppKreinLaplace.triPsi r‖ * ‖GppKreinLaplace.triPsi (-r)‖ * ‖Complex.cos (r * d)‖
      ≤ (144 / (1 + |r|) ^ 2) * (144 / (1 + |r|) ^ 2) * 1 := by gcongr
    _ = 144 ^ 2 / (1 + |r|) ^ 4 := by field_simp

theorem ae_ne_zero : ∀ᵐ r : ℝ, r ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)

theorem bound_pt (d : ℝ) {w : ℝ → ℂ} {K : ℝ} (_hK : 0 ≤ K) (hw : ∀ r, ‖w r‖ ≤ K * (1 + |r|))
    {r : ℝ} (hr : r ≠ 0) :
    ‖hline (gd d) r‖ * ‖w r‖ ≤ 144 ^ 2 * K * (1 + ‖r‖) ^ (-(3 : ℝ)) := by
  have ha : 0 < 1 + |r| := by positivity
  have hp : (1 + ‖r‖) ^ (-(3 : ℝ)) = 1 / (1 + |r|) ^ 3 := by
    rw [Real.rpow_neg (by positivity), Real.norm_eq_abs, one_div]
    norm_cast
  rw [hp]
  calc ‖hline (gd d) r‖ * ‖w r‖ ≤ (144 ^ 2 / (1 + |r|) ^ 4) * (K * (1 + |r|)) :=
        mul_le_mul (norm_hline_gd_le d hr) (hw r) (norm_nonneg _) (by positivity)
    _ = 144 ^ 2 * K * (1 / (1 + |r|) ^ 3) := by field_simp

theorem hline_gd_aesm (d : ℝ) : AEStronglyMeasurable (hline (gd d)) := by
  have hm : Measurable (fun r : ℝ => ((bigPsi r ^ 2 * Real.cos (r * d) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((bigPsi_measurable.pow_const 2).mul (by fun_prop))
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [ae_ne_zero] with r hr using (hline_gd d hr).symm

theorem integrable_hline_gd_mul (d : ℝ) {w : ℝ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hwc : Continuous w) (hw : ∀ r, ‖w r‖ ≤ K * (1 + |r|)) :
    Integrable (fun r => hline (gd d) r * w r) := by
  refine ((integrable_one_add_norm (E := ℝ) (r := 3) (by norm_num)).const_mul
    (144 ^ 2 * K)).mono' ((hline_gd_aesm d).mul hwc.aestronglyMeasurable) ?_
  filter_upwards [ae_ne_zero] with r hr
  rw [norm_mul]
  exact bound_pt d hK hw hr

/-- Dominated convergence on the critical line, from `stripConv` + `phiHat_tendsto` (PROVED). -/
theorem tendsto_hline_mul (d : ℝ) {w : ℝ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hwc : Continuous w) (hw : ∀ r, ‖w r‖ ≤ K * (1 + |r|)) :
    Tendsto (fun n => ∫ r, hline (GppRegularitySplit.moll n (gd d)) r * w r) atTop
      (𝓝 (∫ r, hline (gd d) r * w r)) := by
  have hs : ∀ r : ℝ, 0 < ((1 / 2 : ℂ) + r * Complex.I).re ∧ ((1 / 2 : ℂ) + r * Complex.I).re < 1 :=
    fun r => by simp; norm_num
  have hf : ∀ n r, hline (GppRegularitySplit.moll n (gd d)) r =
      hline (gd d) r * phat n r :=
    fun n r => (GppRegularitySplit.stripConv n d _ (hs r).1 (hs r).2).2
  have hbd : ∀ n r, ‖phat n r‖ ≤ Real.exp (1 / 2) := fun n r =>
    (GppRegularitySplit.stripConv n d _ (hs r).1 (hs r).2).1.trans
      (Real.exp_le_exp.2 (by linarith [GppRegularitySplit.epsN_le_one n]))
  refine tendsto_integral_of_dominated_convergence
    (fun r => Real.exp (1 / 2) * (144 ^ 2 * K * (1 + ‖r‖) ^ (-(3 : ℝ)))) (fun n => ?_)
    ((integrable_one_add_norm (E := ℝ) (r := 3) (by norm_num)).const_mul (144 ^ 2 * K)
      |>.const_mul _) (fun n => ?_) (Eventually.of_forall fun r => ?_)
  · exact ((hline_continuous (GppRegularitySplit.isTest_moll n d)).mul hwc).aestronglyMeasurable
  · filter_upwards [ae_ne_zero] with r hr
    rw [hf, norm_mul, norm_mul]
    calc ‖hline (gd d) r‖ * ‖phat n r‖ * ‖w r‖
        = ‖phat n r‖ * (‖hline (gd d) r‖ * ‖w r‖) := by ring
      _ ≤ Real.exp (1 / 2) * (144 ^ 2 * K * (1 + ‖r‖) ^ (-(3 : ℝ))) :=
        mul_le_mul (hbd n r) (bound_pt d hK hw hr) (by positivity) (by positivity)
  · have e : ∀ n, hline (GppRegularitySplit.moll n (gd d)) r * w r =
        (hline (gd d) r * w r) * phat n r := fun n => by
      rw [hf]; ring
    simp_rw [e]
    have := (GppRegularitySplit.phiHat_tendsto ((1 / 2 : ℂ) + r * Complex.I)).const_mul
      (hline (gd d) r * w r)
    rw [mul_one] at this
    exact this

/-- The in-tree `archimedean_identification` extended to `g_d`, from `ArchLimit`
(PROVED, conditional on `ArchLimit`). -/
theorem archId_gd (hL : GppRegularitySplit.ArchLimit) (d : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ, hline (gd d) r * dig r =
      ((GppArchimedeanFloor.archimedeanTerm (gd d) + gd d 0 * Real.log Real.pi : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := dig_bound
  have hl := (tendsto_hline_mul d hC0 dig_continuous hC).const_mul
    ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hR : Tendsto (fun n => ((GppArchimedeanFloor.archimedeanTerm
      (GppRegularitySplit.moll n (gd d)) +
      GppRegularitySplit.moll n (gd d) 0 * Real.log Real.pi : ℝ) : ℂ)) atTop
      (𝓝 ((GppArchimedeanFloor.archimedeanTerm (gd d) + gd d 0 * Real.log Real.pi : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp
      ((hL d).add ((GppRegularitySplit.moll_tendsto (GppRegularitySplit.gd_continuous d) 0).mul_const _))
  exact tendsto_nhds_unique
    (hl.congr fun n => archimedean_identification (GppRegularitySplit.isTest_moll n d)) hR

/-- Fourier inversion at `0` for `g_d`, by the same limit (PROVED, unconditional). -/
theorem integral_hline_gd (d : ℝ) :
    ∫ r : ℝ, hline (gd d) r = ((2 * Real.pi : ℝ) : ℂ) * (gd d 0 : ℂ) := by
  have hl := tendsto_hline_mul d (w := fun _ => (1 : ℂ)) zero_le_one continuous_const
    (fun r => by rw [norm_one, one_mul]; linarith [abs_nonneg r])
  simp only [mul_one] at hl
  have hR : Tendsto (fun n => ((2 * Real.pi : ℝ) : ℂ) *
      (GppRegularitySplit.moll n (gd d) 0 : ℂ)) atTop
      (𝓝 (((2 * Real.pi : ℝ) : ℂ) * (gd d 0 : ℂ))) :=
    ((Complex.continuous_ofReal.tendsto _).comp
      (GppRegularitySplit.moll_tendsto (GppRegularitySplit.gd_continuous d) 0)).const_mul _
  exact tendsto_nhds_unique (hl.congr fun n => integral_hline (GppRegularitySplit.isTest_moll n d)) hR

/-- The real frequency integrand `Ψ(r)² cos(rd) (Re ψ(1/4 + ir/2) − log π)`. -/
noncomputable def archF (d r : ℝ) : ℝ :=
  bigPsi r ^ 2 * Real.cos (r * d) * ((dig r).re - Real.log Real.pi)

theorem archF_abs (d r : ℝ) : archF d |r| = archF d r := by
  rcases abs_choice r with h | h
  · rw [h]
  · rw [h]; unfold archF; rw [bigPsi_neg, neg_mul, Real.cos_neg, dig_neg]

/-- **`ArchMatch` from `ArchLimit` (PROVED, conditional on `ArchLimit`).** -/
theorem archMatch_of_archLimit (hL : GppRegularitySplit.ArchLimit) : ArchMatch := by
  intro d
  obtain ⟨C, hC0, hC⟩ := dig_bound
  have hI1 := integrable_hline_gd_mul d hC0 dig_continuous hC
  have hI0 : Integrable (hline (gd d)) := by
    have := integrable_hline_gd_mul d (w := fun _ => (1 : ℂ)) zero_le_one continuous_const
      (fun r => by rw [norm_one, one_mul]; linarith [abs_nonneg r])
    simpa only [mul_one] using this
  have hA := archId_gd hL d
  have h0 := integral_hline_gd d
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- `∫ archF = 2π · archimedeanTerm g_d`
  have hF : ∫ r, archF d r =
      (∫ r, hline (gd d) r * dig r).re - Real.log Real.pi * (∫ r, hline (gd d) r).re := by
    have e1 := integral_re hI1
    have e0 := integral_re hI0
    simp only [RCLike.re_to_complex] at e1 e0
    rw [← e1, ← e0, ← integral_const_mul,
      ← integral_sub (f := fun x => (hline (gd d) x * dig x).re)
        (g := fun a => Real.log Real.pi * (hline (gd d) a).re) hI1.re (hI0.re.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with r hr
    unfold archF
    rw [hline_gd d hr, Complex.re_ofReal_mul, Complex.ofReal_re]
    ring
  have hval : (∫ r, hline (gd d) r * dig r) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((GppArchimedeanFloor.archimedeanTerm (gd d) + gd d 0 * Real.log Real.pi : ℝ) : ℂ) := by
    rw [← hA]
    have : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]; field_simp; simp
    rw [← mul_assoc, this, one_mul]
  rw [hval, h0, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_re] at hF
  have hfold : ∫ r, archF d r = 2 * ∫ r in Set.Ioi (0 : ℝ), archF d r := by
    rw [← integral_comp_abs]
    exact integral_congr_ae (Eventually.of_forall fun r => (archF_abs d r).symm)
  unfold archTerm
  change _ = (1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ), archF d t
  have : ∫ t in Set.Ioi (0 : ℝ), archF d t = Real.pi * GppArchimedeanFloor.archimedeanTerm (gd d) := by
    linarith
  rw [this]; field_simp

/-- **`HEFIdent` from `ArchLimit` alone (PROVED, conditional).** -/
theorem hefIdent_of_archLimit' (hL : GppRegularitySplit.ArchLimit) : HEFIdent :=
  GppRegularitySplit.hefIdent_of_archLimit hL (archMatch_of_archLimit hL)

/-- The fine chain with `Regularity` and `ArchMatch` both reduced to `ArchLimit`. -/
def HPsiArchLimitChain : Prop :=
  GppKreinHPsi.HPsi → GppRegularitySplit.ArchLimit → KreinDecomp →
    GppSpectralMatchingSplit.IdentityStep → RiemannHypothesis

theorem hPsiArchLimitChain : HPsiArchLimitChain := fun h hL hD hI =>
  hPsiRegArchChain h (GppRegularitySplit.regularity_of_archLimit hL) (archMatch_of_archLimit hL)
    hD hI

end GppArchMatchSplit
#print axioms GppArchMatchSplit.dig_bound
#print axioms GppArchMatchSplit.not_neg_nat
#print axioms GppArchMatchSplit.dig_continuous
#print axioms GppArchMatchSplit.dig_neg
#print axioms GppArchMatchSplit.hline_gd'
#print axioms GppArchMatchSplit.bigPsi_eq
#print axioms GppArchMatchSplit.hline_gd
#print axioms GppArchMatchSplit.bigPsi_neg
#print axioms GppArchMatchSplit.bigPsi_measurable
#print axioms GppArchMatchSplit.norm_hline_gd_le
#print axioms GppArchMatchSplit.ae_ne_zero
#print axioms GppArchMatchSplit.bound_pt
#print axioms GppArchMatchSplit.hline_gd_aesm
#print axioms GppArchMatchSplit.integrable_hline_gd_mul
#print axioms GppArchMatchSplit.tendsto_hline_mul
#print axioms GppArchMatchSplit.archId_gd
#print axioms GppArchMatchSplit.integral_hline_gd
#print axioms GppArchMatchSplit.archF_abs
#print axioms GppArchMatchSplit.archMatch_of_archLimit
#print axioms GppArchMatchSplit.hefIdent_of_archLimit'
#print axioms GppArchMatchSplit.hPsiArchLimitChain
