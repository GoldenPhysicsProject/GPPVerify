/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6824324169 / 6824338259, item 2.

# `NoRealZeroStrip` PROVED: `ζ(σ) ≠ 0` for real `0 < σ < 1`

`KreinHPsiChain.lean` carried `NoRealZeroStrip` as a named premise. It is discharged here from
Mathlib alone, so the chain's remaining premises are `HPsi` and the two split props `HEF`,
`KreinRep` of `KreinPoleSplit.lean`.

**Route (theta–Mellin, not η).** The η route needs the continuation of the conditionally
convergent series `Σ (−1)^{n−1} n^{−s}` to `Re s > 0`, which Mathlib does not have. Instead we
use Mathlib's own definition of `ζ`: `completedRiemannZeta s = Λ(s/2)/2` for the weak FE-pair
`hurwitzEvenFEPair 0` (`f = θ`, `θ(t) = Σ_{n∈ℤ} e^{−πn²t}`, `f₀ = g₀ = ε = 1`, `k = 1/2`), with
`Λ(u) = Λ₀(u) − 1/u − 1/(1/2 − u)` and `Λ₀ = mellin f_modif`. For `0 < u < 1/2`,
`1/u = ∫₀¹ t^{u−1} dt` and `1/(1/2 − u) = ∫₁^∞ t^{u−3/2} dt`, so

  `Λ(u) = ∫₀^∞ t^{u−1} (θ(t) − 1 − t^{−1/2}) dt`   (`integral_ig`, `completedRiemannZeta_ofReal`).

The bracket is strictly negative for every `t > 0` (`theta_lt`): `θ(t) = 1 + 2 Σ_{n≥1} e^{−πn²t}`
and `Σ_{n≥1} e^{−πn²t} < ∫₀^∞ e^{−πx²t} dx = t^{−1/2}/2` (strict sum–integral comparison for a
decreasing Gaussian, `tsum_g_lt`). Hence `completedRiemannZeta σ` is a negative real
(`completedRiemannZeta_neg`), and `ζ(σ) = completedRiemannZeta σ / Γ_ℝ(σ) ≠ 0`
(`riemannZeta_ne_zero_of_real_strip`). No zero of `ζ` is used as input.

Labels: every theorem below is **PROVED** (standard three axioms). Consequences:
`riemannHypothesis_of_hPsi_poleTransfer : HPsi → PoleTransfer → RiemannHypothesis` and
`hPsiReducedChain : HPsi → HEF → KreinRep → RiemannHypothesis` (conditional, PROVED).
H_ψ: OPEN. `HEF`, `KreinRep`: named premises (NOT proved). ARP: OPEN. RH: OPEN.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import GppVerify.RiemannHypothesis.KreinPoleSplit

namespace GppNoRealZeroStrip

open Real MeasureTheory Set Filter HurwitzZeta

/-! ## 1. Strict sum–integral comparison for the Gaussian, and `θ(t) < 1 + t^{−1/2}` -/

/-- Gaussian `g_b(x) = exp(-b x²)`. -/
noncomputable def g (b x : ℝ) : ℝ := rexp (-b * x ^ 2)

lemma g_pos (b x : ℝ) : 0 < g b x := exp_pos _

lemma g_antitoneOn {b : ℝ} (hb : 0 < b) : AntitoneOn (g b) (Ici 0) := by
  intro x hx y hy hxy
  unfold g
  apply exp_le_exp.2
  have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  nlinarith

lemma g_integrable {b : ℝ} (hb : 0 < b) : Integrable (g b) := integrable_exp_neg_mul_sq hb

/-- `Σ_{n ≥ 1} g(n) < ∫_0^∞ g` (strict sum–integral comparison). -/
lemma tsum_g_lt {b : ℝ} (hb : 0 < b) :
    HasSum (fun n : ℕ => g b ((n : ℝ) + 1)) (∑' n : ℕ, g b ((n : ℝ) + 1)) ∧
    ∑' n : ℕ, g b ((n : ℝ) + 1) < ∫ x in Ioi (0 : ℝ), g b x := by
  set J := ∫ x in Ioi (1 : ℝ), g b x
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, g b ((i : ℝ) + 2) ≤ J := by
    intro N
    have h1 := AntitoneOn.sum_le_integral (x₀ := 1) (a := N) (f := g b)
      ((g_antitoneOn hb).mono (fun x hx => le_trans zero_le_one hx.1))
    have h2 : ∫ x in (1 : ℝ)..1 + N, g b x ≤ J := by
      rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])]
      exact setIntegral_mono_set (g_integrable hb).integrableOn
        (Eventually.of_forall fun x => (g_pos b x).le)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    refine le_trans (le_of_eq ?_) (h1.trans h2)
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; push_cast; ring
  have hs2 : Summable (fun n : ℕ => g b ((n : ℝ) + 2)) :=
    summable_of_sum_range_le (fun n => (g_pos b _).le) hpart
  have hs1 : Summable (fun n : ℕ => g b ((n : ℝ) + 1)) := by
    rw [← summable_nat_add_iff 1]
    refine hs2.congr fun n => ?_
    congr 1; push_cast; ring
  refine ⟨hs1.hasSum, ?_⟩
  have hsplit : ∑' n : ℕ, g b ((n : ℝ) + 1) = g b 1 + ∑' n : ℕ, g b ((n : ℝ) + 2) := by
    rw [hs1.tsum_eq_zero_add]
    congr 1
    · simp
    · congr 1; ext n; congr 1; push_cast; ring
  have htail : ∑' n : ℕ, g b ((n : ℝ) + 2) ≤ J :=
    Real.tsum_le_of_sum_range_le (fun n => (g_pos b _).le) hpart
  have hfirst : g b 1 < ∫ x in (0 : ℝ)..1, g b x := by
    have hpos : 0 < ∫ x in (0 : ℝ)..1, (g b x - g b 1) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
      · exact (g_integrable hb).intervalIntegrable.sub intervalIntegrable_const
      · intro x hx
        unfold g
        rw [sub_pos]
        apply exp_lt_exp.2
        have : x ^ 2 < 1 ^ 2 := pow_lt_pow_left₀ hx.2 hx.1.le two_ne_zero
        nlinarith
      · exact zero_lt_one
    rw [intervalIntegral.integral_sub (g_integrable hb).intervalIntegrable
      intervalIntegrable_const, intervalIntegral.integral_const] at hpos
    simp at hpos
    linarith
  have hadd := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := 1) (μ := volume)
    (g_integrable hb).integrableOn (g_integrable hb).integrableOn
  rw [hsplit, ← hadd]
  linarith


/-- `θ(t) < 1 + t^{-1/2}` for `t > 0`, where `θ = evenKernel 0`. -/
lemma theta_lt {t : ℝ} (ht : 0 < t) : evenKernel 0 t < 1 + t ^ (-(1 / 2 : ℝ)) := by
  have hb : 0 < π * t := mul_pos pi_pos ht
  have h1 := (hasSum_int_evenKernel 0 ht).nat_add_neg
  have h2 : HasSum (fun n : ℕ => 2 * g (π * t) n) (evenKernel 0 t + 1) := by
    convert h1 using 1
    · ext n; simp [g]; ring_nf
    · simp
  have h3 : HasSum (fun n : ℕ => g (π * t) n) ((evenKernel 0 t + 1) / 2) := by
    simpa [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] using h2.div_const 2
  rw [← hasSum_nat_add_iff' 1] at h3
  obtain ⟨hS, hlt⟩ := tsum_g_lt hb
  have hcast : (fun n : ℕ => g (π * t) ((n + 1 : ℕ) : ℝ)) = fun n : ℕ => g (π * t) ((n : ℝ) + 1) := by
    ext n; push_cast; rfl
  rw [hcast] at h3
  have heq := h3.unique hS
  rw [Finset.sum_range_one, Nat.cast_zero] at heq
  have hg0 : g (π * t) 0 = 1 := by simp [g]
  have hI : ∫ x in Ioi (0 : ℝ), g (π * t) x = t ^ (-(1 / 2 : ℝ)) / 2 := by
    unfold g
    rw [integral_gaussian_Ioi, div_mul_cancel_left₀ pi_ne_zero, sqrt_eq_rpow, one_div,
      inv_rpow ht.le, rpow_neg ht.le]
  rw [hI] at hlt
  linarith


/-! ## 2. Mathlib's `completedRiemannZeta` on `(0, 1)` as a negative Mellin integral -/

/-- The even FE-pair at `a = 0` (Mathlib). -/
noncomputable abbrev P0 : WeakFEPair ℂ := hurwitzEvenFEPair 0

lemma P_f : P0.f = ((↑) : ℝ → ℂ) ∘ evenKernel 0 := rfl
lemma P_f₀ : P0.f₀ = 1 := by simp [P0, hurwitzEvenFEPair]
lemma P_g₀ : P0.g₀ = 1 := rfl
lemma P_ε : P0.ε = 1 := rfl
lemma P_k : P0.k = 1 / 2 := rfl

/-- Real form of the modified kernel. -/
noncomputable def fm (t : ℝ) : ℝ :=
  (Ioi 1).indicator (fun x => evenKernel 0 x - 1) t +
  (Ioo 0 1).indicator (fun x => evenKernel 0 x - x ^ (-(1 / 2 : ℝ))) t

lemma f_modif_eq (t : ℝ) : P0.f_modif t = (fm t : ℂ) := by
  simp only [WeakFEPair.f_modif, Pi.add_apply, fm, P_f, P_f₀, P_g₀, P_ε, P_k]
  by_cases h1 : t ∈ Ioi 1 <;> by_cases h2 : t ∈ Ioo 0 1 <;> simp [h1, h2]


lemma mellinConvergent_f_modif (s : ℂ) : MellinConvergent P0.f_modif s := by
  have hP := P0.isStrongFEPair_toStrongFEPair
  exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    P0.toStrongFEPair.hf_int (hP.hf_top _) (by linarith) (hP.hf_zero _) (by linarith)

lemma cpow_smul_eq {u t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ ((u : ℂ) - 1) • P0.f_modif t = ((t ^ (u - 1) * fm t : ℝ) : ℂ) := by
  rw [f_modif_eq, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht.le]
  push_cast; rfl

lemma integrableOn_fm (u : ℝ) : IntegrableOn (fun t => t ^ (u - 1) * fm t) (Ioi 0) := by
  have h := (mellinConvergent_f_modif (u : ℂ))
  unfold MellinConvergent at h
  have h' : IntegrableOn (fun t : ℝ => ((t ^ (u - 1) * fm t : ℝ) : ℂ)) (Ioi 0) :=
    h.congr_fun (fun t ht => cpow_smul_eq ht) measurableSet_Ioi
  exact h'.re

lemma Λ₀_eq_real (u : ℝ) : P0.Λ₀ u = ((∫ t in Ioi 0, t ^ (u - 1) * fm t : ℝ) : ℂ) := by
  rw [WeakFEPair.Λ₀, mellin, ← integral_complex_ofReal]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => cpow_smul_eq ht)


/-- `h(t) = θ(t) − 1 − t^{−1/2}`, strictly negative on `t > 0` (`theta_lt`). -/
noncomputable def hR (t : ℝ) : ℝ := evenKernel 0 t - 1 - t ^ (-(1 / 2 : ℝ))

lemma hR_neg {t : ℝ} (ht : 0 < t) : hR t < 0 := by
  have := theta_lt ht; unfold hR; linarith

/-- The integrand `t^{u−1}·(f_modif − 1_{(0,1)} − 1_{(1,∞)} t^{−1/2})`. -/
noncomputable def ig (u t : ℝ) : ℝ :=
  t ^ (u - 1) * fm t - (Ioo 0 1).indicator (fun t => t ^ (u - 1)) t
    - (Ioi 1).indicator (fun t => t ^ (u - 1 - 1 / 2)) t

lemma ig_eq {u t : ℝ} (ht : 0 < t) (h1 : t ≠ 1) : ig u t = t ^ (u - 1) * hR t := by
  rcases lt_or_gt_of_ne h1 with h | h
  · have hm : t ∈ Ioo 0 1 := ⟨ht, h⟩
    have hn : t ∉ Ioi 1 := fun h' => absurd (h'.trans h) (lt_irrefl _)
    simp only [ig, fm, hR, indicator_of_mem hm, indicator_of_notMem hn]
    ring
  · have hm : t ∈ Ioi 1 := h
    have hn : t ∉ Ioo 0 1 := fun h' => absurd (h'.2.trans h) (lt_irrefl _)
    simp only [ig, fm, hR, indicator_of_mem hm, indicator_of_notMem hn]
    rw [sub_eq_add_neg (u - 1), rpow_add ht]
    ring

lemma ig_one (u : ℝ) : ig u 1 = 0 := by
  simp [ig, fm]

lemma integral_ig {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2) :
    ∫ t in Ioi 0, ig u t = (∫ t in Ioi 0, t ^ (u - 1) * fm t) - 1 / u - 1 / (1 / 2 - u) := by
  have hI1 : IntegrableOn (fun t : ℝ => t ^ (u - 1)) (Ioo 0 1) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)).1).mono_set
      Ioo_subset_Ioc_self
  have hI2 : IntegrableOn (fun t : ℝ => t ^ (u - 1 - 1 / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hA1 : IntegrableOn ((Ioo 0 1).indicator (fun t : ℝ => t ^ (u - 1))) (Ioi 0) :=
    (hI1.integrable_indicator measurableSet_Ioo).integrableOn
  have hA2 : IntegrableOn ((Ioi 1).indicator (fun t : ℝ => t ^ (u - 1 - 1 / 2))) (Ioi 0) :=
    (hI2.integrable_indicator measurableSet_Ioi).integrableOn
  have e1 : ∫ t in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => t ^ (u - 1)) t = 1 / u := by
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith))]
    simp [zero_rpow hu0.ne']
  have e2 : ∫ t in Ioi 0, (Ioi 1).indicator (fun t : ℝ => t ^ (u - 1 - 1 / 2)) t
      = 1 / (1 / 2 - u) := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one),
      integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, one_rpow,
      show u - 1 - 1 / 2 + 1 = -(1 / 2 - u) by ring, div_neg, neg_div, neg_neg]
  have h12 : IntegrableOn (fun t => t ^ (u - 1) * fm t
      - (Ioo 0 1).indicator (fun t : ℝ => t ^ (u - 1)) t) (Ioi 0) := (integrableOn_fm u).sub hA1
  unfold ig
  rw [integral_sub h12 hA2, integral_sub (integrableOn_fm u) hA1, e1, e2]

lemma integral_ig_neg {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2) :
    ∫ t in Ioi 0, ig u t < 0 := by
  have hint : IntegrableOn (ig u) (Ioi 0) := by
    have hI1 : IntegrableOn (fun t : ℝ => t ^ (u - 1)) (Ioo 0 1) :=
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)).1).mono_set
        Ioo_subset_Ioc_self
    have hI2 : IntegrableOn (fun t : ℝ => t ^ (u - 1 - 1 / 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    exact ((integrableOn_fm u).sub (hI1.integrable_indicator measurableSet_Ioo).integrableOn).sub
      (hI2.integrable_indicator measurableSet_Ioi).integrableOn
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ -ig u t := by
    intro t ht
    by_cases h1 : t = 1
    · simp [h1, ig_one]
    · rw [ig_eq ht h1]
      have := hR_neg ht
      have := rpow_pos_of_pos (show (0 : ℝ) < t from ht) (u - 1)
      nlinarith
  have hpos : 0 < ∫ t in Ioi 0, -ig u t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi hnn)
      hint.neg]
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi 1) ?_)
    · simp [Real.volume_Ioi]
    · intro t ht
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      refine ⟨?_, ht0⟩
      rw [Function.mem_support, ig_eq ht0 (ne_of_gt ht)]
      have := hR_neg ht0
      have := rpow_pos_of_pos ht0 (u - 1)
      intro h
      have : t ^ (u - 1) * hR t < 0 := mul_neg_of_pos_of_neg (by assumption) (by assumption)
      linarith
  rw [integral_neg] at hpos
  linarith


lemma completedRiemannZeta_ofReal {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    completedRiemannZeta σ = (((∫ t in Ioi 0, ig (σ / 2) t) / 2 : ℝ) : ℂ) := by
  have hc : (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) := by push_cast; ring
  have hu0 : 0 < σ / 2 := by linarith
  have hu1 : σ / 2 < 1 / 2 := by linarith
  rw [completedRiemannZeta, completedHurwitzZetaEven, hc]
  change P0.Λ _ / 2 = _
  rw [WeakFEPair.Λ, Λ₀_eq_real, integral_ig hu0 hu1, P_f₀, P_g₀, P_ε, P_k]
  push_cast
  simp only [smul_eq_mul, mul_one]

/-- **`NoRealZeroStrip` content.** For real `0 < σ < 1`, `completedRiemannZeta σ` is a negative
real number. -/
lemma completedRiemannZeta_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    completedRiemannZeta σ = (((∫ t in Ioi 0, ig (σ / 2) t) / 2 : ℝ) : ℂ) ∧
      (∫ t in Ioi 0, ig (σ / 2) t) / 2 < 0 :=
  ⟨completedRiemannZeta_ofReal h0 h1, by
    have := integral_ig_neg (u := σ / 2) (by linarith) (by linarith); linarith⟩

theorem riemannZeta_ne_zero_of_real_strip {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  obtain ⟨he, hneg⟩ := completedRiemannZeta_neg h0 h1
  have hs0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0.ne'
  rw [riemannZeta_def_of_ne_zero hs0, he]
  refine div_ne_zero ?_ (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using h0))
  exact Complex.ofReal_ne_zero.2 hneg.ne

/-! ## 3. Consequences for the H_ψ chain (PROVED, conditional on the named premises) -/

open GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit

/-- **`NoRealZeroStrip` PROVED** (was a named premise of `hPsiChain`). -/
theorem noRealZeroStrip : NoRealZeroStrip := fun _ h0 h1 => riemannZeta_ne_zero_of_real_strip h0 h1

/-- The chain with `NoRealZeroStrip` discharged: `H_ψ` + pole transfer ⇒ `RiemannHypothesis`. -/
theorem riemannHypothesis_of_hPsi_poleTransfer (h : HPsi) (hPT : PoleTransfer) :
    RiemannHypothesis :=
  riemannHypothesis_of_hPsi h hPT noRealZeroStrip

/-- The split chain with `NoRealZeroStrip` discharged: premises `HPsi`, `HEF`, `KreinRep` only. -/
def HPsiReducedChain : Prop := HPsi → HEF → KreinRep → RiemannHypothesis

theorem hPsiReducedChain : HPsiReducedChain := fun h hE hK =>
  riemannHypothesis_of_split h hE hK noRealZeroStrip

end GppNoRealZeroStrip

#print axioms GppNoRealZeroStrip.tsum_g_lt
#print axioms GppNoRealZeroStrip.theta_lt
#print axioms GppNoRealZeroStrip.integral_ig
#print axioms GppNoRealZeroStrip.integral_ig_neg
#print axioms GppNoRealZeroStrip.completedRiemannZeta_neg
#print axioms GppNoRealZeroStrip.riemannZeta_ne_zero_of_real_strip
#print axioms GppNoRealZeroStrip.noRealZeroStrip
#print axioms GppNoRealZeroStrip.riemannHypothesis_of_hPsi_poleTransfer
#print axioms GppNoRealZeroStrip.hPsiReducedChain
