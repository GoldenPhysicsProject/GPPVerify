/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convolution
import GppVerify.RiemannHypothesis.HeartLandauReduction

/-!
# F13, spread-average (moving-average) variant

**Conditional implication, RH-strength hypothesis; nothing here proves RH, and this is a
transfer statement, not a positivity proof.**

For a bounded nonnegative measurable kernel `k` supported in `[0, w]` whose Laplace transform
`κ̂(z) = ∫ e^{-zu} k(u) du` has no zero on the strip `ε < Re z < ½` (the only strip the argument
uses: a zero `ρ` of `ξ` has `Re(ρ−½) < ½`, and `Re ≥ 1` is handled by `ζ ≠ 0`, see
`xiE_ne_zero_of_one_le_re`), let
`(k ⋆ D)(L) = ∫ k(u) D(L − u) du` (`conv`, with `D` extended by `0` below `0`, `Dz`).
If `(k ⋆ D)(L) ≥ −C e^{εL}` for all `L > 0` (`0 ≤ ε < ½`), then the entire completed zeta `ξ_E`
has no zero with `Re s > ½ + ε` (`F13_spread_xiE_ne_zero`), and `riemannZeta` has none off
`s = 1` (`F13_spread_riemannZeta_ne_zero`).

Route: `L[k ⋆ D] = κ̂ · L[D]` (Mathlib `integral_convolution`), so with `h = k ⋆ D + C e^{εt}`
the F11 identity gives `κ̂(z) ξ′(½+z) = ξ(½+z) z² (L[h](z) − C/(z−ε))`; `κ̂ ≠ 0` lets the F13
order-comparison and Landau step go through unchanged.

Concrete instances:
* uniform kernel `k = 1_{[0,w]}` (`F13_uniform_xiE_ne_zero`, `F13_uniform_riemannZeta_ne_zero`):
  `κ̂(z) = (1 − e^{−wz})/z` (`momentLap_kU_mul`), nonzero on `Re z > 0` (`momentLap_kU_ne_zero`);
  the hypothesis becomes `∫_{L−w}^{L} D ≥ −C e^{εL}`.
* For the spread-weight kernel `k(u) = eᵘ` on `[0,w]`, the transform away from `z = 1` is `(1 − e^{−(z−1)w})/(z−1)` (`momentLap_kE_mul`). At `z = 1` its value is `w`. For positive `w` its zeros are `1 + 2πin/w` for nonzero integers `n`. The choice `w = log 2` gives Alpöge’s spread window (`F13_expKernel_xiE_ne_zero`, `F13_expKernel_riemannZeta_ne_zero`).

At `w = log 2`, let `U(z)` and `E(z)` be these two transforms. On `0 < Re z < 1`, their product satisfies `z(1 − z) U(z) E(z) = (1 − 2^(−z))(2^(1−z) − 1)`. The right-hand side is the [multiplier for the dyadic difference](https://github.com/leecrossley/dirichlet-window-transfer/blob/fa94718cf9d65ee5b143ded4c91dc3873222cfdf/PROOF.md#L14-L18).

For the convolution `K` of the two kernels at this width, integrate `exp(v)` from `max(0, x − w)` to `min(w, x)` wherever the interval has positive length. With `x = log t`, this gives `2 K(log t) / t = 2(1 − 1/t)` for `1 < t ≤ 2` and `4/t − 1` for `2 < t < 4`. The weight vanishes for `0 < t ≤ 1` and `t ≥ 4`.

**Normalisation choice.** `D` is the continuous-time Round 23 function, and the window is a
continuous moving average. This is **not** the discrete `m`-point average over `log n` nodes;
that form needs a separate Riemann-sum/Lipschitz step and is not claimed here. The converse
(zero-free half-plane ⇒ the averaged floor) is not proved.
-/


open MeasureTheory Set Filter Topology Complex Convolution
open GppHeartLaplace (Dfun)
open RhWaveLean (momentLap hasDerivAt_momentLap aesm_h)
open GppHeartReduction (xiE LapInt lapInt_mono)

namespace GppSpreadAverage

/-- `D` extended by `0` below `0` (continuous because `D(0) = 0`). -/
noncomputable def Dz (t : ℝ) : ℝ := Dfun (max t 0)

theorem continuousOn_Dfun : ContinuousOn Dfun (Ici 0) := by
  have hT := GppHeartLaplace.continuousOn_Tfun
  have hS := (GppHeartRound23.HR23_S_continuous).continuousOn (s := Ici (0 : ℝ))
  unfold Dfun
  refine ((ContinuousOn.sub ?_ hT).sub hS)
  · have : Continuous fun L : ℝ => 4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2))
        + GppHeartLaplace.c1 * L + GppHeartLaplace.C2 := by fun_prop
    exact this.continuousOn

theorem continuous_Dz : Continuous Dz := by
  unfold Dz
  exact continuousOn_Dfun.comp_continuous (by fun_prop) (fun t => le_max_right t 0)

theorem Dz_of_nonpos {t : ℝ} (ht : t ≤ 0) : Dz t = 0 := by
  unfold Dz; rw [max_eq_right ht]; exact GppHeartLaplace.Dfun_zero

theorem Dz_of_pos {t : ℝ} (ht : 0 < t) : Dz t = Dfun t := by
  unfold Dz; rw [max_eq_left ht.le]

/-- Moving average of `D` against a kernel `k`: `(k ⋆ D)(L) = ∫ k(u) D(L − u) du`. -/
noncomputable def conv (k : ℝ → ℝ) (L : ℝ) : ℝ := ∫ u, k u * Dz (L - u)

theorem conv_eq (k : ℝ → ℝ) :
    conv k = k ⋆[ContinuousLinearMap.mul ℝ ℝ] Dz := by
  funext L
  simp [conv, convolution]


/-- Kernel data: measurable, bounded, supported on `[0,w]`. -/
structure KernelSpec (k : ℝ → ℝ) (w K : ℝ) : Prop where
  meas : Measurable k
  nonneg : ∀ u, 0 ≤ k u
  supp : ∀ u, u ∉ Icc 0 w → k u = 0
  bdd : ∀ u, |k u| ≤ K

theorem KernelSpec.neg_of_lt {k : ℝ → ℝ} {w K : ℝ} (hk : KernelSpec k w K) {u : ℝ} (hu : u < 0) :
    k u = 0 := hk.supp u (fun h => absurd h.1 (not_le.mpr hu))

theorem KernelSpec.integrable {k : ℝ → ℝ} {w K : ℝ} (hk : KernelSpec k w K) (σ : ℝ) :
    Integrable (fun u => Real.exp (-σ * u) * k u) := by
  have hmeas : Measurable fun u : ℝ => Real.exp (-σ * u) * k u :=
    (by fun_prop : Measurable fun u : ℝ => Real.exp (-σ * u)).mul hk.meas
  have hint : Integrable ((Icc (0 : ℝ) w).indicator fun _ => Real.exp (|σ| * w) * K) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp)
  refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ Icc (0 : ℝ) w
  · rw [Set.indicator_of_mem hu]
    have hK : 0 ≤ K := (abs_nonneg _).trans (hk.bdd u)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul ?_ (hk.bdd u) (abs_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    have h1 : -σ * u ≤ |σ| * w := by
      calc -σ * u ≤ |-σ * u| := le_abs_self _
        _ = |σ| * |u| := by rw [abs_mul, abs_neg]
        _ ≤ |σ| * w := mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hu.1]; exact hu.2) (abs_nonneg _)
    exact h1
  · rw [Set.indicator_of_notMem hu, hk.supp u hu]; simp

/-- Weighted convolution identity: `e^{−σt}(k ⋆ D)(t) = ((e^{−σ·}k) ⋆ (e^{−σ·}D))(t)`. -/
theorem exp_mul_conv (k : ℝ → ℝ) (σ t : ℝ) :
    Real.exp (-σ * t) * conv k t =
      ((fun u => Real.exp (-σ * u) * k u) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (fun s => Real.exp (-σ * s) * Dz s)) t := by
  simp only [conv, convolution, ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have : Real.exp (-σ * t) = Real.exp (-σ * u) * Real.exp (-σ * (t - u)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [this]; ring


theorem integrable_expDz {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (fun s : ℝ => Real.exp (-σ * s) * Dz s) := by
  have h1 : (fun s : ℝ => Real.exp (-σ * s) * Dz s)
      = (Ioi (0 : ℝ)).indicator (fun s => Real.exp (-σ * s) * Dfun s) := by
    funext s
    by_cases hs : 0 < s
    · rw [Set.indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), Dz_of_pos hs]
    · rw [Set.indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs), Dz_of_nonpos (not_lt.mp hs)]
      simp
  rw [h1, integrable_indicator_iff measurableSet_Ioi]
  exact GppHeartReduction.integrableOn_D hσ


theorem conv_nonpos {k : ℝ → ℝ} {w K : ℝ} (hk : KernelSpec k w K) {t : ℝ} (ht : t ≤ 0) :
    conv k t = 0 := by
  unfold conv
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : u < 0
  · simp [hk.neg_of_lt hu]
  · have : t - u ≤ 0 := by linarith [not_lt.mp hu]
    simp [Dz_of_nonpos this]

/-- **Laplace transform of the moving average** (real `σ > ½`):
`∫₀^∞ e^{−σt}(k ⋆ D)(t) dt = κ̂(σ) · L[D](σ)`, with `κ̂(σ) = ∫ e^{−σu}k(u) du`. -/
theorem laplace_conv {k : ℝ → ℝ} {w K : ℝ} (hk : KernelSpec k w K) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * conv k t
      = (∫ u, Real.exp (-σ * u) * k u) * ∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * Dfun t := by
  have h0 : ∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * conv k t
      = ∫ t, Real.exp (-σ * t) * conv k t := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)
    have : t ≤ 0 := not_lt.mp ht
    simp [conv_nonpos hk this]
  rw [h0]
  simp_rw [exp_mul_conv]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) (hk.integrable σ) (integrable_expDz hσ)]
  simp only [ContinuousLinearMap.mul_apply']
  congr 1
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))]
  · exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => by rw [Dz_of_pos hs])
  · intro s hs
    simp [Dz_of_nonpos (not_lt.mp hs)]


/-! ### Abstract core with a kernel factor `κ` -/

section Core

variable {h : ℝ → ℝ} {κ : ℂ → ℂ} {ε C σc : ℝ}

/-- `L[h](σ) = κ(σ)·(ξ′/ξ)(½+σ)/σ² + C/(σ−ε)` for real `σ > ½`. -/
def MatchesXiK (h : ℝ → ℝ) (κ : ℂ → ℂ) (ε C : ℝ) : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → momentLap h 0 (σ : ℂ)
    = κ (σ : ℂ) * (logDeriv xiE (((1 / 2 + σ : ℝ)) : ℂ) / (σ : ℂ) ^ 2) + (C : ℂ) / ((σ : ℂ) - ε)

theorem W_differentiableOn' (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hεσ : ε ≤ σc) :
    DifferentiableOn ℂ (fun z : ℂ => z ^ 2 * (momentLap h 0 z - (C : ℂ) / (z - ε)))
      {z : ℂ | σc < z.re} :=
  GppHeartReduction.W_differentiableOn hpos hconv hεσ

theorem xiE_deriv_eq_mulK (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hκd : Differentiable ℂ κ) (hT : MatchesXiK h κ ε C) (hεσ : ε ≤ σc) (hσc : σc ≤ 1 / 2) :
    ∀ z : ℂ, σc < z.re →
      κ z * deriv xiE (1 / 2 + z)
        = xiE (1 / 2 + z) * (z ^ 2 * (momentLap h 0 z - (C : ℂ) / (z - ε))) := by
  set H : Set ℂ := {z : ℂ | σc < z.re} with hH
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHpre : IsPreconnected H := (convex_halfSpace_re_gt σc).isPreconnected
  set W : ℂ → ℂ := fun z => z ^ 2 * (momentLap h 0 z - (C : ℂ) / (z - ε)) with hW
  have hWd : DifferentiableOn ℂ W H := GppHeartReduction.W_differentiableOn hpos hconv hεσ
  have hdx : Differentiable ℂ (deriv xiE) := fun z =>
    (GppHeartReduction.differentiable_xiE.analyticAt z).deriv.differentiableAt
  set f : ℂ → ℂ := fun z => κ z * deriv xiE (1 / 2 + z) - xiE (1 / 2 + z) * W z with hf
  have hfd : DifferentiableOn ℂ f H := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => deriv xiE (1 / 2 + z)) z :=
      (hdx (1 / 2 + z)).comp z (differentiableAt_const _ |>.add differentiableAt_id)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => xiE (1 / 2 + z)) z :=
      (GppHeartReduction.differentiable_xiE (1 / 2 + z)).comp z
        (differentiableAt_const _ |>.add differentiableAt_id)
    exact ((hκd z).differentiableWithinAt.mul h1.differentiableWithinAt).sub
      (h2.differentiableWithinAt.mul (hWd z hz))
  have hfa : AnalyticOnNhd ℂ f H := hfd.analyticOnNhd hHopen
  have hzero : ∀ σ : ℝ, 1 / 2 < σ → f (σ : ℂ) = 0 := by
    intro σ hσ
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : σ ≠ 0)
    have hx : xiE (1 / 2 + (σ : ℂ)) ≠ 0 := by
      have := GppHeartReduction.xiE_real_ne_zero (x := 1 / 2 + σ) (by linarith)
      simpa using this
    have hm := hT σ hσ
    have hlog : logDeriv xiE (((1 / 2 + σ : ℝ)) : ℂ)
        = deriv xiE (1 / 2 + (σ : ℂ)) / xiE (1 / 2 + (σ : ℂ)) := by
      rw [logDeriv_apply]; push_cast; rfl
    have hT' : momentLap h 0 (σ : ℂ) - (C : ℂ) / ((σ : ℂ) - ε)
        = κ (σ : ℂ) * (deriv xiE (1 / 2 + (σ : ℂ)) / xiE (1 / 2 + (σ : ℂ)) / (σ : ℂ) ^ 2) := by
      rw [hm, hlog]; ring
    simp only [hf, hW]
    rw [hT']
    generalize deriv xiE (1 / 2 + (σ : ℂ)) = D at *
    generalize xiE (1 / 2 + (σ : ℂ)) = X at *
    field_simp
    ring
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), f z = 0 := by
    have h1 : ∀ᶠ r : ℝ in 𝓝[≠] (1 : ℝ), f (r : ℂ) = 0 := by
      have : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), 1 / 2 < r := lt_mem_nhds (by norm_num)
      exact eventually_nhdsWithin_of_eventually_nhds (this.mono fun r hr => hzero r hr)
    have h2 : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    exact (h2.frequently h1.frequently)
  have h1H : (1 : ℂ) ∈ H := by
    show σc < (1 : ℂ).re
    simp; linarith
  have hEq := hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero hHpre h1H hfreq
  intro z hz
  have := hEq hz
  simp only [hf, Pi.zero_apply] at this
  exact sub_eq_zero.mp this


/-- `ξ_E` has no zero on `Re s ≥ 1` (`ξ_E(1) = ½`; `ζ ≠ 0` on `Re s ≥ 1`). -/
theorem xiE_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xiE s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1; simp [GppHeartReduction.xiE_one]
  have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; simp at hs; linarith
  rw [GppHeartReduction.xiE_eq hs0 h1]
  have hz := riemannZeta_ne_zero_of_one_le_re hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h0
    apply hz
    rw [riemannZeta_def_of_ne_zero hs0, h0, zero_div]
  have h2 : (2 : ℂ)⁻¹ ≠ 0 := by norm_num
  have : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  simp only [one_div]
  exact mul_ne_zero (mul_ne_zero h2 hs0 |> fun h => mul_ne_zero h this) hΛ

theorem xiE_ne_zero_onK (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hκd : Differentiable ℂ κ) (hκne : ∀ z : ℂ, ε < z.re → z.re < 1 / 2 → κ z ≠ 0)
    (hT : MatchesXiK h κ ε C) (hεσ : ε ≤ σc) (hσc : σc ≤ 1 / 2) :
    ∀ z : ℂ, σc < z.re → xiE (1 / 2 + z) ≠ 0 := by
  intro z0 hz0 hF0
  by_cases hhalf : 1 / 2 ≤ z0.re
  · exact xiE_ne_zero_of_one_le_re (s := 1 / 2 + z0)
      (by simp only [Complex.add_re]; norm_num; linarith) hF0
  push Not at hhalf
  have hode := xiE_deriv_eq_mulK hpos hconv hκd hT hεσ hσc
  set W : ℂ → ℂ := fun z => z ^ 2 * (momentLap h 0 z - (C : ℂ) / (z - ε)) with hW
  set H : Set ℂ := {z : ℂ | σc < z.re} with hH
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hWa : AnalyticAt ℂ W z0 :=
    (GppHeartReduction.W_differentiableOn (C := C) hpos hconv hεσ).analyticAt (hHopen.mem_nhds hz0)
  set F : ℂ → ℂ := fun z => xiE (1 / 2 + z) with hF
  have hFd : Differentiable ℂ F := fun z =>
    (GppHeartReduction.differentiable_xiE (1 / 2 + z)).comp z
      (differentiableAt_const _ |>.add differentiableAt_id)
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => (hFd.analyticAt z)
  have hFz0 : AnalyticAt ℂ F z0 := hFd.analyticAt z0
  have hne_top : analyticOrderAt F z0 ≠ ⊤ := by
    intro htop
    have hev : ∀ᶠ z in 𝓝 z0, F z = 0 := analyticOrderAt_eq_top.mp htop
    have h0 := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z0) hev
    have h1 : F 1 = 0 := h0 (Set.mem_univ 1)
    have h2 : xiE ((3 / 2 : ℝ) : ℂ) ≠ 0 := GppHeartReduction.xiE_real_ne_zero (by norm_num)
    apply h2
    have : F 1 = xiE ((3 / 2 : ℝ) : ℂ) := by simp only [hF]; norm_num
    rw [← this]; exact h1
  obtain ⟨m, hm⟩ : ∃ m : ℕ, analyticOrderAt F z0 = m := by
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne_top
    exact ⟨m, hm.symm⟩
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, analyticOrderAt_eq_zero] at hm
    rcases hm with h | h
    · exact h hFz0
    · exact h hF0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hord : analyticOrderAt F z0 = (n : ℕ∞) + 1 := by rw [hm]; push_cast; rfl
  have hderiv : analyticOrderAt (deriv F) z0 = n := analyticOrderAt_deriv_of_pos hFz0 hord
  have hκa : AnalyticAt ℂ κ z0 := hκd.analyticAt z0
  have hκ0 : analyticOrderAt κ z0 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (hκne z0 (by have : σc < z0.re := hz0; linarith) hhalf))
  have hev : κ * deriv F =ᶠ[𝓝 z0] F * W := by
    filter_upwards [hHopen.mem_nhds hz0] with z hz
    have hdz : deriv F z = deriv xiE (1 / 2 + z) :=
      deriv_comp_const_add (f := xiE) (a := (1 / 2 : ℂ)) (x := z)
    show κ z * deriv F z = F z * W z
    rw [hdz]
    exact hode z hz
  have hdFa : AnalyticAt ℂ (deriv F) z0 := hFz0.deriv
  have h2 : analyticOrderAt (κ * deriv F) z0 = analyticOrderAt (F * W) z0 :=
    analyticOrderAt_congr hev
  rw [analyticOrderAt_mul hκa hdFa, analyticOrderAt_mul hFz0 hWa, hκ0, hderiv, hord] at h2
  have h3 : ((n : ℕ∞)) ≥ (n : ℕ∞) + 1 := by
    calc (n : ℕ∞) = 0 + (n : ℕ∞) := by simp
      _ = (n : ℕ∞) + 1 + analyticOrderAt W z0 := h2
      _ ≥ (n : ℕ∞) + 1 := le_self_add
  have h4 : ((n : ℕ∞)) < (n : ℕ∞) + 1 := by
    exact ENat.lt_add_one_iff (by simp) |>.mpr le_rfl
  exact absurd h3 (not_le.mpr h4)


/-- **Landau step with a kernel factor.** -/
theorem landau_stepK (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hκd : Differentiable ℂ κ) (hκne : ∀ z : ℂ, ε < z.re → z.re < 1 / 2 → κ z ≠ 0)
    (hT : MatchesXiK h κ ε C) (hε0 : 0 ≤ ε) (hεσ : ε < σc) (hσc : σc ≤ 1 / 2) :
    ∃ y : ℝ, y < σc ∧
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-y * t) * h t : ℝ) : ℂ)) (Ioi 0) volume := by
  have hode := xiE_deriv_eq_mulK hpos hconv hκd hT hεσ.le hσc
  have hz := xiE_ne_zero_onK hpos hconv hκd hκne hT hεσ.le hσc
  have hxσ : xiE (1 / 2 + (σc : ℂ)) ≠ 0 := by
    have := GppHeartReduction.xiE_real_ne_zero (x := 1 / 2 + σc) (by linarith)
    simpa using this
  have hcont : ContinuousAt (fun z : ℂ => xiE (1 / 2 + z)) (σc : ℂ) :=
    (GppHeartReduction.differentiable_xiE (1 / 2 + (σc : ℂ))).continuousAt.comp
      (f := fun z : ℂ => 1 / 2 + z) (continuousAt_const.add continuousAt_id)
  obtain ⟨δ1, hδ1, hball1⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hxσ)
  set δ : ℝ := min δ1 (σc - ε) with hδ
  have hδpos : 0 < δ := lt_min hδ1 (by linarith)
  have hball : ∀ z : ℂ, z ∈ Metric.ball (σc : ℂ) δ →
      xiE (1 / 2 + z) ≠ 0 ∧ ε < z.re := by
    intro z hzb
    rw [Metric.mem_ball] at hzb
    refine ⟨hball1 (lt_of_lt_of_le hzb (min_le_left _ _)), ?_⟩
    have h1 : dist z (σc : ℂ) < σc - ε := lt_of_lt_of_le hzb (min_le_right _ _)
    have h2 : |z.re - σc| ≤ dist z (σc : ℂ) := by
      have := Complex.abs_re_le_norm (z - σc)
      simpa [Complex.dist_eq] using this
    have := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
    linarith
  set Hext : ℂ → ℂ := fun z => κ z * deriv xiE (1 / 2 + z) / (xiE (1 / 2 + z) * z ^ 2)
    + (C : ℂ) / (z - ε) with hHext
  have hgood : ∀ z ∈ Metric.ball (σc : ℂ) δ ∪ {z : ℂ | σc < z.re},
      xiE (1 / 2 + z) ≠ 0 ∧ ε < z.re := by
    intro z hzu
    rcases hzu with hzb | hzH
    · exact hball z hzb
    · exact ⟨hz z hzH, by have : σc < z.re := hzH; linarith⟩
  have hdiff : DifferentiableOn ℂ Hext (Metric.ball (σc : ℂ) δ ∪ {z : ℂ | σc < z.re}) := by
    intro z hzu
    obtain ⟨hx, hre⟩ := hgood z hzu
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0] at hre; simp at hre; linarith
    have hzε : z - (ε : ℂ) ≠ 0 := by
      intro h0
      have : (z - (ε : ℂ)).re = 0 := by rw [h0]; simp
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    have hdx : DifferentiableAt ℂ (deriv xiE) (1 / 2 + z) :=
      (GppHeartReduction.differentiable_xiE.analyticAt _).deriv.differentiableAt
    have h1 : DifferentiableAt ℂ (fun z : ℂ => deriv xiE (1 / 2 + z)) z :=
      hdx.comp z (differentiableAt_const _ |>.add differentiableAt_id)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => xiE (1 / 2 + z)) z :=
      (GppHeartReduction.differentiable_xiE (1 / 2 + z)).comp z
        (differentiableAt_const _ |>.add differentiableAt_id)
    have h3 : DifferentiableAt ℂ Hext z := by
      refine DifferentiableAt.add (((hκd z).mul h1).div (h2.mul (differentiableAt_id.pow 2))
        (mul_ne_zero hx (pow_ne_zero 2 hz0))) ?_
      exact (differentiableAt_const _).div (differentiableAt_id.sub_const _) hzε
    exact h3.differentiableWithinAt
  have heq : ∀ z : ℂ, σc < z.re →
      Hext z = ∫ t : ℝ in Ioi 0, Complex.exp (-z * (t : ℂ)) * ((h t : ℝ) : ℂ) := by
    intro z hzH
    have hre : ε < z.re := by linarith
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0] at hre; simp at hre; linarith
    have hzε : z - (ε : ℂ) ≠ 0 := by
      intro h0
      have : (z - (ε : ℂ)).re = 0 := by rw [h0]; simp
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    have hx := hz z hzH
    have hT0 : momentLap h 0 z = ∫ t : ℝ in Ioi 0, Complex.exp (-z * (t : ℂ)) * ((h t : ℝ) : ℂ) := by
      simp [momentLap]
    rw [← hT0]
    simp only [hHext]
    rw [hode z hzH]
    generalize xiE (1 / 2 + z) = X at *
    field_simp
    ring
  have hlocal := GppHeartLandau.landau_local hpos hδpos hconv hdiff heq
  have hr : 0 < min 1 (δ ^ 2 / 3) := lt_min one_pos (by positivity)
  exact ⟨σc - min 1 (δ ^ 2 / 3) / 2, by linarith, hlocal _ (by linarith)⟩

end Core


/-! ### Instance: the moving average of `D` -/

section Instance

variable {k : ℝ → ℝ} {w K : ℝ}

/-- `κ̂(z) = ∫₀^∞ e^{−zu} k(u) du`, entire because `k` has compact support. -/
theorem differentiable_kappa (hk : KernelSpec k w K) : Differentiable ℂ (momentLap k 0) := by
  intro z0
  have hconv : ∀ τ : ℝ, z0.re - 1 < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * k t : ℝ) : ℂ)) (Ioi 0) volume :=
    fun τ _ => (hk.integrable τ).ofReal.integrableOn
  exact (hasDerivAt_momentLap hk.nonneg hconv 0 (by linarith)).differentiableAt

/-- `κ̂(σ)` for real `σ` is the real integral of `e^{−σu}k(u)` over all of `ℝ`. -/
theorem momentLap_kappa_real (hk : KernelSpec k w K) (σ : ℝ) :
    momentLap k 0 (σ : ℂ) = (((∫ u, Real.exp (-σ * u) * k u : ℝ)) : ℂ) := by
  have hI : ∫ u, Real.exp (-σ * u) * k u = ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * k u := by
    rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic (hk.integrable σ)]
    have h1 : ∫ u in Iic (0 : ℝ), Real.exp (-σ * u) * k u = 0 := by
      rw [← setIntegral_congr_set Iio_ae_eq_Iic]
      exact setIntegral_eq_zero_of_forall_eq_zero (fun u hu => by
        simp [hk.neg_of_lt (show u < 0 from hu)])
    rw [h1, zero_add, compl_Iic]
  rw [hI]
  simp only [momentLap, pow_zero, one_mul]
  have hio := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t : ℝ => Real.exp (-σ * t) * k t)
  refine Eq.trans (setIntegral_congr_fun
    (g := fun t : ℝ => ((Real.exp (-σ * t) * k t : ℝ) : ℂ)) measurableSet_Ioi
    (fun t _ => ?_)) hio
  push_cast
  ring_nf


theorem integrable_expConv (hk : KernelSpec k w K) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (fun t : ℝ => Real.exp (-σ * t) * conv k t) := by
  have := (hk.integrable σ).integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_expDz hσ)
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  exact (exp_mul_conv k σ t).symm

/-- The F11 identity in `ξ_E` form: `∫₀^∞ e^{−σt} D(t) dt = (ξ_E′/ξ_E)(½+σ)/σ²`. -/
theorem laplace_D_xiE {σ : ℝ} (hσ : 1 / 2 < σ) :
    (((∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * Dfun t : ℝ)) : ℂ)
      = logDeriv xiE (((1 / 2 + σ : ℝ)) : ℂ) / (σ : ℂ) ^ 2 := by
  have hF11 := GppHeartLaplace.F11_laplace_identity hσ
  have hxi : logDeriv GppHeartLaplace.xiC (((1 / 2 + σ : ℝ)) : ℂ)
      = logDeriv xiE (((1 / 2 + σ : ℝ)) : ℂ) := by
    have hev : GppHeartLaplace.xiC =ᶠ[𝓝 (((1 / 2 + σ : ℝ)) : ℂ)] xiE := by
      have h0 : ∀ᶠ s : ℂ in 𝓝 (((1 / 2 + σ : ℝ)) : ℂ), s ≠ 0 := isOpen_ne.mem_nhds (by
        push_cast; intro h; have := congrArg Complex.re h; simp at this; linarith)
      have h1 : ∀ᶠ s : ℂ in 𝓝 (((1 / 2 + σ : ℝ)) : ℂ), s ≠ 1 := isOpen_ne.mem_nhds (by
        push_cast; intro h; have := congrArg Complex.re h; simp at this; linarith)
      filter_upwards [h0, h1] with s hs0 hs1
      exact (GppHeartReduction.xiE_eq hs0 hs1).symm
    exact (logDeriv_congr_nhds hev).eq_of_nhds
  rw [hF11, hxi]

/-- `h = k ⋆ D + C e^{εt}` on `t > 0`, `0` elsewhere. -/
noncomputable def hK (k : ℝ → ℝ) (ε C : ℝ) (t : ℝ) : ℝ :=
  if 0 < t then conv k t + C * Real.exp (ε * t) else 0

theorem hK_nonneg {ε C : ℝ} (hD : ∀ L : ℝ, 0 < L → -C * Real.exp (ε * L) ≤ conv k L) (t : ℝ) :
    0 ≤ hK k ε C t := by
  unfold hK
  split_ifs with ht
  · have := hD t ht
    linarith
  · exact le_rfl

theorem integrableOn_hK (hk : KernelSpec k w K) {ε C σ : ℝ} (hσ : 1 / 2 < σ) (hε : ε < 1 / 2) :
    IntegrableOn (fun t : ℝ => ((Real.exp (-σ * t) * hK k ε C t : ℝ) : ℂ)) (Ioi 0) := by
  have h1 := (integrable_expConv hk hσ).integrableOn (s := Ioi (0 : ℝ))
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < σ - ε)).const_mul C
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-σ * t) * hK k ε C t) (Ioi 0) := by
    refine (h1.add h2).congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only [hK, if_pos ht0]
    have : Real.exp (-σ * t) * Real.exp (ε * t) = Real.exp (-(σ - ε) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-σ * t) * conv k t + C * Real.exp (-(σ - ε) * t)
        = Real.exp (-σ * t) * conv k t + C * (Real.exp (-σ * t) * Real.exp (ε * t)) := by rw [this]
      _ = _ := by ring
  exact h3.ofReal

theorem matchesXiK_hK (hk : KernelSpec k w K) {ε C : ℝ} (hε : ε < 1 / 2) :
    MatchesXiK (hK k ε C) (momentLap k 0) ε C := by
  intro σ hσ
  have hσ0 : 0 < σ := by linarith
  have hE : IntegrableOn (fun t : ℝ => C * Real.exp (-(σ - ε) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < σ - ε)).const_mul C
  have hC := (integrable_expConv hk hσ).integrableOn (s := Ioi (0 : ℝ))
  have hreal : (∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * hK k ε C t)
      = (∫ u, Real.exp (-σ * u) * k u) * (∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * Dfun t)
        + C / (σ - ε) := by
    have e1 : (∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * hK k ε C t)
        = ∫ t in Ioi (0 : ℝ), (Real.exp (-σ * t) * conv k t + C * Real.exp (-(σ - ε) * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : 0 < t := ht
      simp only [hK, if_pos ht0]
      have : Real.exp (-σ * t) * Real.exp (ε * t) = Real.exp (-(σ - ε) * t) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (-σ * t) * (conv k t + C * Real.exp (ε * t))
          = Real.exp (-σ * t) * conv k t + C * (Real.exp (-σ * t) * Real.exp (ε * t)) := by ring
        _ = _ := by rw [this]
    rw [e1, integral_add hC hE, integral_const_mul,
      GppHeartLaplace.integral_exp_neg_Ioi_zero' (by linarith : 0 < σ - ε), laplace_conv hk hσ]
    ring
  have hmom : momentLap (hK k ε C) 0 (σ : ℂ)
      = (((∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * hK k ε C t : ℝ)) : ℂ) := by
    simp only [momentLap, pow_zero, one_mul]
    have hio := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun t : ℝ => Real.exp (-σ * t) * hK k ε C t)
    refine Eq.trans (setIntegral_congr_fun
      (g := fun t : ℝ => ((Real.exp (-σ * t) * hK k ε C t : ℝ) : ℂ)) measurableSet_Ioi
      (fun t _ => ?_)) hio
    push_cast
    ring_nf
  have hc : (((1 / 2 + σ : ℝ)) : ℂ) = 1 / 2 + (σ : ℂ) := by push_cast; ring
  rw [hmom, hreal, momentLap_kappa_real hk σ]
  push_cast
  rw [laplace_D_xiE hσ, hc]


/-! ### The spread-average theorem -/

/-- **F13, spread-average (moving-average) variant.** Let `k ≥ 0` be a bounded measurable kernel
supported on `[0,w]` whose Laplace transform `κ̂(z) = ∫ e^{−zu}k(u) du` has no zero on the strip `ε < Re z < ½`.
If the moving average `∫ k(u) D(L−u) du` is `≥ −C e^{εL}` for all `L > 0` (`D` extended by `0`
below `0`), `0 ≤ ε < ½`, then `ξ_E(s) ≠ 0` for every `Re s > ½ + ε`. -/
theorem F13_spread_xiE_ne_zero (hk : KernelSpec k w K)
    {ε C : ℝ} (hκne : ∀ z : ℂ, ε < z.re → z.re < 1 / 2 → momentLap k 0 z ≠ 0)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (hD : ∀ L : ℝ, 0 < L → -C * Real.exp (ε * L) ≤ conv k L) :
    ∀ s : ℂ, 1 / 2 + ε < s.re → xiE s ≠ 0 := by
  set h := hK k ε C with hh
  have hpos := hK_nonneg hD
  have hT := matchesXiK_hK hk (C := C) hε1
  have hκd := differentiable_kappa hk
  have hhalf : ∀ τ : ℝ, 1 / 2 < τ → LapInt h τ := fun τ hτ => integrableOn_hK hk hτ hε1
  have haesm : AEStronglyMeasurable h (volume.restrict (Ioi 0)) := aesm_h (σc := 1 / 2) hhalf
  have hclaim : ∀ y : ℝ, ε < y → LapInt h y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hεy, hy⟩ := hcon
    set S : Set ℝ := {τ | LapInt h τ} with hS
    have hlb : ∀ τ ∈ S, y < τ := by
      intro τ hτ
      by_contra hle
      exact hy (lapInt_mono hpos haesm (not_lt.mp hle) hτ)
    have hne : S.Nonempty := ⟨1, hhalf 1 (by norm_num)⟩
    have hbdd : BddBelow S := ⟨y, fun τ hτ => (hlb τ hτ).le⟩
    set σ := sInf S with hσ
    have hyσ : y ≤ σ := le_csInf hne (fun τ hτ => (hlb τ hτ).le)
    have hσhalf : σ ≤ 1 / 2 := by
      refine le_of_forall_pos_le_add (fun η hη => ?_)
      exact csInf_le hbdd (hhalf (1 / 2 + η) (by linarith))
    have hconvσ : ∀ τ : ℝ, σ < τ → LapInt h τ := by
      intro τ hτ
      obtain ⟨t, htS, htτ⟩ := exists_lt_of_csInf_lt hne hτ
      exact lapInt_mono hpos haesm htτ.le htS
    obtain ⟨y', hy'σ, hy'⟩ := landau_stepK hpos hconvσ hκd hκne hT hε0 (by linarith) hσhalf
    have : σ ≤ y' := csInf_le hbdd hy'
    linarith
  intro s hs
  have hz := xiE_ne_zero_onK hpos (fun τ hτ => hclaim τ hτ) hκd hκne hT (le_refl ε) hε1.le
    (s - 1 / 2) (by simp only [Complex.sub_re]; norm_num; linarith)
  have : 1 / 2 + (s - 1 / 2) = s := by ring
  rwa [this] at hz

/-- The same conclusion for Mathlib's `riemannZeta` (off the pole). -/
theorem F13_spread_riemannZeta_ne_zero (hk : KernelSpec k w K)
    {ε C : ℝ} (hκne : ∀ z : ℂ, ε < z.re → z.re < 1 / 2 → momentLap k 0 z ≠ 0)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (hD : ∀ L : ℝ, 0 < L → -C * Real.exp (ε * L) ≤ conv k L) :
    ∀ s : ℂ, 1 / 2 + ε < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  intro s hs hs1
  have hx := F13_spread_xiE_ne_zero hk hκne hε0 hε1 hD s hs
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hs; simp at hs; linarith
  rw [GppHeartReduction.xiE_eq hs0 hs1] at hx
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h0; apply hx; rw [h0, mul_zero]
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp at hs ⊢; linarith)
  rw [riemannZeta_def_of_ne_zero hs0]
  exact div_ne_zero hΛ hG

end Instance


/-! ### The uniform kernel: a plain moving average of width `w` -/

section Uniform

/-- Indicator of `[0,w]`. -/
noncomputable def kU (w : ℝ) (u : ℝ) : ℝ := (Icc (0 : ℝ) w).indicator (fun _ => (1 : ℝ)) u

theorem kernelSpec_kU (w : ℝ) : KernelSpec (kU w) w 1 where
  meas := measurable_const.indicator measurableSet_Icc
  nonneg := fun u => by
    unfold kU; by_cases h : u ∈ Icc (0 : ℝ) w <;> simp [Set.indicator, h]
  supp := fun u hu => by unfold kU; simp [Set.indicator, hu]
  bdd := fun u => by
    unfold kU; by_cases h : u ∈ Icc (0 : ℝ) w <;> simp [Set.indicator, h]

theorem conv_kU (w L : ℝ) : conv (kU w) L = ∫ u in Icc (0 : ℝ) w, Dz (L - u) := by
  unfold conv kU
  rw [← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  by_cases h : u ∈ Icc (0 : ℝ) w <;> simp [Set.indicator, h]

/-- `κ̂(z) · z = 1 − e^{−wz}` for the uniform kernel. -/
theorem momentLap_kU_mul {w : ℝ} (hw : 0 ≤ w) (z : ℂ) (hz : z ≠ 0) :
    momentLap (kU w) 0 z * z = 1 - Complex.exp (-z * w) := by
  have h1 : momentLap (kU w) 0 z = ∫ t in Ioc (0 : ℝ) w, Complex.exp (-z * (t : ℂ)) := by
    simp only [momentLap, pow_zero, one_mul]
    have : ∀ t : ℝ, Complex.exp (-z * (t : ℂ)) * ((kU w t : ℝ) : ℂ)
        = (Icc (0 : ℝ) w).indicator (fun t : ℝ => Complex.exp (-z * (t : ℂ))) t := by
      intro t; unfold kU
      by_cases h : t ∈ Icc (0 : ℝ) w <;> simp [Set.indicator, h]
    simp_rw [this]
    rw [setIntegral_indicator measurableSet_Icc]
    have hset : Ioi (0 : ℝ) ∩ Icc (0 : ℝ) w = Ioc (0 : ℝ) w := by
      ext t; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]; constructor
      · rintro ⟨h0, _, h2⟩; exact ⟨h0, h2⟩
      · rintro ⟨h0, h2⟩; exact ⟨h0, h0.le, h2⟩
    rw [hset]
  rw [h1]
  rw [← intervalIntegral.integral_of_le hw]
  have := integral_exp_mul_complex (a := (0 : ℝ)) (b := w) (c := -z) (neg_ne_zero.mpr hz)
  rw [this]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf

/-- For `w > 0` the uniform-kernel transform is nonvanishing on `Re z > 0`
(`|e^{-wz}| = e^{-w Re z} < 1`). -/
theorem momentLap_kU_ne_zero {w : ℝ} (hw : 0 < w) (z : ℂ) (hz : 0 < z.re) :
    momentLap (kU w) 0 z ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  intro h0
  have h := momentLap_kU_mul hw.le z hz0
  rw [h0, zero_mul] at h
  have h1 : Complex.exp (-z * w) = 1 := by
    have := h.symm; exact (sub_eq_zero.mp this).symm
  have h2 : ‖Complex.exp (-z * (w : ℂ))‖ = Real.exp (-(z.re * w)) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [h1, norm_one] at h2
  have : Real.exp (-(z.re * w)) < 1 := by
    have := Real.exp_lt_exp.mpr (show -(z.re * w) < 0 by nlinarith); simpa using this
  linarith

/-- The uniform-kernel convolution is the moving integral of `D` over `[L-w, L]`
(with `D` extended by `D(t) = D(0) = 0` for `t ≤ 0`). -/
theorem conv_kU_interval (w L : ℝ) (hw : 0 ≤ w) :
    conv (kU w) L = ∫ t in (L - w)..L, Dz t := by
  rw [conv_kU, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hw,
    intervalIntegral.integral_comp_sub_left (fun t => Dz t) L]
  simp

/-- **F13, moving-average (uniform window) form.**  Conditional: if the window integrals
`∫_{L-w}^{L} D` of the Round 23 function are bounded below by `-C e^{εL}` for every `L > 0`
(for some width `w > 0`, `0 ≤ ε < 1/2`), then the entire ξ has no zero with `Re s > 1/2 + ε`.
This is an RH-strength hypothesis; not a positivity proof. -/
theorem F13_uniform_xiE_ne_zero {w : ℝ} (hw : 0 < w) {ε C : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (hD : ∀ L : ℝ, 0 < L → -C * Real.exp (ε * L) ≤ ∫ t in (L - w)..L, Dz t) :
    ∀ s : ℂ, 1 / 2 + ε < s.re → xiE s ≠ 0 :=
  F13_spread_xiE_ne_zero (kernelSpec_kU w) (fun z h1 _ => momentLap_kU_ne_zero hw z (by linarith)) hε0 hε1
    (fun L hL => by rw [conv_kU_interval w L hw.le]; exact hD L hL)

/-- Same, for the Riemann zeta function (adds `s ≠ 1`). -/
theorem F13_uniform_riemannZeta_ne_zero {w : ℝ} (hw : 0 < w) {ε C : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (hD : ∀ L : ℝ, 0 < L → -C * Real.exp (ε * L) ≤ ∫ t in (L - w)..L, Dz t) :
    ∀ s : ℂ, 1 / 2 + ε < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
  F13_spread_riemannZeta_ne_zero (kernelSpec_kU w) (fun z h1 _ => momentLap_kU_ne_zero hw z (by linarith)) hε0 hε1
    (fun L hL => by rw [conv_kU_interval w L hw.le]; exact hD L hL)

end Uniform

/-! ### The Alpöge-weighted kernel `k(u) = eᵘ` on `[0, w]` (spread weights, `w = log 2`) -/

section Exponential

/-- `eᵘ` on `[0,w]`, zero elsewhere. -/
noncomputable def kE (w : ℝ) (u : ℝ) : ℝ := (Icc (0 : ℝ) w).indicator (fun u => Real.exp u) u

theorem kernelSpec_kE (w : ℝ) : KernelSpec (kE w) w (Real.exp w) where
  meas := (Real.continuous_exp.measurable).indicator measurableSet_Icc
  nonneg := fun u => by
    unfold kE; by_cases h : u ∈ Icc (0 : ℝ) w <;> simp [Set.indicator, h, (Real.exp_pos u).le]
  supp := fun u hu => by unfold kE; simp [Set.indicator, hu]
  bdd := fun u => by
    unfold kE
    by_cases h : u ∈ Icc (0 : ℝ) w
    · simp only [Set.indicator, h, if_true]
      rw [abs_of_pos (Real.exp_pos u)]; exact Real.exp_le_exp.mpr h.2
    · simp [Set.indicator, h, (Real.exp_pos w).le]

/-- `κ̂(z)·(z − 1) = 1 − e^{−(z−1)w}` for the `eᵘ` kernel on `[0,w]`. -/
theorem momentLap_kE_mul {w : ℝ} (hw : 0 ≤ w) (z : ℂ) (hz : z - 1 ≠ 0) :
    momentLap (kE w) 0 z * (z - 1) = 1 - Complex.exp (-(z - 1) * w) := by
  have h1 : momentLap (kE w) 0 z = ∫ t in Ioc (0 : ℝ) w, Complex.exp (-(z - 1) * (t : ℂ)) := by
    simp only [momentLap, pow_zero, one_mul]
    have : ∀ t : ℝ, Complex.exp (-z * (t : ℂ)) * ((kE w t : ℝ) : ℂ)
        = (Icc (0 : ℝ) w).indicator (fun t : ℝ => Complex.exp (-(z - 1) * (t : ℂ))) t := by
      intro t; unfold kE
      by_cases h : t ∈ Icc (0 : ℝ) w
      · simp only [Set.indicator, h, if_true]
        rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; ring
      · simp [Set.indicator, h]
    simp_rw [this]
    rw [setIntegral_indicator measurableSet_Icc]
    have hset : Ioi (0 : ℝ) ∩ Icc (0 : ℝ) w = Ioc (0 : ℝ) w := by
      ext t; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]; constructor
      · rintro ⟨h0, _, h2⟩; exact ⟨h0, h2⟩
      · rintro ⟨h0, h2⟩; exact ⟨h0, h0.le, h2⟩
    rw [hset]
  rw [h1, ← intervalIntegral.integral_of_le hw]
  have := integral_exp_mul_complex (a := (0 : ℝ)) (b := w) (c := -(z - 1)) (neg_ne_zero.mpr hz)
  rw [this]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf

/-- For `w > 0` the exponential kernel transform has no zeros on `Re z < 1`, since `|e^{−(z−1)w}| = e^{(1−Re z)w} > 1` there. On `Re z = 1` its zeros are `1 + 2πin/w` for nonzero integers `n`. At `z = 1` the integrand is one throughout `[0,w]`, so the transform equals `w`. -/
theorem momentLap_kE_ne_zero {w : ℝ} (hw : 0 < w) (z : ℂ) (hz : z.re < 1) :
    momentLap (kE w) 0 z ≠ 0 := by
  have hz1 : z - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  intro h0
  have h := momentLap_kE_mul hw.le z hz1
  rw [h0, zero_mul] at h
  have h1 : Complex.exp (-(z - 1) * w) = 1 := (sub_eq_zero.mp h.symm).symm
  have h2 : ‖Complex.exp (-(z - 1) * (w : ℂ))‖ = Real.exp ((1 - z.re) * w) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [h1, norm_one] at h2
  have : 1 < Real.exp ((1 - z.re) * w) := by
    have := Real.exp_lt_exp.mpr (show 0 < (1 - z.re) * w by nlinarith)
    simpa using this
  linarith

theorem conv_kE_interval (w L : ℝ) :
    conv (kE w) L = ∫ u in Icc (0 : ℝ) w, Real.exp u * Dz (L - u) := by
  unfold conv kE
  rw [← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  by_cases h : u ∈ Icc (0 : ℝ) w <;> simp [Set.indicator, h]

/-- **F13, spread-weight form** (`k(u) = eᵘ` on `[0,w]`; `w = log 2` is Alpöge's spread
weight window).  Conditional: `∫_0^w e^u D(L−u) du ≥ −C e^{εL}` for all `L > 0` ⇒ `ξ_E` has no
zero with `Re s > ½ + ε`. The kernel transform vanishes on `Re z = 1`, so only the strip
`ε < Re z < ½` is used. -/
theorem F13_expKernel_xiE_ne_zero {w : ℝ} (hw : 0 < w) {ε C : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (hD : ∀ L : ℝ, 0 < L →
      -C * Real.exp (ε * L) ≤ ∫ u in Icc (0 : ℝ) w, Real.exp u * Dz (L - u)) :
    ∀ s : ℂ, 1 / 2 + ε < s.re → xiE s ≠ 0 :=
  F13_spread_xiE_ne_zero (kernelSpec_kE w)
    (fun z _ h2 => momentLap_kE_ne_zero hw z (by linarith)) hε0 hε1
    (fun L hL => by rw [conv_kE_interval w L]; exact hD L hL)

theorem F13_expKernel_riemannZeta_ne_zero {w : ℝ} (hw : 0 < w) {ε C : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (hD : ∀ L : ℝ, 0 < L →
      -C * Real.exp (ε * L) ≤ ∫ u in Icc (0 : ℝ) w, Real.exp u * Dz (L - u)) :
    ∀ s : ℂ, 1 / 2 + ε < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
  F13_spread_riemannZeta_ne_zero (kernelSpec_kE w)
    (fun z _ h2 => momentLap_kE_ne_zero hw z (by linarith)) hε0 hε1
    (fun L hL => by rw [conv_kE_interval w L]; exact hD L hL)

end Exponential

end GppSpreadAverage

#print axioms GppSpreadAverage.laplace_conv
#print axioms GppSpreadAverage.F13_spread_xiE_ne_zero
#print axioms GppSpreadAverage.F13_spread_riemannZeta_ne_zero
#print axioms GppSpreadAverage.momentLap_kU_ne_zero
#print axioms GppSpreadAverage.F13_uniform_xiE_ne_zero
#print axioms GppSpreadAverage.F13_uniform_riemannZeta_ne_zero
#print axioms GppSpreadAverage.momentLap_kE_ne_zero
#print axioms GppSpreadAverage.F13_expKernel_xiE_ne_zero
#print axioms GppSpreadAverage.F13_expKernel_riemannZeta_ne_zero
#print axioms GppSpreadAverage.xiE_ne_zero_of_one_le_re
