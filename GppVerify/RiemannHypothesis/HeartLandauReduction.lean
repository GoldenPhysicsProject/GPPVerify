/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import GppVerify.RiemannHypothesis.HeartZetaUnitInterval
import GppVerify.RiemannHypothesis.HeartLaplaceIdentity
import GppVerify.RiemannHypothesis.HeartLandauLocal

/-!
# The Landau reduction (Round 23 F12 / F13)

For `0 ≤ ε < ½` and a constant `C`: if Round 23's function `D` (`GppHeartLaplace.Dfun`) satisfies
`D(L) ≥ −C e^{εL}` for all `L > 0`, then the entire completed zeta `ξ_E(s) = ½ + ½ s (s−1) Λ₀(s)`
has no zero with `Re s > ½ + ε` (`F13_xiE_ne_zero`); `F12_xiE_ne_zero` is `ε = 0` and
`F13_riemannZeta_ne_zero` states the conclusion for Mathlib's `riemannZeta` off `s = 1`.
The converse (zero-free half-plane ⇒ the one-sided bound) is **not** proved here.

**Route.** Put `h = D + C e^{εt}` (≥ 0 by hypothesis). F11 (`F11_laplace_identity`) gives, for real
`σ > ½`, `L[h](σ) = (ξ′/ξ)(½+σ)/σ² + C/(σ−ε)`. Then:

1. *ODE.* On `Re z > σc` (any `ε ≤ σc ≤ ½` above which `L[h]` converges) the identity theorem
   extends this to `ξ′(½+z) = ξ(½+z) · z²(L[h](z) − C/(z−ε))` (`xiE_deriv_eq_mul`); the right
   factor is holomorphic, so comparing orders of vanishing (`analyticOrderAt_deriv_of_pos`) shows
   `ξ(½+z) ≠ 0` there (`xiE_ne_zero_on`). Real nonvanishing of `ξ_E` on `s > 0` (F9 on `(0,1)`,
   `ξ_E(1) = ½`, `ζ ≠ 0` for `Re s ≥ 1`) supplies the one real point the argument needs.
2. *Landau step.* If the abscissa `σc` exceeded `ε` then `(ξ′/ξ)(½+z)/z² + C/(z−ε)` is a single
   holomorphic formula on a disc about `σc` (nonvanishing of `ξ(½+σc)`, real) glued to the half-plane;
   `landau_local` (`HeartLandauLocal`) then gives convergence below `σc` (`landau_step`).
3. *Abscissa.* `σc = sInf` of the convergence set; the two steps force `σc ≤ ε`
   (`F13_xiE_ne_zero`), and then step 1 at `σc = ε` is the conclusion.

Statement fidelity notes: `ξ_E` is used because Mathlib's `completedRiemannZeta` is junk at `s = 1`.
No zeta zero is an input; no `sorry`, no `axiom`.
-/

namespace GppHeartReduction

open Complex MeasureTheory Set Filter Topology
open RhWaveLean (momentLap hasDerivAt_momentLap aesm_h)
open GppHeartLaplace (Dfun)

/-- The entire completed zeta `ξ_E(s) = ½ + ½ s (s−1) Λ₀(s)`; equals `½ s (s−1) Λ(s)` off `s = 0, 1`. -/
noncomputable def xiE (s : ℂ) : ℂ := 1 / 2 + (1 / 2) * s * (s - 1) * completedRiemannZeta₀ s

theorem differentiable_xiE : Differentiable ℂ xiE := by
  unfold xiE
  have := differentiable_completedZeta₀
  fun_prop

theorem xiE_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiE s = (1 / 2) * s * (s - 1) * completedRiemannZeta s := by
  unfold xiE
  rw [completedRiemannZeta_eq]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

theorem xiE_one : xiE 1 = 1 / 2 := by simp [xiE]

theorem xiE_real_ne_zero {x : ℝ} (hx : 0 < x) : xiE (x : ℂ) ≠ 0 := by
  by_cases h1 : x = 1
  · subst h1; simp [xiE_one]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast h1
  rw [xiE_eq hx0 hx1]
  have hz : riemannZeta (x : ℂ) ≠ 0 := by
    rcases lt_or_gt_of_ne h1 with h | h
    · exact GppHeartZeta.riemannZeta_ne_zero_of_mem_Ioo hx h
    · exact riemannZeta_ne_zero_of_one_le_re (by simp; exact h.le)
  have hG : Gammaℝ (x : ℂ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simpa using hx)
  have hΛ : completedRiemannZeta (x : ℂ) ≠ 0 := by
    intro h
    apply hz
    rw [riemannZeta_def_of_ne_zero hx0, h, zero_div]
  have : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp [hx0, this, hΛ]


/-! ### Abstract core: a nonnegative `h` whose Laplace transform matches the F11 identity -/

section Core

variable {h : ℝ → ℝ} {ε C σc : ℝ}

/-- The hypothesis tying `h` to `ξ_E`: for real `σ > ½`, `L[h](σ) = (ξ_E′/ξ_E)(½+σ)/σ² + C/(σ−ε)`. -/
def MatchesXi (h : ℝ → ℝ) (ε C : ℝ) : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → momentLap h 0 (σ : ℂ)
    = logDeriv xiE (((1 / 2 + σ : ℝ)) : ℂ) / (σ : ℂ) ^ 2 + (C : ℂ) / ((σ : ℂ) - ε)

theorem W_differentiableOn (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hεσ : ε ≤ σc) :
    DifferentiableOn ℂ (fun z : ℂ => z ^ 2 * (momentLap h 0 z - (C : ℂ) / (z - ε)))
      {z : ℂ | σc < z.re} := by
  have hTd : DifferentiableOn ℂ (momentLap h 0) {z : ℂ | σc < z.re} := fun z hz =>
    (hasDerivAt_momentLap hpos hconv 0 hz).differentiableAt.differentiableWithinAt
  have hsub : ∀ z ∈ {z : ℂ | σc < z.re}, z - (ε : ℂ) ≠ 0 := by
    intro z hz hc
    have : (z - (ε : ℂ)).re = 0 := by rw [hc]; simp
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    have : σc < z.re := hz
    linarith
  intro z hz
  have h1 : DifferentiableWithinAt ℂ (fun z : ℂ => (C : ℂ) / (z - ε)) {z : ℂ | σc < z.re} z :=
    (differentiableWithinAt_const _).div (differentiableWithinAt_id.sub_const _) (hsub z hz)
  exact (differentiableWithinAt_id.pow 2).mul ((hTd z hz).sub h1)

theorem xiE_deriv_eq_mul (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hT : MatchesXi h ε C) (hεσ : ε ≤ σc) (hσc : σc ≤ 1 / 2) :
    ∀ z : ℂ, σc < z.re →
      deriv xiE (1 / 2 + z) = xiE (1 / 2 + z) * (z ^ 2 * (momentLap h 0 z - (C : ℂ) / (z - ε))) := by
  set H : Set ℂ := {z : ℂ | σc < z.re} with hH
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHpre : IsPreconnected H := (convex_halfSpace_re_gt σc).isPreconnected
  set W : ℂ → ℂ := fun z => z ^ 2 * (momentLap h 0 z - (C : ℂ) / (z - ε)) with hW
  have hWd : DifferentiableOn ℂ W H := W_differentiableOn hpos hconv hεσ
  have hdx : Differentiable ℂ (deriv xiE) := fun z =>
    (differentiable_xiE.analyticAt z).deriv.differentiableAt
  set f : ℂ → ℂ := fun z => deriv xiE (1 / 2 + z) - xiE (1 / 2 + z) * W z with hf
  have hfd : DifferentiableOn ℂ f H := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => deriv xiE (1 / 2 + z)) z :=
      (hdx (1 / 2 + z)).comp z (differentiableAt_const _ |>.add differentiableAt_id)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => xiE (1 / 2 + z)) z :=
      (differentiable_xiE (1 / 2 + z)).comp z (differentiableAt_const _ |>.add differentiableAt_id)
    exact h1.differentiableWithinAt.sub (h2.differentiableWithinAt.mul (hWd z hz))
  have hfa : AnalyticOnNhd ℂ f H := hfd.analyticOnNhd hHopen
  have hzero : ∀ σ : ℝ, 1 / 2 < σ → f (σ : ℂ) = 0 := by
    intro σ hσ
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : σ ≠ 0)
    have hx : xiE (1 / 2 + (σ : ℂ)) ≠ 0 := by
      have := xiE_real_ne_zero (x := 1 / 2 + σ) (by linarith)
      simpa using this
    have hm := hT σ hσ
    have hlog : logDeriv xiE (((1 / 2 + σ : ℝ)) : ℂ) = deriv xiE (1 / 2 + (σ : ℂ)) / xiE (1 / 2 + (σ : ℂ)) := by
      rw [logDeriv_apply]; push_cast; rfl
    have hT' : momentLap h 0 (σ : ℂ) - (C : ℂ) / ((σ : ℂ) - ε)
        = deriv xiE (1 / 2 + (σ : ℂ)) / xiE (1 / 2 + (σ : ℂ)) / (σ : ℂ) ^ 2 := by
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

theorem xiE_ne_zero_on (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hT : MatchesXi h ε C) (hεσ : ε ≤ σc) (hσc : σc ≤ 1 / 2) :
    ∀ z : ℂ, σc < z.re → xiE (1 / 2 + z) ≠ 0 := by
  intro z0 hz0 hF0
  have hode := xiE_deriv_eq_mul hpos hconv hT hεσ hσc
  set W : ℂ → ℂ := fun z => z ^ 2 * (momentLap h 0 z - (C : ℂ) / (z - ε)) with hW
  set H : Set ℂ := {z : ℂ | σc < z.re} with hH
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hWa : AnalyticAt ℂ W z0 :=
    (W_differentiableOn (C := C) hpos hconv hεσ).analyticAt (hHopen.mem_nhds hz0)
  set F : ℂ → ℂ := fun z => xiE (1 / 2 + z) with hF
  have hFd : Differentiable ℂ F := fun z =>
    (differentiable_xiE (1 / 2 + z)).comp z (differentiableAt_const _ |>.add differentiableAt_id)
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => (hFd.analyticAt z)
  have hFz0 : AnalyticAt ℂ F z0 := hFd.analyticAt z0
  -- F is not locally zero at z0
  have hne_top : analyticOrderAt F z0 ≠ ⊤ := by
    intro htop
    have hev : ∀ᶠ z in 𝓝 z0, F z = 0 := analyticOrderAt_eq_top.mp htop
    have h0 := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z0) hev
    have h1 : F 1 = 0 := h0 (Set.mem_univ 1)
    have h2 : xiE ((3 / 2 : ℝ) : ℂ) ≠ 0 := xiE_real_ne_zero (by norm_num)
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
  -- deriv F = F * W near z0
  have hev : deriv F =ᶠ[𝓝 z0] F * W := by
    filter_upwards [hHopen.mem_nhds hz0] with z hz
    have hdz : deriv F z = deriv xiE (1 / 2 + z) := deriv_comp_const_add (f := xiE) (a := (1/2:ℂ)) (x := z)
    rw [hdz, hode z hz]
    rfl
  have h2 : analyticOrderAt (deriv F) z0 = analyticOrderAt F z0 + analyticOrderAt W z0 := by
    rw [analyticOrderAt_congr hev]
    exact analyticOrderAt_mul hFz0 hWa
  rw [hderiv, hord] at h2
  have h3 : ((n : ℕ∞)) ≥ (n : ℕ∞) + 1 := by
    calc (n : ℕ∞) = (n : ℕ∞) + 1 + analyticOrderAt W z0 := h2
      _ ≥ (n : ℕ∞) + 1 := le_self_add
  have h4 : ((n : ℕ∞)) < (n : ℕ∞) + 1 := by
    exact ENat.lt_add_one_iff (by simp) |>.mpr le_rfl
  exact absurd h3 (not_le.mpr h4)

/-- **Landau step.** If `ε ≥ 0`, `ε < σc ≤ ½`, and `h ≥ 0` has Laplace transform converging above `σc`
and matching the `ξ_E` identity, then it converges at some exponent strictly below `σc`. -/
theorem landau_step (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hT : MatchesXi h ε C) (hε0 : 0 ≤ ε) (hεσ : ε < σc) (hσc : σc ≤ 1 / 2) :
    ∃ y : ℝ, y < σc ∧
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-y * t) * h t : ℝ) : ℂ)) (Ioi 0) volume := by
  have hode := xiE_deriv_eq_mul hpos hconv hT hεσ.le hσc
  have hz := xiE_ne_zero_on hpos hconv hT hεσ.le hσc
  have hxσ : xiE (1 / 2 + (σc : ℂ)) ≠ 0 := by
    have := xiE_real_ne_zero (x := 1 / 2 + σc) (by linarith)
    simpa using this
  have hcont : ContinuousAt (fun z : ℂ => xiE (1 / 2 + z)) (σc : ℂ) :=
    (differentiable_xiE (1 / 2 + (σc : ℂ))).continuousAt.comp (f := fun z : ℂ => 1 / 2 + z)
      (continuousAt_const.add continuousAt_id)
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
  set Hext : ℂ → ℂ := fun z => deriv xiE (1 / 2 + z) / (xiE (1 / 2 + z) * z ^ 2)
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
      (differentiable_xiE.analyticAt _).deriv.differentiableAt
    have h1 : DifferentiableAt ℂ (fun z : ℂ => deriv xiE (1 / 2 + z)) z :=
      hdx.comp z (differentiableAt_const _ |>.add differentiableAt_id)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => xiE (1 / 2 + z)) z :=
      (differentiable_xiE (1 / 2 + z)).comp z (differentiableAt_const _ |>.add differentiableAt_id)
    have h3 : DifferentiableAt ℂ Hext z := by
      refine DifferentiableAt.add (h1.div (h2.mul (differentiableAt_id.pow 2)) (mul_ne_zero hx (pow_ne_zero 2 hz0))) ?_
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

/-! ### Instantiation at the Round 23 function `D` -/

section Instance

/-- `h = D + C e^{εt}` on `t > 0` (and `0` elsewhere). -/
noncomputable def hfun (ε C : ℝ) (t : ℝ) : ℝ :=
  if 0 < t then Dfun t + C * Real.exp (ε * t) else 0

theorem hfun_nonneg {ε C : ℝ} (hD : ∀ L : ℝ, 0 < L → -C * Real.exp (ε * L) ≤ Dfun L) (t : ℝ) :
    0 ≤ hfun ε C t := by
  unfold hfun
  split_ifs with ht
  · have := hD t ht
    linarith
  · exact le_rfl

theorem integrableOn_D {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun L : ℝ => Real.exp (-σ * L) * Dfun L) (Ioi 0) := by
  have hσ0 : 0 < σ := by linarith
  have hA := GppHeartLaplace.integrableOn_arch hσ
  have hLin := (GppHeartLaplace.integrableOn_linear hσ0).const_mul GppHeartLaplace.c1
  have hE := (exp_neg_integrableOn_Ioi 0 hσ0).const_mul GppHeartLaplace.C2
  have hT := GppHeartLaplace.integrableOn_T hσ0
  have hS := GppHeartLaplace.integrableOn_S hσ
  have h := (((hA.add hLin).add hE).sub hT).sub hS
  refine h.congr_fun (fun L _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Pi.sub_apply, GppHeartLaplace.Dfun]
  ring

theorem integrableOn_hfun {ε C σ : ℝ} (hσ : 1 / 2 < σ) (hε : ε < 1 / 2) :
    IntegrableOn (fun t : ℝ => ((Real.exp (-σ * t) * hfun ε C t : ℝ) : ℂ)) (Ioi 0) := by
  have h1 := integrableOn_D hσ
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < σ - ε)).const_mul C
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-σ * t) * hfun ε C t) (Ioi 0) := by
    refine (h1.add h2).congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only [hfun, if_pos ht0]
    have : Real.exp (-σ * t) * Real.exp (ε * t) = Real.exp (-(σ - ε) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-σ * t) * Dfun t + C * Real.exp (-(σ - ε) * t)
        = Real.exp (-σ * t) * Dfun t + C * (Real.exp (-σ * t) * Real.exp (ε * t)) := by rw [this]
      _ = _ := by ring
  exact h3.ofReal

theorem matchesXi {ε C : ℝ} (hε : ε < 1 / 2) : MatchesXi (hfun ε C) ε C := by
  intro σ hσ
  have hσ0 : 0 < σ := by linarith
  have hID := integrableOn_D hσ
  have hE : IntegrableOn (fun t : ℝ => C * Real.exp (-(σ - ε) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < σ - ε)).const_mul C
  have hreal : (∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * hfun ε C t)
      = (∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * Dfun t)
        + C / (σ - ε) := by
    have e1 : (∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * hfun ε C t)
        = ∫ t in Ioi (0 : ℝ), (Real.exp (-σ * t) * Dfun t + C * Real.exp (-(σ - ε) * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : 0 < t := ht
      simp only [hfun, if_pos ht0]
      have : Real.exp (-σ * t) * Real.exp (ε * t) = Real.exp (-(σ - ε) * t) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (-σ * t) * (Dfun t + C * Real.exp (ε * t))
          = Real.exp (-σ * t) * Dfun t + C * (Real.exp (-σ * t) * Real.exp (ε * t)) := by ring
        _ = _ := by rw [this]
    rw [e1, integral_add hID hE, integral_const_mul,
      GppHeartLaplace.integral_exp_neg_Ioi_zero' (by linarith : 0 < σ - ε)]
    ring
  have hF11 := GppHeartLaplace.F11_laplace_identity hσ
  have hxi : logDeriv GppHeartLaplace.xiC (((1 / 2 + σ : ℝ)) : ℂ)
      = logDeriv xiE (((1 / 2 + σ : ℝ)) : ℂ) := by
    have hev : GppHeartLaplace.xiC =ᶠ[𝓝 (((1 / 2 + σ : ℝ)) : ℂ)] xiE := by
      have h0 : ∀ᶠ s : ℂ in 𝓝 (((1 / 2 + σ : ℝ)) : ℂ), s ≠ 0 := isOpen_ne.mem_nhds (by
        push_cast; intro h; have := congrArg Complex.re h; simp at this; linarith)
      have h1 : ∀ᶠ s : ℂ in 𝓝 (((1 / 2 + σ : ℝ)) : ℂ), s ≠ 1 := isOpen_ne.mem_nhds (by
        push_cast; intro h; have := congrArg Complex.re h; simp at this; linarith)
      filter_upwards [h0, h1] with s hs0 hs1
      exact (xiE_eq hs0 hs1).symm
    exact (logDeriv_congr_nhds hev).eq_of_nhds
  have hmom : momentLap (hfun ε C) 0 (σ : ℂ)
      = (((∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * hfun ε C t : ℝ)) : ℂ) := by
    simp only [momentLap, pow_zero, one_mul]
    have hio := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun t : ℝ => Real.exp (-σ * t) * hfun ε C t)
    refine Eq.trans (setIntegral_congr_fun
      (g := fun t : ℝ => ((Real.exp (-σ * t) * hfun ε C t : ℝ) : ℂ)) measurableSet_Ioi
      (fun t _ => ?_)) hio
    push_cast
    ring_nf
  have hc : (((1 / 2 + σ : ℝ)) : ℂ) = 1 / 2 + (σ : ℂ) := by push_cast; ring
  rw [hmom, hreal]
  push_cast
  rw [hF11, hxi, hc]

end Instance

/-! ### The reduction theorem (F12 / F13) -/

section Main

/-- Laplace integrability at exponent `τ`. -/
def LapInt (h : ℝ → ℝ) (τ : ℝ) : Prop :=
  IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume

theorem lapInt_mono {h : ℝ → ℝ} (hpos : ∀ t, 0 ≤ h t)
    (haesm : AEStronglyMeasurable h (volume.restrict (Ioi 0))) {τ τ' : ℝ} (hτ : τ ≤ τ')
    (hI : LapInt h τ) : LapInt h τ' := by
  unfold LapInt at *
  refine Integrable.mono' hI.norm ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-τ' * t)).aestronglyMeasurable.mul haesm))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hpos t)),
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hpos t))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (hpos t)

/-- **F13 (parametrised Landau reduction).** For `0 ≤ ε < ½` and any `C`: if
`D(L) ≥ −C e^{εL}` for all `L > 0`, then `ξ_E(s) ≠ 0` for every `Re s > ½ + ε`.
(`D` is Round 23's function; the hypothesis is the RH-equivalent one-sided boundedness.) -/
theorem F13_xiE_ne_zero {ε C : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (hD : ∀ L : ℝ, 0 < L → -C * Real.exp (ε * L) ≤ Dfun L) :
    ∀ s : ℂ, 1 / 2 + ε < s.re → xiE s ≠ 0 := by
  set h := hfun ε C with hh
  have hpos := hfun_nonneg hD
  have hT := matchesXi (C := C) hε1
  have hhalf : ∀ τ : ℝ, 1 / 2 < τ → LapInt h τ := fun τ hτ => integrableOn_hfun hτ hε1
  have haesm : AEStronglyMeasurable h (volume.restrict (Ioi 0)) := aesm_h (σc := 1 / 2) hhalf
  -- every exponent above `ε` converges
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
    obtain ⟨y', hy'σ, hy'⟩ := landau_step hpos hconvσ hT hε0 (by linarith) hσhalf
    have : σ ≤ y' := csInf_le hbdd hy'
    linarith
  intro s hs
  have hz := xiE_ne_zero_on hpos (fun τ hτ => hclaim τ hτ) hT (le_refl ε) hε1.le (s - 1 / 2) (by
    simp only [Complex.sub_re]; norm_num; linarith)
  have : 1 / 2 + (s - 1 / 2) = s := by ring
  rwa [this] at hz

/-- **F12.** The `ε = 0` case: `D(L) ≥ −C` for `L > 0` forces `ξ_E ≠ 0` on `Re s > ½`. -/
theorem F12_xiE_ne_zero {C : ℝ} (hD : ∀ L : ℝ, 0 < L → -C ≤ Dfun L) :
    ∀ s : ℂ, 1 / 2 < s.re → xiE s ≠ 0 := by
  have := F13_xiE_ne_zero (ε := 0) (C := C) le_rfl (by norm_num) (by
    intro L hL; simpa using hD L hL)
  intro s hs
  exact this s (by simpa using hs)

/-- The same conclusion for Mathlib's `riemannZeta` (off the pole). -/
theorem F13_riemannZeta_ne_zero {ε C : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (hD : ∀ L : ℝ, 0 < L → -C * Real.exp (ε * L) ≤ Dfun L) :
    ∀ s : ℂ, 1 / 2 + ε < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  intro s hs hs1
  have hx := F13_xiE_ne_zero hε0 hε1 hD s hs
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hs; simp at hs; linarith
  rw [xiE_eq hs0 hs1] at hx
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h0; apply hx; rw [h0, mul_zero]
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp at hs ⊢; linarith)
  rw [riemannZeta_def_of_ne_zero hs0]
  exact div_ne_zero hΛ hG

end Main

end GppHeartReduction

#print axioms GppHeartReduction.xiE_deriv_eq_mul
#print axioms GppHeartReduction.xiE_ne_zero_on
#print axioms GppHeartReduction.landau_step
#print axioms GppHeartReduction.F13_xiE_ne_zero
#print axioms GppHeartReduction.F12_xiE_ne_zero
#print axioms GppHeartReduction.F13_riemannZeta_ne_zero
