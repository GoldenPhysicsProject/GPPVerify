import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A holomorphic logarithmic derivative forbids zeros

This is the exact complex-analysis step behind the slit-resolvent / connected-current reductions
(Codex, `2026-09-28_independent_frontier_assessment.md` §4, repaired versions A and B):

> If `F` is analytic on a preconnected open set `U`, `M` is analytic on `U`, `F' = M F` on `U`, and
> `F` is not identically zero, then `F` has **no zeros in `U`**.

`zero_free_of_log_deriv`. The proof is the order argument from the note: at a zero of finite order `m ≥ 1`
write `F = (w − z₀)^m G` with `G(z₀) ≠ 0`; then `F' = m (w−z₀)^{m−1} G + (w−z₀)^m G'` and `M F = (w−z₀)^m M G`
agree to order `m − 1`, which forces `m G(z₀) = 0`. A zero of infinite order makes `F ≡ 0` by the identity
theorem.

## Scope

This is a reduction lemma. The hard step in any application to the Riemann zeta function is *constructing* a
holomorphic `M` on the slit plane with `M F = F'` from arithmetic data; nothing here constructs it, and the
counterexample in the note (bounded functionals with non-analytic dependence) shows the analytic dependence
hypothesis cannot be dropped. No RH claim.
-/

open Filter Topology

namespace GppLogDerivZeroFree

/-- Local step: a zero of an analytic `F` with `F' = M F` nearby, `M` analytic, forces `F ≡ 0` nearby. -/
theorem local_zero_vanishes {F M : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀) (hM : AnalyticAt ℂ M z₀)
    (hode : ∀ᶠ w in 𝓝 z₀, deriv F w = M w * F w) (h0 : F z₀ = 0) : ∀ᶠ w in 𝓝 z₀, F w = 0 := by
  by_contra hne
  have hord : analyticOrderAt F z₀ ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hord
  obtain ⟨G, hGa, hG0, hFG⟩ := (hF.analyticOrderAt_eq_natCast).mp hm.symm
  have hFG1 : ∀ᶠ z in 𝓝 z₀, F z = (z - z₀) ^ m * G z := by simpa using hFG
  have hmpos : m ≠ 0 := by
    intro hm0
    subst hm0
    have := hFG1.self_of_nhds
    simp at this
    exact hG0 (by rw [← this]; exact h0)
  have hGd : ∀ᶠ w in 𝓝 z₀, DifferentiableAt ℂ G w :=
    hGa.eventually_analyticAt.mono fun w hw => hw.differentiableAt
  have hall : ∀ᶠ w in 𝓝 z₀, ∀ᶠ z in 𝓝 w, F z = (z - z₀) ^ m * G z := hFG1.eventually_nhds
  have key : ∀ᶠ w in 𝓝[≠] z₀,
      (m : ℂ) * G w + (w - z₀) * deriv G w - M w * (w - z₀) * G w = 0 := by
    have h1 := hall.and (hode.and hGd)
    have h2 : ∀ᶠ w in 𝓝[≠] z₀, w ≠ z₀ := self_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds h1, h2] with w ⟨hFw, hode', hGdw⟩ hw
    have h3 : HasDerivAt (fun w => (w - z₀) ^ m) ((m : ℂ) * (w - z₀) ^ (m - 1)) w := by
      simpa using (hasDerivAt_pow m (w - z₀)).comp_sub_const w z₀
    have h4 := h3.mul hGdw.hasDerivAt
    have h5 : HasDerivAt F ((m : ℂ) * (w - z₀) ^ (m - 1) * G w + (w - z₀) ^ m * deriv G w) w :=
      h4.congr_of_eventuallyEq hFw
    have hd := h5.deriv
    have hFw0 : F w = (w - z₀) ^ m * G w := hFw.self_of_nhds
    rw [hd, hFw0] at hode'
    have hpow : (w - z₀) ^ (m - 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
    have hm1 : (w - z₀) ^ m = (w - z₀) ^ (m - 1) * (w - z₀) := by
      rw [← pow_succ]; congr 1; omega
    rw [hm1] at hode'
    have hmul : (w - z₀) ^ (m - 1) *
        ((m : ℂ) * G w + (w - z₀) * deriv G w - M w * (w - z₀) * G w) = 0 := by
      linear_combination hode'
    exact (mul_eq_zero.mp hmul).resolve_left hpow
  -- pass to the limit `w → z₀`
  have hcont : ContinuousAt (fun w => (m : ℂ) * G w + (w - z₀) * deriv G w - M w * (w - z₀) * G w) z₀ := by
    have hG := hGa.continuousAt
    have hGd' := hGa.deriv.continuousAt
    have hMc := hM.continuousAt
    fun_prop
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {z₀}ᶜ))
  have hzero : Tendsto (fun w => (m : ℂ) * G w + (w - z₀) * deriv G w - M w * (w - z₀) * G w)
      (𝓝[≠] z₀) (𝓝 0) := tendsto_const_nhds.congr' (key.mono fun w hw => hw.symm)
  have := tendsto_nhds_unique hlim hzero
  simp at this
  rcases this with h | h
  · exact hmpos (by exact_mod_cast h)
  · exact hG0 h

/-- **A holomorphic logarithmic derivative forbids zeros.** -/
theorem zero_free_of_log_deriv {U : Set ℂ} (hU : IsOpen U) (hpc : IsPreconnected U) {F M : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hM : AnalyticOnNhd ℂ M U)
    (hode : ∀ z ∈ U, deriv F z = M z * F z) {z₁ : ℂ} (hz₁ : z₁ ∈ U) (hne : F z₁ ≠ 0) :
    ∀ z ∈ U, F z ≠ 0 := by
  intro z hz h0
  have hloc := local_zero_vanishes (hF z hz) (hM z hz)
    (Filter.eventually_of_mem (hU.mem_nhds hz) hode) h0
  have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hz hloc
  exact hne (this hz₁)

/-! ## Application to the completed zeta function on the slit plane -/

open Complex

/-- The entire function `ξ(s) = (1 + s(s−1) Λ₀(s))/2` (so `ξ = ½ s(s−1) Λ`, with `ξ(0) = ξ(1) = ½`). -/
noncomputable def xi (s : ℂ) : ℂ := (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem differentiable_xi : Differentiable ℂ xi := by
  unfold xi
  have := differentiable_completedZeta₀
  fun_prop

/-- `ξ(2) ≠ 0` (so `ξ` is not identically zero). -/
theorem xi_two_ne : xi 2 ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hz : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp)
  have hG : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp)
  have hL : completedRiemannZeta 2 ≠ 0 := by
    have := riemannZeta_def_of_ne_zero h2
    intro h0
    rw [h0, zero_div] at this
    exact hz this
  have e := completedRiemannZeta_eq 2
  have hx : xi 2 = completedRiemannZeta 2 := by
    rw [e]; unfold xi; norm_num; ring
  rw [hx]; exact hL

/-- `F(u) = ξ(1/2 + √u)` on the slit plane. -/
noncomputable def slitF (u : ℂ) : ℂ := xi (1 / 2 + u ^ (2⁻¹ : ℂ))

theorem analyticOnNhd_slitF : AnalyticOnNhd ℂ slitF slitPlane := by
  intro u hu
  have hxi : AnalyticAt ℂ xi (1 / 2 + u ^ (2⁻¹ : ℂ)) := differentiable_xi.analyticAt _
  have hs : AnalyticAt ℂ (fun u : ℂ => 1 / 2 + u ^ (2⁻¹ : ℂ)) u := by
    have : AnalyticAt ℂ (fun u : ℂ => u ^ (2⁻¹ : ℂ)) u :=
      (analyticAt_id).cpow analyticAt_const (by simpa using hu)
    exact analyticAt_const.add this
  exact hxi.comp_of_eq hs rfl

lemma sq_mem_slitPlane {w : ℂ} (hw : 0 < w.re) : w ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  have hre : (w ^ 2).re = w.re * w.re - w.im * w.im := by simp [sq]
  have him : (w ^ 2).im = 2 * w.re * w.im := by simp [sq]; ring
  by_cases hb : w.im = 0
  · left; rw [hre, hb]; nlinarith
  · right; rw [him]; exact mul_ne_zero (by positivity) hb

/-- **RH from a holomorphic logarithmic derivative on the slit plane.** If there is `M` analytic on the
slit plane `ℂ ∖ (−∞, 0]` with `F' = M F` for `F(u) = ξ(1/2 + √u)`, then every zero of `ξ` lies on the
critical line. The analytic input `M` is exactly the object whose construction from arithmetic data is the
open step of the slit-resolvent route. -/
theorem rh_of_slit_log_derivative {M : ℂ → ℂ} (hM : AnalyticOnNhd ℂ M slitPlane)
    (hode : ∀ u ∈ slitPlane, deriv slitF u = M u * slitF u) :
    ∀ s : ℂ, xi s = 0 → s.re = 1 / 2 := by
  intro s hs
  by_contra hne
  -- reduce to `Re s > 1/2` by the functional equation
  obtain ⟨s', hs'0, hs're⟩ : ∃ s' : ℂ, xi s' = 0 ∧ 1 / 2 < s'.re := by
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨1 - s, by rw [xi_one_sub]; exact hs, ?_⟩
      simp; linarith
    · exact ⟨s, hs, h⟩
  have hw : 0 < (s' - 1 / 2).re := by simp; linarith
  have hu : (s' - 1 / 2) ^ 2 ∈ slitPlane := sq_mem_slitPlane hw
  have hF0 : slitF ((s' - 1 / 2) ^ 2) = 0 := by
    unfold slitF
    rw [sq_cpow_two_inv hw]
    have : (1 / 2 : ℂ) + (s' - 1 / 2) = s' := by ring
    rw [this]; exact hs'0
  have hz1 : ((3 / 2 : ℂ) ^ 2) ∈ slitPlane := sq_mem_slitPlane (by norm_num)
  have hF1 : slitF ((3 / 2 : ℂ) ^ 2) ≠ 0 := by
    unfold slitF
    rw [sq_cpow_two_inv (by norm_num)]
    have : (1 / 2 : ℂ) + 3 / 2 = 2 := by norm_num
    rw [this]; exact xi_two_ne
  exact zero_free_of_log_deriv isOpen_slitPlane (starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected
    analyticOnNhd_slitF hM hode hz1 hF1 _ hu hF0

/-- Nontrivial zeros of `ζ` are zeros of `ξ`. -/
theorem xi_eq_zero_of_zeta_zero {s : ℂ} (hz : riemannZeta s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hg : Gammaℝ s ≠ 0) : xi s = 0 := by
  have hL : completedRiemannZeta s = 0 := by
    have := riemannZeta_def_of_ne_zero hs0
    rw [hz] at this
    exact (div_eq_zero_iff.mp this.symm).resolve_right hg
  have e := completedRiemannZeta_eq s
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold xi
  have : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
    rw [hL] at e; linear_combination -e
  rw [this]
  field_simp
  ring

/-- **The Riemann Hypothesis from a holomorphic logarithmic derivative on the slit plane.** -/
theorem riemannHypothesis_of_slit_log_derivative {M : ℂ → ℂ} (hM : AnalyticOnNhd ℂ M slitPlane)
    (hode : ∀ u ∈ slitPlane, deriv slitF u = M u * slitF u) : RiemannHypothesis := by
  intro s hz htriv h1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hg : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hs0 (by simpa using hn)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      exact htriv ⟨m, by rw [hn]; push_cast; ring⟩
  exact rh_of_slit_log_derivative hM hode s (xi_eq_zero_of_zeta_zero hz hs0 h1 hg)

end GppLogDerivZeroFree
