import GppVerify.Analysis.Pringsheim
import Mathlib.Analysis.Normed.Module.Convex

/-!
# One-sided Pringsheim: a one-sided coefficient bound forces radius one

This file proves the abstract analytic step behind Codex's one-sided Cayley–Laguerre RH
criterion (2026-10-11, §§L and R). If the Taylor coefficients `aₙ` of a function `g` are bounded
below by `−eₙ`, where `Σ eₙ zⁿ` has radius at least one, and `g` continues analytically along
the whole real segment `[0, 1)`, then `Σ aₙ zⁿ` itself has radius at least one.

`GppOneSidedPringsheim.summable_of_oneSided`. Let `aₙ + eₙ ≥ 0`, with `Σ |eₙ| rⁿ < ∞` for
`r < 1` and `Σ |aₙ| rⁿ < ∞` for `r < R`. Suppose `g = Σ aₙ zⁿ` on `‖z‖ < R`, and `g` is
analytic at every real `x ∈ [0, 1)`. Then `Σ |aₙ| rⁿ < ∞` for every `r < 1`.

**Proof.** Put `bₙ = aₙ + eₙ ≥ 0`. If some `r₀ < 1` had `Σ bₙ r₀ⁿ = ∞`, let `ρ ≤ r₀` be the
supremum of the convergence points in `[0, r₀]`.

1. The points where `g` is analytic form an open set containing the compact segment
   `[0, ρ]`, so some convex `δ`-thickening `T` of it lies in that set.
2. On the convex set `T ∩ B(0, ρ)`, `g` and `Σ aₙ zⁿ` are both analytic and agree near `0`.
   The identity theorem makes them agree on all of it.
3. So near `ρ`, `Σ bₙ zⁿ` agrees with `g + Σ eₙ zⁿ`, which is analytic at `ρ`.
4. Pringsheim (`GppPringsheim.pringsheim`) then gives convergence past `ρ`, which contradicts
   the choice of `ρ`.

**Use.** For `H(z) = (ξ'/ξ)((2+z)/(1−z))`, the real segment `[0, 1)` maps to real `s ≥ 2`,
where `ξ` has no zeros. So `H` is analytic there, unconditionally. Take `aₙ` to be the Taylor
coefficients of `H` and `eₙ` a one-sided majorant with radius one: `E⁺ₙ` plus the bounded
Archimedean part, as in Codex's §R. The theorem then says `H` has radius one, i.e. no zeros
of `ξ` with `Re s > 1/2`. That arithmetic input, a subexponential one-sided bound on the prime
side `Eₙ`, is **open and RH-strength**, and it is not assumed or claimed anywhere in this file.
Only the analytic implication is proved here.
-/

namespace GppOneSidedPringsheim

open Metric Set Filter Topology GppPringsheim

/-- A real power series that converges absolutely on `[0, ρ)` defines an analytic function on
the open disc of radius `ρ`. -/
theorem analyticAt_h (c : ℕ → ℝ) {ρ : ℝ}
    (hc : ∀ r, 0 ≤ r → r < ρ → Summable (fun n => |c n| * r ^ n))
    {z : ℂ} (hz : ‖z‖ < ρ) : AnalyticAt ℂ (h c) z := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n => (c n : ℂ))
  have hpe : h c = p.sum := by
    funext w
    simp only [h, FormalMultilinearSeries.sum, p, FormalMultilinearSeries.ofScalars_apply_eq',
      smul_eq_mul]
  obtain ⟨r, hzr, hrρ⟩ := exists_between hz
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hrad : ENNReal.ofReal r ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    refine (hc r hr0 hrρ).congr (fun n => ?_)
    simp [p, Complex.norm_real, Real.norm_eq_abs,
      Real.coe_toNNReal r hr0]
  have hzlt : ‖z‖ₑ < p.radius := by
    refine lt_of_lt_of_le ?_ hrad
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hzr
  have hpos : 0 < p.radius := pos_of_gt hzlt
  rw [hpe]
  refine (p.hasFPowerSeriesOnBall hpos).analyticAt_of_mem ?_
  simpa [Metric.mem_eball, edist_zero_right] using hzlt

theorem summable_of_oneSided (a e : ℕ → ℝ) (hpos : ∀ n, 0 ≤ a n + e n)
    (he : ∀ r, 0 ≤ r → r < 1 → Summable (fun n => |e n| * r ^ n))
    {R : ℝ} (hR : 0 < R)
    (ha : ∀ r, 0 ≤ r → r < R → Summable (fun n => |a n| * r ^ n))
    {g : ℂ → ℂ} (hg : ∀ x : ℝ, 0 ≤ x → x < 1 → AnalyticAt ℂ g x)
    (hgh : ∀ z : ℂ, ‖z‖ < R → g z = h a z) :
    ∀ r, 0 ≤ r → r < 1 → Summable (fun n => |a n| * r ^ n) := by
  set b : ℕ → ℝ := fun n => a n + e n with hbdef
  have hb0 : ∀ n, 0 ≤ b n := hpos
  -- |a| ≤ b + |e|
  have habs : ∀ n, |a n| ≤ b n + |e n| := by
    intro n
    have h1 : a n = b n - e n := by simp [hbdef]
    rw [h1]
    calc |b n - e n| ≤ |b n| + |e n| := abs_sub _ _
      _ = b n + |e n| := by rw [abs_of_nonneg (hb0 n)]
  -- b ≤ |a| + |e|
  have hbabs : ∀ n, b n ≤ |a n| + |e n| := fun n =>
    add_le_add (le_abs_self _) (le_abs_self _)
  -- monotonicity of summability for nonnegative coefficients
  have hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → Summable (fun n => b n * t ^ n) →
      Summable (fun n => b n * s ^ n) := by
    intro s t hs hst hsum
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hb0 n) (pow_nonneg hs n))
      (fun n => ?_) hsum
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst n) (hb0 n)
  have hb_of : ∀ r, 0 ≤ r → r < 1 → Summable (fun n => b n * r ^ n) →
      Summable (fun n => |a n| * r ^ n) := by
    intro r hr hr1 hs
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hr n))
      (fun n => ?_) (hs.add (he r hr hr1))
    have := mul_le_mul_of_nonneg_right (habs n) (pow_nonneg hr n)
    linarith [this]
  intro r0 hr0 hr01
  apply hb_of r0 hr0 hr01
  by_contra hns
  -- below `m = min R 1` everything converges
  set m : ℝ := min R 1 with hmdef
  have hm0 : 0 < m := lt_min hR one_pos
  have hbm : ∀ r, 0 ≤ r → r < m → Summable (fun n => b n * r ^ n) := by
    intro r hr hrm
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hb0 n) (pow_nonneg hr n))
      (fun n => mul_le_mul_of_nonneg_right (hbabs n) (pow_nonneg hr n)) ?_
    simp_rw [add_mul]
    exact (ha r hr (lt_of_lt_of_le hrm (min_le_left _ _))).add
      (he r hr (lt_of_lt_of_le hrm (min_le_right _ _)))
  have hr0m : m ≤ r0 := by
    by_contra hlt
    exact hns (hbm r0 hr0 (lt_of_not_ge hlt))
  -- the set of convergence points in [0, r0] and its supremum
  set S : Set ℝ := {r | 0 ≤ r ∧ r ≤ r0 ∧ Summable (fun n => b n * r ^ n)} with hS
  have hSbdd : BddAbove S := ⟨r0, fun r hr => hr.2.1⟩
  have hm2S : m / 2 ∈ S := ⟨by positivity, by linarith, hbm _ (by positivity) (by linarith)⟩
  set ρ : ℝ := sSup S with hρdef
  have hρpos : 0 < ρ := lt_of_lt_of_le (half_pos hm0) (le_csSup hSbdd hm2S)
  have hρr0 : ρ ≤ r0 := csSup_le ⟨_, hm2S⟩ (fun r hr => hr.2.1)
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρr0 hr01
  have hconvρ : ∀ r, 0 ≤ r → r < ρ → Summable (fun n => b n * r ^ n) := by
    intro r hr hrρ
    obtain ⟨s, hsS, hrs⟩ := exists_lt_of_lt_csSup ⟨_, hm2S⟩ hrρ
    exact hmono r s hr hrs.le hsS.2.2
  have haρ : ∀ r, 0 ≤ r → r < ρ → Summable (fun n => |a n| * r ^ n) :=
    fun r hr hrρ => hb_of r hr (by linarith) (hconvρ r hr hrρ)
  -- a convex neighbourhood of the segment [0, ρ] on which g is analytic
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc 0 ρ with hKdef
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKconv : Convex ℝ K := by
    have := (convex_Icc (0 : ℝ) ρ).linear_image Complex.ofRealCLM.toLinearMap
    simpa [hKdef] using this
  have hO : IsOpen {z : ℂ | AnalyticAt ℂ g z} := isOpen_analyticAt ℂ g
  have hKO : K ⊆ {z : ℂ | AnalyticAt ℂ g z} := by
    rintro _ ⟨x, ⟨hx0, hxρ⟩, rfl⟩
    exact hg x hx0 (by linarith)
  obtain ⟨δ, hδ, hT⟩ := hKc.exists_thickening_subset_open hO hKO
  set U : Set ℂ := thickening δ K ∩ ball (0 : ℂ) ρ with hUdef
  have hUconv : Convex ℝ U := (hKconv.thickening δ).inter (convex_ball _ _)
  have h0K : (0 : ℂ) ∈ K := ⟨0, ⟨le_rfl, hρpos.le⟩, by simp⟩
  have h0U : (0 : ℂ) ∈ U := ⟨self_subset_thickening hδ K h0K, mem_ball_self hρpos⟩
  have hgU : AnalyticOnNhd ℂ g U := fun z hz => hT hz.1
  have haU : AnalyticOnNhd ℂ (h a) U := fun z hz =>
    analyticAt_h a haρ (by simpa [mem_ball_zero_iff] using hz.2)
  have heq0 : g =ᶠ[𝓝 0] h a := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hm0] with z hz
    exact hgh z (lt_of_lt_of_le (mem_ball_zero_iff.mp hz) (min_le_left _ _))
  have hEq := hgU.eqOn_of_preconnected_of_eventuallyEq haU hUconv.isPreconnected h0U heq0
  -- on the disc of radius ρ, h b = h a + h e
  have hsplit : ∀ z : ℂ, ‖z‖ < ρ → h b z = h a z + h e z := by
    intro z hz
    have hza : Summable (fun n => (a n : ℂ) * z ^ n) := by
      refine Summable.of_norm ((haρ ‖z‖ (norm_nonneg _) hz).congr (fun n => ?_))
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hze : Summable (fun n => (e n : ℂ) * z ^ n) := by
      refine Summable.of_norm ((he ‖z‖ (norm_nonneg _) (by linarith)).congr (fun n => ?_))
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    simp only [h]
    rw [← hza.tsum_add hze]
    refine tsum_congr (fun n => ?_)
    simp only [hbdef]; push_cast; ring
  -- the continuation G
  set G : ℂ → ℂ := fun z => if ‖z‖ < ρ then h b z else g z + h e z with hGdef
  have hGeq : ∀ z : ℂ, ‖z‖ < ρ → G z = h b z := fun z hz => if_pos hz
  have hρn : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
  have hgeAt : AnalyticAt ℂ (fun z => g z + h e z) (ρ : ℂ) :=
    (hg ρ hρpos.le hρ1).add (analyticAt_h e he (by rw [hρn]; exact hρ1))
  have hρK : (ρ : ℂ) ∈ K := ⟨ρ, ⟨hρpos.le, le_rfl⟩, rfl⟩
  have hGat : AnalyticAt ℂ G (ρ : ℂ) := by
    refine hgeAt.congr ?_
    filter_upwards [ball_mem_nhds (ρ : ℂ) hδ] with z hz
    simp only [hGdef]
    split_ifs with hzρ
    · have hzU : z ∈ U :=
        ⟨mem_thickening_iff.mpr ⟨ρ, hρK, hz⟩, mem_ball_zero_iff.mpr hzρ⟩
      rw [hsplit z hzρ, hEq hzU]
    · rfl
  obtain ⟨r', hr'ρ, hr'sum⟩ := pringsheim b hb0 hρpos hconvρ hGat hGeq
  by_cases hr'0 : r' ≤ r0
  · have hr'S : r' ∈ S := ⟨by linarith, hr'0, hr'sum⟩
    linarith [le_csSup hSbdd hr'S]
  · exact hns (hmono r0 r' hr0 (by linarith) hr'sum)

end GppOneSidedPringsheim
