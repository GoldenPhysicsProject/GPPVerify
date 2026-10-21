import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Landau's theorem for Laplace transforms with nonnegative integrand

The continuous companion of `GppLandau.landau` (Dirichlet series) and `GppPringsheim.pringsheim`
(power series). Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.

* `summable_of_nonneg_coeffs`: if `F` is holomorphic on `B(x, R)` and agrees near `x` with the power
  series `Σ cₖ (x − z)^k`, then `Σ cₖ ρ^k` converges for every `0 ≤ ρ < R` (Taylor coefficients of `F`
  are those of the series, `iteratedDeriv_eq_of_hasFPowerSeriesAt`).
* `lintegral_shift_eq_tsum` (Tonelli): for `g ≥ 0`, `∫₀^∞ g e^{−(x−ρ)t} = Σₙ ρⁿ/n! ∫₀^∞ tⁿ g e^{−xt}`.
* `hasFPowerSeriesAt_laplace`: if `∫₀^∞ g e^{−x't} < ∞` and `x > x'`, the Laplace transform
  `laplace g z = ∫₀^∞ g(t) e^{−zt} dt` has the power series `Σ (−1)ⁿ mₙ/n! (z − x)ⁿ` at `x`, with
  `mₙ = ∫₀^∞ tⁿ g e^{−xt}` (sum and integral exchanged by `hasSum_integral_of_summable_integral_norm`).
* `lintegral_lt_top_of_holomorphic`: a holomorphic `F` on `B(x, R)` equal to `laplace g` near `x`
  forces `∫₀^∞ g e^{−yt} < ∞` for real `y ∈ (x − R, x]`.
* `landau_laplace`: if the integral converges for `s > σ` and diverges for `s < σ`, the Laplace
  transform has no holomorphic extension to `{re s > σ} ∪ B(σ, ε)` (Landau).

**Use (not formalized here).** This is the analytic half of the one-sided criterion for the prime
signal `J(t) = ∫₁^{e^t} (ψ(x) − x) x^{−3/2} dx`. Suppose `g(t) = J(t) − κ − R(t) + C(1+t)^k ≥ 0` for all
`t`. Its Laplace transform differs from `L[J](z) = −[ζ'/ζ(z+½) + 1/(z−½) + 1] / (z(z+½))` by terms
whose only singularities are at `z ≤ 0`. If some zero had `Re ρ > ½`, the abscissa of `g` would be a
positive real number, and `landau_laplace` would put a singularity there; but `ζ` has no real zeros in
`(½, 1)` and the pole at `z = ½` cancels, so there is none. The arithmetic bound on `J` is
RH-strength and open, and the zeta identity is not formalized here. Nothing here claims RH.
-/

open MeasureTheory Set Complex
open scoped Nat ENNReal

namespace GppLandauLaplace

/-- Coefficients of a power series at `x` read off from any holomorphic function agreeing with it
near `x`: `iteratedDeriv k F x = k! · aₖ`. -/
lemma iteratedDeriv_eq_of_hasFPowerSeriesAt {F G : ℂ → ℂ} {x : ℂ} {a : ℕ → ℂ}
    (hG : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ a) x) (hFG : F =ᶠ[nhds x] G)
    (k : ℕ) : iteratedDeriv k F x = (k ! : ℂ) * a k := by
  rw [hFG.iteratedDeriv_eq]
  obtain ⟨r, hr⟩ := hG
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hr.factorial_smul 1 k,
    FormalMultilinearSeries.ofScalars_apply_eq]
  simp [nsmul_eq_mul]

/-- **Nonnegative Taylor coefficients force convergence on the whole disc of holomorphy.** If `F` is
holomorphic on `B(x, R)` and agrees near `x` with `Σ cₖ (x − z)^k`, `cₖ ≥ 0`, then
`Σ cₖ ρ^k < ∞` for every `0 ≤ ρ < R`. -/
theorem summable_of_nonneg_coeffs {F G : ℂ → ℂ} {x : ℝ} {R : ℝ} {c : ℕ → ℝ}
    (hG : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ
      (fun k => ((-1 : ℂ) ^ k * c k))) (x : ℂ))
    (hFG : F =ᶠ[nhds (x : ℂ)] G) (hF : DifferentiableOn ℂ F (Metric.ball (x : ℂ) R))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < R) : Summable fun k => c k * ρ ^ k := by
  have hmem : ((x - ρ : ℝ) : ℂ) ∈ Metric.ball (x : ℂ) R := by
    rw [Metric.mem_ball, dist_eq, ofReal_sub, sub_sub_cancel_left, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ
  have hT := Complex.hasSum_taylorSeries_on_ball hF hmem
  have hterm : ∀ k, ((k ! : ℂ)⁻¹ • (((x - ρ : ℝ) : ℂ) - x) ^ k • iteratedDeriv k F x) =
      ((c k * ρ ^ k : ℝ) : ℂ) := by
    intro k
    rw [iteratedDeriv_eq_of_hasFPowerSeriesAt hG hFG k]
    have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    push_cast
    simp only [smul_eq_mul, sub_sub_cancel_left]
    field_simp
    rw [neg_pow]
    have h1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    linear_combination (↑ρ ^ k * ↑(c k)) * h1
  simp_rw [hterm] at hT
  exact Complex.summable_ofReal.mp hT.summable



lemma hasSum_exp_real (a : ℝ) : HasSum (fun n : ℕ => a ^ n / n !) (Real.exp a) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp a

lemma hasSum_exp_complex (a : ℂ) : HasSum (fun n : ℕ => a ^ n / n !) (Complex.exp a) := by
  rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp a

/-- The (one-sided) Laplace transform of `g` on `(0, ∞)`. -/
noncomputable def laplace (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (g t : ℂ) * Complex.exp (-z * t)

/-- The `n`-th moment of `g · e^{−xt}` on `(0, ∞)`. -/
noncomputable def moment (g : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ n * g t * Real.exp (-x * t)

lemma meas_moment {g : ℝ → ℝ} (hgm : Measurable g) (x : ℝ) (n : ℕ) :
    Measurable fun t : ℝ => t ^ n * g t * Real.exp (-x * t) :=
  ((measurable_id.pow_const n).mul hgm).mul
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))

theorem lintegral_shift_eq_tsum {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g)
    (x ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-(x - ρ) * t)) =
      ∑' n : ℕ, ENNReal.ofReal (ρ ^ n / n !) *
        ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n * g t * Real.exp (-x * t)) := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (g t * Real.exp (-(x - ρ) * t)) =
      ∑' n : ℕ, ENNReal.ofReal (ρ ^ n / n !) * ENNReal.ofReal (t ^ n * g t * Real.exp (-x * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hs := (hasSum_exp_real (ρ * t)).mul_left (g t * Real.exp (-x * t))
    have heq : g t * Real.exp (-(x - ρ) * t) = g t * Real.exp (-x * t) * Real.exp (ρ * t) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [heq, ← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg]
    · congr 1; funext n
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [mul_pow]; ring
    · intro n; have := hg t; positivity
    · exact hs.summable
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_tsum]
  · congr 1; funext n
    rw [lintegral_const_mul]
    exact ENNReal.measurable_ofReal.comp (meas_moment hgm x n)
  · intro n
    exact (measurable_const.mul (ENNReal.measurable_ofReal.comp (meas_moment hgm x n))).aemeasurable

/-- Finiteness transfer: if `g e^{−x' t}` has finite integral and `x − ρ ≥ x'`, `ρ ≥ 0`, then the
weighted moment sum at `x` is finite. -/
theorem tsum_moment_lt_top {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g) {x' x ρ : ℝ}
    (hρ : 0 ≤ ρ) (hxρ : x' ≤ x - ρ)
    (hfin : ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-x' * t)) < ⊤) :
    ∑' n : ℕ, ENNReal.ofReal (ρ ^ n / n !) *
        ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n * g t * Real.exp (-x * t)) < ⊤ := by
  rw [← lintegral_shift_eq_tsum hg hgm x ρ hρ]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_) hfin
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (hg t)
  apply Real.exp_le_exp.mpr
  have : (0 : ℝ) ≤ t := le_of_lt ht
  nlinarith

/-- Each weighted moment is finite once the shifted integral is. -/
theorem lintegral_moment_lt_top {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g) {x' x : ℝ}
    (hx : x' < x) (hfin : ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-x' * t)) < ⊤) (n : ℕ) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n * g t * Real.exp (-x * t)) < ⊤ := by
  set r := x - x' with hr
  have hr0 : 0 < r := by simp [hr]; linarith
  have hsum := tsum_moment_lt_top hg hgm (x' := x') (x := x) hr0.le (by simp [hr]) hfin
  have hle := ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal (r ^ n / n !) *
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n * g t * Real.exp (-x * t))) n
  have hpos : ENNReal.ofReal (r ^ n / n !) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have h2 := lt_of_le_of_lt hle hsum
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h, ENNReal.mul_top hpos] at h2
  exact lt_irrefl _ h2

theorem integrableOn_moment {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g) {x' x : ℝ}
    (hx : x' < x) (hfin : ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-x' * t)) < ⊤) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * g t * Real.exp (-x * t)) (Ioi 0) := by
  rw [IntegrableOn, ← lintegral_ofReal_ne_top_iff_integrable]
  · exact (lintegral_moment_lt_top hg hgm hx hfin n).ne
  · exact (meas_moment hgm x n).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have := hg t; have : (0:ℝ) ≤ t := le_of_lt ht; simp only [Pi.zero_apply]; positivity

lemma moment_nonneg {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (x : ℝ) (n : ℕ) : 0 ≤ moment g x n := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht; have := hg t; have : (0:ℝ) ≤ t := le_of_lt ht; positivity

theorem ofReal_moment {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g) {x' x : ℝ}
    (hx : x' < x) (hfin : ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-x' * t)) < ⊤) (n : ℕ) :
    ENNReal.ofReal (moment g x n) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n * g t * Real.exp (-x * t)) := by
  rw [moment, ofReal_integral_eq_lintegral_ofReal (integrableOn_moment hg hgm hx hfin n)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have := hg t; have : (0:ℝ) ≤ t := le_of_lt ht; simp only [Pi.zero_apply]; positivity

/-- The weighted moment series is summable in `ℝ` for `0 ≤ ρ ≤ x − x'`. -/
theorem summable_moment {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g) {x' x ρ : ℝ}
    (hx : x' < x) (hρ : 0 ≤ ρ) (hxρ : x' ≤ x - ρ)
    (hfin : ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-x' * t)) < ⊤) :
    Summable fun n : ℕ => ρ ^ n / n ! * moment g x n := by
  have h := tsum_moment_lt_top hg hgm hρ hxρ hfin
  have hEq : ∀ n : ℕ, ENNReal.ofReal (ρ ^ n / n !) *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n * g t * Real.exp (-x * t)) =
      ENNReal.ofReal (ρ ^ n / n ! * moment g x n) := by
    intro n
    rw [← ofReal_moment hg hgm hx hfin, ← ENNReal.ofReal_mul (by positivity)]
  rw [tsum_congr hEq] at h
  have := ENNReal.summable_toReal h.ne
  refine this.congr fun n => ?_
  rw [ENNReal.toReal_ofReal]
  have := moment_nonneg hg x n; positivity

/-- Coefficients `(−1)ⁿ mₙ / n!` of the Laplace transform at `x`. -/
noncomputable def coeff (g : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℂ := (-1) ^ n * ((moment g x n / n ! : ℝ) : ℂ)

/-- Pointwise expansion of the Laplace kernel. -/
lemma hasSum_kernel (g : ℝ → ℝ) (x : ℝ) (y : ℂ) (t : ℝ) :
    HasSum (fun n : ℕ => (-y) ^ n / n ! * (((t ^ n * g t * Real.exp (-x * t)) : ℝ) : ℂ))
      ((g t : ℂ) * Complex.exp (-((x : ℂ) + y) * t)) := by
  have hs := (hasSum_exp_complex (-y * t)).mul_left ((g t : ℂ) * Complex.exp (-(x : ℂ) * t))
  have hf : (fun n : ℕ => (-y) ^ n / n ! * (((t ^ n * g t * Real.exp (-x * t)) : ℝ) : ℂ)) =
      fun i => (g t : ℂ) * Complex.exp (-(x : ℂ) * t) * ((-y * t) ^ i / i !) := by
    funext n; push_cast; rw [mul_pow]; ring
  have hv : (g t : ℂ) * Complex.exp (-((x : ℂ) + y) * t) =
      (g t : ℂ) * Complex.exp (-(x : ℂ) * t) * Complex.exp (-y * t) := by
    rw [mul_assoc, ← Complex.exp_add]; ring_nf
  rw [hf, hv]; exact hs

/-- **The Laplace transform is analytic to the right of its abscissa**, with the moment power
series at `x`. -/
theorem hasFPowerSeriesAt_laplace {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g)
    {x' x : ℝ} (hx : x' < x)
    (hfin : ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-x' * t)) < ⊤) :
    HasFPowerSeriesAt (laplace g) (FormalMultilinearSeries.ofScalars ℂ (coeff g x)) (x : ℂ) := by
  set r : NNReal := ⟨(x - x') / 2, by linarith⟩ with hr
  have hrv : (r : ℝ) = (x - x') / 2 := rfl
  have hr0 : (0 : ℝ) < r := by rw [hrv]; linarith
  refine ⟨r, ?_, by exact_mod_cast hr0, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_summable
    have := summable_moment hg hgm (ρ := r) hx hr0.le (by rw [hrv]; linarith) hfin
    refine this.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, coeff, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := moment_nonneg hg x n; positivity)]
    ring
  · intro y hy
    have hyr : ‖y‖ < (r : ℝ) := by
      rw [Metric.mem_eball, edist_zero_right] at hy
      have h' : ‖y‖₊ < r := by simpa [enorm, ENNReal.coe_lt_coe] using hy
      exact_mod_cast h'
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    set F : ℕ → ℝ → ℂ := fun n t => (-y) ^ n / n ! * (((t ^ n * g t * Real.exp (-x * t)) : ℝ) : ℂ)
    have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
      ((integrableOn_moment hg hgm hx hfin n).ofReal).const_mul _
    have hnorm : ∀ n, (∫ t in Ioi (0 : ℝ), ‖F n t‖) = ‖y‖ ^ n / n ! * moment g x n := by
      intro n
      have : ∀ t ∈ Ioi (0 : ℝ), ‖F n t‖ = ‖y‖ ^ n / n ! * (t ^ n * g t * Real.exp (-x * t)) := by
        intro t ht
        have := hg t; have : (0:ℝ) ≤ t := le_of_lt ht
        simp only [F, norm_mul, norm_div, norm_pow, norm_neg, norm_real, Real.norm_eq_abs,
          Complex.norm_natCast]
        rw [abs_of_nonneg (hg t), abs_of_pos (Real.exp_pos _)]
        try rw [abs_of_nonneg this]
      rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul, moment]
    have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
      simp_rw [hnorm]
      exact summable_moment hg hgm (ρ := ‖y‖) hx (norm_nonneg y) (by linarith) hfin
    have H := hasSum_integral_of_summable_integral_norm hint hsum
    have hval : (∫ t in Ioi (0 : ℝ), ∑' n, F n t) = laplace g ((x : ℂ) + y) := by
      rw [laplace]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      exact (hasSum_kernel g x y t).tsum_eq
    rw [hval] at H
    convert H using 1
    funext n
    simp only [F, coeff]
    rw [integral_const_mul, integral_complex_ofReal, ← moment]
    push_cast
    rw [neg_pow y]
    field_simp


/-- **Landau's theorem for Laplace transforms (core).** Let `g ≥ 0` be measurable with
`∫₀^∞ g e^{−x' t} < ∞`, and let `x > x'`. If `F` is holomorphic on `B(x, R)` and equals the Laplace
transform of `g` near `x`, then `∫₀^∞ g e^{−y t} < ∞` for every real `y ≤ x` with `x − y < R`. -/
theorem lintegral_lt_top_of_holomorphic {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g)
    {x' x : ℝ} (hx : x' < x)
    (hfin : ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-x' * t)) < ⊤)
    {F : ℂ → ℂ} {R : ℝ} (hF : DifferentiableOn ℂ F (Metric.ball (x : ℂ) R))
    (hFL : F =ᶠ[nhds (x : ℂ)] laplace g) {y : ℝ} (hy : y ≤ x) (hyR : x - y < R) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-y * t)) < ⊤ := by
  set ρ := x - y with hρdef
  have hρ : 0 ≤ ρ := by simp [hρdef]; linarith
  have hsum := summable_of_nonneg_coeffs (c := fun k => moment g x k / k !)
    (hasFPowerSeriesAt_laplace hg hgm hx hfin) hFL hF hρ hyR
  have hy' : y = x - ρ := by simp [hρdef]
  rw [hy', lintegral_shift_eq_tsum hg hgm x ρ hρ]
  have hEq : ∀ n : ℕ, ENNReal.ofReal (ρ ^ n / n !) *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ n * g t * Real.exp (-x * t)) =
      ENNReal.ofReal (moment g x n / n ! * ρ ^ n) := by
    intro n
    rw [← ofReal_moment hg hgm hx hfin, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  rw [tsum_congr hEq, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by
    have := moment_nonneg hg x n; positivity) hsum]
  exact ENNReal.ofReal_lt_top

/-- **Landau's theorem for Laplace transforms.** Let `g ≥ 0` be measurable, and let `σ` be the
abscissa of convergence of `∫₀^∞ g e^{−st} dt`: finite for every real `s > σ`, infinite for every
real `s < σ`. Then the Laplace transform has no holomorphic extension to the half-plane `re s > σ`
together with a disc around `σ`: the real point of the abscissa is a singularity. -/
theorem landau_laplace {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g) {σ : ℝ}
    (hconv : ∀ s : ℝ, σ < s → ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-s * t)) < ⊤)
    (hdiv : ∀ s : ℝ, s < σ → ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-s * t)) = ⊤)
    {F : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hF : DifferentiableOn ℂ F ({s | σ < s.re} ∪ Metric.ball (σ : ℂ) ε))
    (heq : Set.EqOn F (laplace g) {s | σ < s.re}) : False := by
  set x : ℝ := σ + ε / 4
  set y : ℝ := σ - ε / 8
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hxmem : (x : ℂ) ∈ {s : ℂ | σ < s.re} := by
    simp only [Set.mem_ofPred_eq, Complex.ofReal_re, x]; linarith
  have hFL : F =ᶠ[nhds (x : ℂ)] laplace g := heq.eventuallyEq_of_mem (hopen.mem_nhds hxmem)
  have hball : Metric.ball (x : ℂ) (ε / 2) ⊆ {s | σ < s.re} ∪ Metric.ball (σ : ℂ) ε := by
    intro z hz
    by_cases h : σ < z.re
    · exact Or.inl h
    · right
      rw [Metric.mem_ball] at hz ⊢
      have hxσ : dist (x : ℂ) σ = ε / 4 := by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by simp [x]; linarith)]
        simp [x]
      calc dist z σ ≤ dist z x + dist (x : ℂ) σ := dist_triangle _ _ _
        _ < ε / 2 + ε / 4 := by rw [hxσ]; linarith
        _ < ε := by linarith
  have hx' : σ + ε / 8 < x := by simp [x]; linarith
  have hfin := hconv (σ + ε / 8) (by linarith)
  have h := lintegral_lt_top_of_holomorphic hg hgm hx' hfin (hF.mono hball) hFL
    (y := y) (by simp [x, y]; linarith) (by simp [x, y]; linarith)
  rw [hdiv y (by simp [y]; linarith)] at h
  exact lt_irrefl _ h

end GppLandauLaplace
