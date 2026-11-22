/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statement from Codex / GPT, audited by Turbo)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import GppVerify.RiemannHypothesis.OneSided
import GppVerify.RiemannHypothesis.HeartLandauReduction
import GppVerify.RiemannHypothesis.CausalKernels
import GppVerify.RiemannHypothesis.CausalTailEstimate
import GppVerify.RiemannHypothesis.CausalNormBounds

/-!
# Transforms of the causal kernels at a zero (Part C of the causal proof of `EnergyZeroInequality`)

**Unconditional; this is a lemma, not RH.** Part C of the four-part formalization of Codex's causal
proof (`causal_zero_bound.md` §2, last paragraph, GPPDiscovery2 `cae0656`, Turbo-audited).

Let `lap f s = ∫₀^∞ e^{-st} f(t) dt`. Main results, with `Z = ν ∗ w`, `k = ν ∗ w′`:

* `lap_w`, `lap_wd`: `ŵ(s) = (s − ½)/(1+s)⁴` and `ŵ′(s) = s(s − ½)/(1+s)⁴` for `Re s > −1`
  (explicit antiderivatives `laplace_pow1/2/3`; the exact transforms of `g₂, g₃, g₄`).
* `lap_nuConv`: the Dirichlet-series interchange. For `Re s > 1/2` and causal `f` with `e^{-σu}|f|`
  integrable, `lap (ν ∗ f)(s) = ζ(1/2 + s) · lap f (s)`.
* `hasDerivAt_lap`: signed Laplace holomorphy on `Re w > σ₀` when `e^{-τt}|f|` is integrable for all
  `τ > σ₀`; used for `Z ∈ L²` and `k ∈ L¹` on `Re s > 0` (`differentiableOn_lap_Z`, `…_kk`).
* **The identity-theorem step** (`lap_Z_eq`, `lap_kk_eq`): `lap Z = G_z` and `lap k = G_k` on the
  whole half-plane `Re s > 0`, where `G_z(s) = Ê(1/2+s)/(1+s)⁴`, `G_k(s) = s Ê(1/2+s)/(1+s)⁴` and
  `Ê(s') = 2 ξ_E(s')/(s' Γℝ(s'))`. Both sides are holomorphic on the open convex (so
  preconnected) half-plane `{Re s > 0}` — the left side by `Z ∈ L²`, `k ∈ L¹` (Part D2), the right
  side because `ξ_E` and `1/Γℝ` are entire and `1/2 + s ≠ 0`, `1 + s ≠ 0` there — and they agree on
  the open nonempty set `{Re s > 1/2}` (`lap_Z_eq_right`, `lap_kk_eq_right`, from `lap_nuConv`), so
  they agree on `{Re s > 0}` (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`). `Ê` equals
  `(s' − 1) ζ(s')` off `s' ∈ {0, 1}` (`zetaRes_eq`), which is why the pole of `ζ` at `s' = 1`
  (`s = 1/2`) needs no removable-singularity theorem and no punctured domain.
* At a zero `r` of `ζ(1/2 + ·)` with `Re r > 0`, `r ≠ 1/2`: `lap_kk_at_zero` (`k̂(r) = 0`),
  `lap_Z_at_zero` (`Ẑ(r) = 0`) and `lap_hh_at_zero` (`ĥ(r) = (r − 1/2)/(1 + r)⁴`, `h = w − cZ`).

The case `r = 1/2` is not covered here (the weight `‖r − 1/2‖` vanishes there; the final assembly
handles it trivially). **Not in this file:** the final `energyZeroInequality_causal`.
-/

open MeasureTheory Set Filter Topology GppCausalKernels

namespace GppCausalTransforms
theorem tendsto_pow_exp (c : ℂ) (hc : 0 < c.re) (m : ℕ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-c * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) c.re hc
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, Real.rpow_natCast,
    Real.norm_eq_abs, abs_of_nonneg ht]
  congr 2
  simp

theorem integrableOn_pow_exp (c : ℂ) (hc : 0 < c.re) (m : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-c * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (m : ℝ)) (b := c.re)
    (by have : (0:ℝ) ≤ m := by positivity
        linarith) one_pos hc
  refine Integrable.mono' h ?_ ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun t ht => ?_))
  · exact (Complex.continuous_ofReal.pow m |>.mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · have ht0 : 0 ≤ t := le_of_lt ht
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, Real.rpow_natCast,
      Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg ht0]
    refine le_of_eq ?_
    congr 2
    simp


theorem hasDerivAt_pow_exp (c : ℂ) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-c * t))
      ((m : ℂ) * (t : ℂ) ^ (m - 1) * Complex.exp (-c * t) -
        c * ((t : ℂ) ^ m * Complex.exp (-c * t))) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ m) ((m : ℂ) * (t : ℂ) ^ (m - 1)) t := by
    exact (h1.pow m).congr_deriv (by simp)
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp (-c * t)) (-c * Complex.exp (-c * t)) t := by
    have := (h1.const_mul (-c)).cexp
    simpa [mul_comm] using this
  refine (h2.mul h3).congr_deriv ?_
  ring

theorem ftc_Ioi (f F : ℝ → ℂ) (hF : ∀ t, HasDerivAt F (f t) t) (hint : IntegrableOn f (Ioi 0))
    (hlim : Tendsto F atTop (𝓝 0)) : ∫ t in Ioi (0:ℝ), f t = - F 0 := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0:ℝ)) (hF 0).continuousAt.continuousWithinAt
    (fun x _ => hF x) hint hlim
  simpa using this

theorem laplace_pow1 (c : ℂ) (hc : 0 < c.re) :
    ∫ t in Ioi (0:ℝ), (t : ℂ) ^ 1 * Complex.exp (-c * t) = 1 / c ^ 2 := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hF : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => -(1 / c) * ((t : ℂ) ^ 1 * Complex.exp (-c * t)) -
        (1 / c ^ 2) * ((t : ℂ) ^ 0 * Complex.exp (-c * t)))
      ((t : ℂ) ^ 1 * Complex.exp (-c * t)) t := by
    intro t
    have := ((hasDerivAt_pow_exp c 1 t).const_mul (-(1 / c))).sub
      ((hasDerivAt_pow_exp c 0 t).const_mul (1 / c ^ 2))
    refine this.congr_deriv ?_
    field_simp
    ring
  rw [ftc_Ioi _ _ hF (integrableOn_pow_exp c hc 1)]
  · simp
  · have h1 := tendsto_pow_exp c hc 1
    have h0 := tendsto_pow_exp c hc 0
    have := (h1.const_mul (-(1 / c))).sub (h0.const_mul (1 / c ^ 2))
    simpa using this


theorem laplace_pow2 (c : ℂ) (hc : 0 < c.re) :
    ∫ t in Ioi (0:ℝ), (t : ℂ) ^ 2 * Complex.exp (-c * t) = 2 / c ^ 3 := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hF : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => -(1 / c) * ((t : ℂ) ^ 2 * Complex.exp (-c * t)) -
        (2 / c ^ 2) * ((t : ℂ) ^ 1 * Complex.exp (-c * t)) -
        (2 / c ^ 3) * ((t : ℂ) ^ 0 * Complex.exp (-c * t)))
      ((t : ℂ) ^ 2 * Complex.exp (-c * t)) t := by
    intro t
    have := (((hasDerivAt_pow_exp c 2 t).const_mul (-(1 / c))).sub
      ((hasDerivAt_pow_exp c 1 t).const_mul (2 / c ^ 2))).sub
      ((hasDerivAt_pow_exp c 0 t).const_mul (2 / c ^ 3))
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, zero_mul, pow_zero, one_mul,
      Nat.sub_self, mul_one]
    field_simp
    ring
  rw [ftc_Ioi _ _ hF (integrableOn_pow_exp c hc 2)]
  · simp
  · have h2 := tendsto_pow_exp c hc 2
    have h1 := tendsto_pow_exp c hc 1
    have h0 := tendsto_pow_exp c hc 0
    have := ((h2.const_mul (-(1 / c))).sub (h1.const_mul (2 / c ^ 2))).sub (h0.const_mul (2 / c ^ 3))
    simpa using this

theorem laplace_pow3 (c : ℂ) (hc : 0 < c.re) :
    ∫ t in Ioi (0:ℝ), (t : ℂ) ^ 3 * Complex.exp (-c * t) = 6 / c ^ 4 := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hF : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => -(1 / c) * ((t : ℂ) ^ 3 * Complex.exp (-c * t)) -
        (3 / c ^ 2) * ((t : ℂ) ^ 2 * Complex.exp (-c * t)) -
        (6 / c ^ 3) * ((t : ℂ) ^ 1 * Complex.exp (-c * t)) -
        (6 / c ^ 4) * ((t : ℂ) ^ 0 * Complex.exp (-c * t)))
      ((t : ℂ) ^ 3 * Complex.exp (-c * t)) t := by
    intro t
    have := ((((hasDerivAt_pow_exp c 3 t).const_mul (-(1 / c))).sub
      ((hasDerivAt_pow_exp c 2 t).const_mul (3 / c ^ 2))).sub
      ((hasDerivAt_pow_exp c 1 t).const_mul (6 / c ^ 3))).sub
      ((hasDerivAt_pow_exp c 0 t).const_mul (6 / c ^ 4))
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, zero_mul, pow_zero, one_mul,
      Nat.sub_self, mul_one]
    field_simp
    ring
  rw [ftc_Ioi _ _ hF (integrableOn_pow_exp c hc 3)]
  · simp
  · have h3 := tendsto_pow_exp c hc 3
    have h2 := tendsto_pow_exp c hc 2
    have h1 := tendsto_pow_exp c hc 1
    have h0 := tendsto_pow_exp c hc 0
    have := (((h3.const_mul (-(1 / c))).sub (h2.const_mul (3 / c ^ 2))).sub
      (h1.const_mul (6 / c ^ 3))).sub (h0.const_mul (6 / c ^ 4))
    simpa using this


/-- `exp(-s t) · exp(-t) = exp(-(1+s) t)`. -/
theorem exp_mul_exp (s : ℂ) (t : ℝ) :
    Complex.exp (-s * t) * Complex.exp (-(t : ℂ)) = Complex.exp (-(1 + s) * t) := by
  rw [← Complex.exp_add]; congr 1; ring

/-- **`ŵ(s) = (s − ½)/(1+s)⁴`** for `Re s > −1`. -/
theorem lap_w {s : ℂ} (hs : -1 < s.re) :
    ∫ t in Ioi (0:ℝ), Complex.exp (-s * t) * (w t : ℂ) = (s - 1 / 2) / (1 + s) ^ 4 := by
  have hc : 0 < (1 + s).re := by simp; linarith
  have hc0 : (1 + s) ≠ 0 := fun h => by simp [h] at hc
  have h1 : ∀ t ∈ Ioi (0:ℝ), Complex.exp (-s * t) * (w t : ℂ) =
      (1 / 2) * ((t : ℂ) ^ 2 * Complex.exp (-(1 + s) * t)) -
        (1 / 4) * ((t : ℂ) ^ 3 * Complex.exp (-(1 + s) * t)) := by
    intro t ht
    rw [w_of_nonneg (le_of_lt ht)]
    push_cast
    rw [← exp_mul_exp s t]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1,
    integral_sub ((integrableOn_pow_exp (1 + s) hc 2).const_mul _)
      ((integrableOn_pow_exp (1 + s) hc 3).const_mul _),
    integral_const_mul, integral_const_mul, laplace_pow2 _ hc, laplace_pow3 _ hc]
  field_simp
  ring

/-- **`ŵ′(s) = s (s − ½)/(1+s)⁴`** (so `ŵ′ = s ŵ`) for `Re s > −1`. -/
theorem lap_wd {s : ℂ} (hs : -1 < s.re) :
    ∫ t in Ioi (0:ℝ), Complex.exp (-s * t) * (wd t : ℂ) = s * (s - 1 / 2) / (1 + s) ^ 4 := by
  have hc : 0 < (1 + s).re := by simp; linarith
  have hc0 : (1 + s) ≠ 0 := fun h => by simp [h] at hc
  have h1 : ∀ t ∈ Ioi (0:ℝ), Complex.exp (-s * t) * (wd t : ℂ) =
      ((t : ℂ) ^ 1 * Complex.exp (-(1 + s) * t)) -
        (5 / 4) * ((t : ℂ) ^ 2 * Complex.exp (-(1 + s) * t)) +
        (1 / 4) * ((t : ℂ) ^ 3 * Complex.exp (-(1 + s) * t)) := by
    intro t ht
    rw [wd_of_nonneg (le_of_lt ht)]
    push_cast
    rw [← exp_mul_exp s t]
    ring
  have iA : IntegrableOn (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(1 + s) * t)) (Ioi 0) :=
    integrableOn_pow_exp (1 + s) hc 1
  have iB : IntegrableOn (fun t : ℝ => (5 / 4 : ℂ) * ((t : ℂ) ^ 2 * Complex.exp (-(1 + s) * t))) (Ioi 0) :=
    (integrableOn_pow_exp (1 + s) hc 2).const_mul _
  have iC : IntegrableOn (fun t : ℝ => (1 / 4 : ℂ) * ((t : ℂ) ^ 3 * Complex.exp (-(1 + s) * t))) (Ioi 0) :=
    (integrableOn_pow_exp (1 + s) hc 3).const_mul _
  have iAB : IntegrableOn (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(1 + s) * t) -
      (5 / 4 : ℂ) * ((t : ℂ) ^ 2 * Complex.exp (-(1 + s) * t))) (Ioi 0) := iA.sub iB
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_add iAB iC, integral_sub iA iB,
    integral_const_mul, integral_const_mul, laplace_pow1 _ hc, laplace_pow2 _ hc, laplace_pow3 _ hc]
  field_simp
  ring



/-- The Laplace transform of a real function on `(0, ∞)`. -/
noncomputable def lap (f : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, Complex.exp (-w * (t : ℂ)) * (f t : ℂ)

/-- **Signed Laplace holomorphy.** If `e^{-τt}|f|` is integrable on `(0, ∞)` for every `τ > σ₀`, the
Laplace transform of `f` is complex differentiable on `Re w > σ₀`. -/
theorem hasDerivAt_lap (f : ℝ → ℝ) (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (σ₀ : ℝ)
    (hint : ∀ τ : ℝ, σ₀ < τ → IntegrableOn (fun t : ℝ => Real.exp (-τ * t) * |f t|) (Ioi 0))
    {w₀ : ℂ} (hw₀ : σ₀ < w₀.re) :
    HasDerivAt (lap f) (-(∫ t : ℝ in Ioi 0, (t : ℂ) * (Complex.exp (-w₀ * (t : ℂ)) * (f t : ℂ)))) w₀ := by
  set δ : ℝ := (w₀.re - σ₀) / 2 with hδ
  have hδpos : 0 < δ := by simp only [hδ]; linarith
  set τ₂ : ℝ := w₀.re - δ with hτ₂
  have hτ₂σ : σ₀ < τ₂ := by simp only [hτ₂, hδ]; linarith
  obtain ⟨τ₁, hτ₁a, hτ₁b⟩ := exists_between hτ₂σ
  obtain ⟨C, hC0, hC⟩ := RhWaveLean.pow_mul_exp_neg_bound (n := 1) (c := τ₂ - τ₁) (by linarith)
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  set F : ℂ → ℝ → ℂ := fun w t => Complex.exp (-w * (t : ℂ)) * (f t : ℂ) with hF
  set F' : ℂ → ℝ → ℂ := fun w t => -((t : ℂ) * (Complex.exp (-w * (t : ℂ)) * (f t : ℂ))) with hF'
  set bound : ℝ → ℝ := fun t => C * (Real.exp (-τ₁ * t) * |f t|) with hbound
  set s : Set ℂ := Metric.ball w₀ δ with hs
  have hsn : s ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ hδpos
  have hfc : AEStronglyMeasurable (fun t : ℝ => (f t : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hf
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) μ :=
    Filter.Eventually.of_forall fun w =>
      (Complex.continuous_exp.comp (by fun_prop : Continuous fun t : ℝ => -w * (t : ℂ))).aestronglyMeasurable.mul hfc
  -- integrability at `w₀` from `|F w₀ t| = e^{-Re w₀ t}|f t| ≤ e^{-τ₂ t}|f t|`-type bound; use `τ = Re w₀`
  have hF_int : Integrable (F w₀) μ := by
    refine Integrable.mono' (hint w₀.re hw₀) (hF_meas.self_of_nhds) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    simp only [hF, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    refine le_of_eq ?_
    congr 2
    simp
  have hF'_meas : AEStronglyMeasurable (F' w₀) μ := by
    refine AEStronglyMeasurable.neg ?_
    exact Complex.continuous_ofReal.aestronglyMeasurable.mul
      ((Complex.continuous_exp.comp (by fun_prop : Continuous fun t : ℝ => -w₀ * (t : ℂ))).aestronglyMeasurable.mul hfc)
  have h_bound : ∀ᵐ t ∂μ, ∀ w ∈ s, ‖F' w t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hre : τ₂ ≤ w.re := by
      have h1 : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
        have h2 := Complex.abs_re_le_norm (w - w₀)
        rwa [show (w - w₀).re = w.re - w₀.re from by simp [Complex.sub_re]] at h2
      have h4 : -δ ≤ w.re - w₀.re := (abs_le.mp (le_trans h1 (le_of_lt hw))).1
      simp only [hτ₂]; linarith
    have hnorm : ‖F' w t‖ = t * Real.exp (-w.re * t) * |f t| := by
      simp only [hF', norm_neg, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
      have : (-w * (t : ℂ)).re = -w.re * t := by simp [Complex.mul_re]
      rw [this]; ring
    rw [hnorm]
    have hle : t ^ 1 * Real.exp (-(τ₂ - τ₁) * t) ≤ C := hC t ht0.le
    have hexp_le : Real.exp (-w.re * t) ≤ Real.exp (-τ₂ * t) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hexp_eq : Real.exp (-τ₂ * t) = Real.exp (-(τ₂ - τ₁) * t) * Real.exp (-τ₁ * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have hH : 0 ≤ |f t| := abs_nonneg _
    have hE1 : 0 ≤ Real.exp (-τ₁ * t) := (Real.exp_pos _).le
    have p1 : 0 ≤ (Real.exp (-τ₂ * t) - Real.exp (-w.re * t)) * (t * |f t|) :=
      mul_nonneg (sub_nonneg.2 hexp_le) (mul_nonneg ht0.le hH)
    have p2 : 0 ≤ (C - t ^ 1 * Real.exp (-(τ₂ - τ₁) * t)) * (Real.exp (-τ₁ * t) * |f t|) :=
      mul_nonneg (sub_nonneg.2 hle) (mul_nonneg hE1 hH)
    rw [hexp_eq] at p1
    simp only [hbound]
    nlinarith [p1, p2]
  have bound_int : Integrable bound μ := (hint τ₁ hτ₁a).const_mul C
  have h_diff : ∀ᵐ t ∂μ, ∀ w ∈ s, HasDerivAt (F · t) (F' w t) w := by
    refine Filter.Eventually.of_forall fun t w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (t : ℂ)) (-(t : ℂ)) w := by
      simpa using (hasDerivAt_id w).neg.mul_const (t : ℂ)
    have h2 := ((Complex.hasDerivAt_exp _).comp w h1).mul_const (f t : ℂ)
    refine h2.congr_deriv ?_
    simp only [hF']; ring
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) hsn hF_meas hF_int
    hF'_meas h_bound bound_int h_diff
  have e2 : (∫ a, F' w₀ a ∂μ) = -(∫ t : ℝ in Ioi 0, (t : ℂ) * (Complex.exp (-w₀ * (t : ℂ)) * (f t : ℂ))) := by
    simp only [hF']; rw [integral_neg]
  rw [e2] at hderiv
  exact hderiv


theorem weighted_abs_integrable_of_sq (f : ℝ → ℝ) (hf : Measurable f)
    (hsq : IntegrableOn (fun t => f t ^ 2) (Ioi (0:ℝ))) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun t : ℝ => Real.exp (-τ * t) * |f t|) (Ioi 0) := by
  have h := GppCausalTail.integrableOn_exp_mul_of_sq f hf.aemeasurable (τ : ℂ) (by simpa using hτ) 0
    (GppCausalTail.lintegral_enorm_sq_lt_top _ f hsq)
  have h2 : IntegrableOn (fun t : ℝ => ‖Complex.exp (-(τ : ℂ) * (t : ℂ)) * (f t : ℂ)‖) (Ioi 0) := h.norm
  refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 2
  simp

theorem weighted_abs_integrable_of_L1 (f : ℝ → ℝ) (hf : Measurable f)
    (h1 : IntegrableOn f (Ioi (0:ℝ))) {τ : ℝ} (hτ : 0 ≤ τ) :
    IntegrableOn (fun t : ℝ => Real.exp (-τ * t) * |f t|) (Ioi 0) := by
  refine Integrable.mono' h1.norm ?_ ?_
  · exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul (by simpa [Real.norm_eq_abs] using hf.norm : Measurable fun t => |f t|)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
    have : Real.exp (-τ * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc Real.exp (-τ * t) * |f t| ≤ 1 * |f t| := by gcongr
      _ = ‖f t‖ := by rw [one_mul, Real.norm_eq_abs]


open GppCausalKernels in
/-- The `n`-th term of the Dirichlet-series expansion of `exp(-st) (ν ∗ f)(t)`. -/
noncomputable def term (f : ℝ → ℝ) (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-s * (t : ℂ)) * ((f (t - Real.log n) / Real.sqrt n : ℝ) : ℂ)

open GppCausalKernels in
theorem term_eq_zero_of_gt (f : ℝ → ℝ) (hf0 : ∀ u, u ≤ 0 → f u = 0) (s : ℂ) {n : ℕ} {t : ℝ}
    (hn : ⌊Real.exp t⌋₊ < n) : term f s n t = 0 := by
  unfold term
  by_cases h0 : n = 0
  · simp [h0]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
    have : Real.exp t < n := (Nat.floor_lt (Real.exp_pos t).le).1 hn
    have hlog : t < Real.log n := (Real.lt_log_iff_exp_lt hnpos).2 this
    simp [hf0 (t - Real.log n) (by linarith)]

open GppCausalKernels in
theorem exp_mul_nuConv_eq_tsum (f : ℝ → ℝ) (hf0 : ∀ u, u ≤ 0 → f u = 0) (s : ℂ) (t : ℝ) :
    Complex.exp (-s * (t : ℂ)) * (nuConv f t : ℂ) = ∑' n : ℕ, term f s n t := by
  have h0 : ∀ n ∉ Finset.Icc 1 ⌊Real.exp t⌋₊, term f s n t = 0 := by
    intro n hn
    by_cases hz : n = 0
    · simp [term, hz]
    · refine term_eq_zero_of_gt f hf0 s ?_
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      exact hn (Nat.pos_of_ne_zero hz)
  rw [tsum_eq_sum h0, nuConv, Complex.ofReal_sum, Finset.mul_sum]
  rfl


/-- The Dirichlet coefficient `e^{-s log n}/√n`. -/
noncomputable def coef (s : ℂ) (n : ℕ) : ℂ := Complex.exp (-s * (Real.log n : ℂ)) / (Real.sqrt n : ℂ)

theorem term_eq (f : ℝ → ℝ) (s : ℂ) (n : ℕ) (t : ℝ) :
    term f s n t = coef s n * (Complex.exp (-s * ((t - Real.log n : ℝ) : ℂ)) * (f (t - Real.log n) : ℂ)) := by
  unfold term coef
  simp only [Complex.ofReal_div, Complex.ofReal_sub]
  have : Complex.exp (-s * (t : ℂ)) =
      Complex.exp (-s * (Real.log n : ℂ)) * Complex.exp (-s * ((t : ℂ) - (Real.log n : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; ring

/-- Causal weighted function is integrable on `ℝ`. -/
theorem integrable_causal_weighted (f : ℝ → ℝ) (hfm : Measurable f) (hf0 : ∀ u, u ≤ 0 → f u = 0)
    (s : ℂ) (hint : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u) * |f u|) (Ioi 0)) :
    Integrable (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) := by
  have hm : Measurable (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) :=
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)).mul
      (Complex.measurable_ofReal.comp hfm)
  have h1 : IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) (Ioi 0) := by
    refine Integrable.mono' hint (hm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun u => ?_
    simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    refine le_of_eq ?_
    congr 2
    simp [Complex.mul_re]
  rw [← integrableOn_iff_integrable_of_support_subset (s := Ioi (0:ℝ))]
  · exact h1
  · intro u hu
    by_contra h
    exact hu (by simp [hf0 u (not_lt.1 h)])

theorem integral_causal (f : ℝ → ℝ) (hf0 : ∀ u, u ≤ 0 → f u = 0) (s : ℂ) :
    ∫ u : ℝ, Complex.exp (-s * (u : ℂ)) * (f u : ℂ) = lap f s := by
  unfold lap
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro u hu
  simp [hf0 u (not_lt.1 hu)]

theorem integral_term (f : ℝ → ℝ) (hf0 : ∀ u, u ≤ 0 → f u = 0) (s : ℂ) (n : ℕ) :
    ∫ t : ℝ, term f s n t = coef s n * lap f s := by
  have e : (fun t => term f s n t) = fun t => coef s n *
      ((fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) (t - Real.log n)) := by
    funext t; rw [term_eq]
  rw [e, integral_const_mul, integral_sub_right_eq_self
    (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) (Real.log n), integral_causal f hf0]


theorem coef_eq {s : ℂ} (hs : 1 / 2 < s.re) (n : ℕ) :
    coef s n = 1 / (n : ℂ) ^ ((1 : ℂ) / 2 + s) := by
  have hne : (1 : ℂ) / 2 + s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  by_cases hn : n = 0
  · subst hn
    have h0 : (0 : ℂ) ^ ((1 : ℂ) / 2 + s) = 0 := Complex.zero_cpow hne
    rw [show ((0 : ℕ) : ℂ) = 0 from Nat.cast_zero, h0]
    simp [coef]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hsq : (Real.sqrt n : ℂ) = Complex.exp ((Real.log n : ℂ) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
      push_cast
      congr 1; ring
    unfold coef
    rw [Complex.cpow_def_of_ne_zero hn0, hsq, ← Complex.ofReal_natCast, ← Complex.ofReal_log hnpos.le]
    rw [div_eq_div_iff (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)]
    rw [one_mul, ← Complex.exp_add]
    congr 1; ring

theorem summable_norm_coef {s : ℂ} (hs : 1 / 2 < s.re) : Summable fun n => ‖coef s n‖ := by
  have h : 1 < ((1 : ℂ) / 2 + s).re := by simp; linarith
  have := Complex.summable_one_div_nat_cpow.2 h
  have h2 : Summable fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + s)‖ := summable_norm_iff.2 this
  have e : (fun n : ℕ => ‖coef s n‖) = fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + s)‖ := by
    funext n; rw [coef_eq hs]
  rw [e]; exact h2

theorem hasSum_coef {s : ℂ} (hs : 1 / 2 < s.re) : HasSum (coef s) (riemannZeta (1 / 2 + s)) := by
  have h : 1 < ((1 : ℂ) / 2 + s).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow h]
  have : coef s = fun n : ℕ => 1 / (n : ℂ) ^ ((1 : ℂ) / 2 + s) := funext (coef_eq hs)
  rw [this]
  exact (Complex.summable_one_div_nat_cpow.2 h).hasSum


open GppCausalKernels in
/-- **Dirichlet-series interchange.** For `Re s > 1/2` and causal `f` with `e^{-σu}|f|` integrable
(`σ = Re s`): `∫₀^∞ e^{-st} (ν ∗ f)(t) dt = ζ(1/2 + s) ∫₀^∞ e^{-su} f(u) du`. -/
theorem lap_nuConv (f : ℝ → ℝ) (hfm : Measurable f) (hf0 : ∀ u, u ≤ 0 → f u = 0) {s : ℂ}
    (hs : 1 / 2 < s.re) (hint : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u) * |f u|) (Ioi 0)) :
    lap (nuConv f) s = riemannZeta (1 / 2 + s) * lap f s := by
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  have hG := integrable_causal_weighted f hfm hf0 s hint
  -- each term vanishes for `t ≤ 0`
  have hterm0 : ∀ n : ℕ, ∀ t : ℝ, t ≤ 0 → term f s n t = 0 := by
    intro n t ht
    unfold term
    have : f (t - Real.log n) = 0 := by
      refine hf0 _ ?_
      have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      linarith
    simp [this]
  have hF_int : ∀ n : ℕ, Integrable (term f s n) μ := by
    intro n
    have e : term f s n = fun t => coef s n *
        ((fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) (t - Real.log n)) := by
      funext t; rw [term_eq]
    rw [e]
    exact ((hG.comp_sub_right (Real.log n)).const_mul (coef s n)).restrict
  have hint_eq : ∀ n : ℕ, ∫ t, term f s n t ∂μ = coef s n * lap f s := by
    intro n
    rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ))
      (fun t (ht : t ∉ Ioi (0:ℝ)) => hterm0 n t (not_lt.1 ht))]
    exact integral_term f hf0 s n
  have hnorm_eq : ∀ n : ℕ, ∫ t, ‖term f s n t‖ ∂μ = ‖coef s n‖ * ∫ u : ℝ, ‖Complex.exp (-s * (u : ℂ)) * (f u : ℂ)‖ := by
    intro n
    rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ))
      (fun t (ht : t ∉ Ioi (0:ℝ)) => by simp [hterm0 n t (not_lt.1 ht)])]
    have e : (fun t => ‖term f s n t‖) = fun t => ‖coef s n‖ *
        ((fun u : ℝ => ‖Complex.exp (-s * (u : ℂ)) * (f u : ℂ)‖) (t - Real.log n)) := by
      funext t; rw [term_eq, norm_mul]
    rw [e, integral_const_mul, integral_sub_right_eq_self
      (fun u : ℝ => ‖Complex.exp (-s * (u : ℂ)) * (f u : ℂ)‖) (Real.log n)]
  have hF_sum : Summable fun n : ℕ => ∫ t, ‖term f s n t‖ ∂μ := by
    simp_rw [hnorm_eq]
    exact (summable_norm_coef hs).mul_right _
  have hsum := hasSum_integral_of_summable_integral_norm hF_int hF_sum
  simp_rw [hint_eq] at hsum
  have hsum2 : HasSum (fun n : ℕ => coef s n * lap f s) (riemannZeta (1 / 2 + s) * lap f s) :=
    (hasSum_coef hs).mul_right _
  have := hsum.unique hsum2
  unfold lap
  have e2 : (∫ t : ℝ in Ioi 0, Complex.exp (-s * (t : ℂ)) * (nuConv f t : ℂ)) =
      ∫ t, ∑' n : ℕ, term f s n t ∂μ := by
    rw [hμ]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact exp_mul_nuConv_eq_tsum f hf0 s t
  rw [e2]
  exact this


open GppHeartReduction in
/-- `Ê(s) = 2 ξ_E(s) / (s Γℝ(s))`: equals `(s − 1) ζ(s)` for `s ≠ 0, 1`, and is holomorphic off `s = 0`. -/
noncomputable def zetaRes (s : ℂ) : ℂ := 2 * xiE s * (Complex.Gammaℝ s)⁻¹ / s

open GppHeartReduction in
theorem zetaRes_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : zetaRes s = (s - 1) * riemannZeta s := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hΛ := xiE_eq h0 h1
  rw [riemannZeta_def_of_ne_zero h0]
  unfold zetaRes
  rw [hΛ]
  by_cases hG : Complex.Gammaℝ s = 0
  · simp [hG]
  · field_simp

open GppHeartReduction in
theorem differentiableAt_zetaRes {s : ℂ} (h0 : s ≠ 0) : DifferentiableAt ℂ zetaRes s := by
  unfold zetaRes
  exact (((differentiable_xiE s).const_mul 2).mul (Complex.differentiable_Gammaℝ_inv s)).div
    differentiableAt_id h0


open GppCausalKernels GppCausalNorms in
theorem w_causal : ∀ u : ℝ, u ≤ 0 → w u = 0 := fun u hu => by
  rcases lt_or_eq_of_le hu with h | h
  · exact w_of_neg h
  · rw [h]; exact w_zero

open GppCausalKernels GppCausalNorms in
theorem wd_causal : ∀ u : ℝ, u ≤ 0 → wd u = 0 := fun _ hu => wd_of_nonpos hu

open GppCausalKernels GppCausalNorms in
theorem integrableOn_w : IntegrableOn w (Ioi (0:ℝ)) := by
  have h3 := integrableOn_g (by norm_num : 1 ≤ 3)
  have h4 := integrableOn_g (by norm_num : 1 ≤ 4)
  exact h3.sub (h4.const_mul (3 / 2))

open GppCausalKernels GppCausalNorms in
theorem integrableOn_wd : IntegrableOn wd (Ioi (0:ℝ)) := by
  have h2 := integrableOn_g (by norm_num : 1 ≤ 2)
  have h3 := integrableOn_g (by norm_num : 1 ≤ 3)
  have h4 := integrableOn_g (by norm_num : 1 ≤ 4)
  have := (h2.sub (h3.const_mul (5 / 2))).add (h4.const_mul (3 / 2))
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [wd]

/-- The right-hand sides on `Re s > 0`. -/
noncomputable def Gz (s : ℂ) : ℂ := zetaRes (1 / 2 + s) / (1 + s) ^ 4
noncomputable def Gk (s : ℂ) : ℂ := s * zetaRes (1 / 2 + s) / (1 + s) ^ 4

theorem differentiableOn_Gz : DifferentiableOn ℂ Gz {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : 0 < s.re := hs
  have h1 : (1 / 2 + s) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (1 + s) ^ 4 ≠ 0 := by
    apply pow_ne_zero; intro h; have := congrArg Complex.re h; simp at this; linarith
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Gz
  exact ((differentiableAt_zetaRes h1).comp s (differentiableAt_const _ |>.add differentiableAt_id)).div
    ((differentiableAt_const _ |>.add differentiableAt_id).pow 4) h2

theorem differentiableOn_Gk : DifferentiableOn ℂ Gk {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : 0 < s.re := hs
  have h1 : (1 / 2 + s) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (1 + s) ^ 4 ≠ 0 := by
    apply pow_ne_zero; intro h; have := congrArg Complex.re h; simp at this; linarith
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Gk
  exact ((differentiableAt_id).mul
    ((differentiableAt_zetaRes h1).comp s (differentiableAt_const _ |>.add differentiableAt_id))).div
    ((differentiableAt_const _ |>.add differentiableAt_id).pow 4) h2


open GppCausalKernels GppCausalNorms in
theorem differentiableOn_lap_Z : DifferentiableOn ℂ (lap Z) {s : ℂ | 0 < s.re} := fun _ hs =>
  (hasDerivAt_lap Z measurable_Z.aestronglyMeasurable 0
    (fun _ hτ => weighted_abs_integrable_of_sq Z measurable_Z Z_sq_bound.1 hτ) hs).differentiableAt.differentiableWithinAt

open GppCausalKernels GppCausalNorms in
theorem differentiableOn_lap_kk : DifferentiableOn ℂ (lap kk) {s : ℂ | 0 < s.re} := fun _ hs =>
  (hasDerivAt_lap kk measurable_kk.aestronglyMeasurable 0
    (fun _ hτ => weighted_abs_integrable_of_L1 kk measurable_kk kk_L1_bound.1 hτ.le) hs).differentiableAt.differentiableWithinAt

open GppCausalKernels GppCausalNorms in
/-- On `Re s > 1/2`, the Dirichlet-series interchange gives `lap Z = G_z`. -/
theorem lap_Z_eq_right {s : ℂ} (hs : 1 / 2 < s.re) : lap Z s = Gz s := by
  have hint := weighted_abs_integrable_of_L1 w measurable_w integrableOn_w (τ := s.re) (by linarith)
  have h1 : lap Z s = riemannZeta (1 / 2 + s) * lap w s := lap_nuConv w measurable_w w_causal hs hint
  rw [h1, show lap w s = (s - 1 / 2) / (1 + s) ^ 4 from lap_w (by linarith)]
  have h0 : (1 / 2 + s) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1' : (1 / 2 + s) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold Gz
  rw [zetaRes_eq h0 h1']
  have : (1 / 2 + s - 1) = s - 1 / 2 := by ring
  rw [this]; ring

open GppCausalKernels GppCausalNorms in
theorem lap_kk_eq_right {s : ℂ} (hs : 1 / 2 < s.re) : lap kk s = Gk s := by
  have hint := weighted_abs_integrable_of_L1 wd measurable_wd integrableOn_wd (τ := s.re) (by linarith)
  have h1 : lap kk s = riemannZeta (1 / 2 + s) * lap wd s := lap_nuConv wd measurable_wd wd_causal hs hint
  rw [h1, show lap wd s = s * (s - 1 / 2) / (1 + s) ^ 4 from lap_wd (by linarith)]
  have h0 : (1 / 2 + s) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1' : (1 / 2 + s) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold Gk
  rw [zetaRes_eq h0 h1']
  have : (1 / 2 + s - 1) = s - 1 / 2 := by ring
  rw [this]; ring


/-- The open right half-plane. -/
theorem isOpen_re_pos : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_re_pos : IsPreconnected {s : ℂ | 0 < s.re} :=
  (convex_halfSpace_re_gt 0).isPreconnected

theorem eventually_re_gt_half : ∀ᶠ s : ℂ in 𝓝 1, 1 / 2 < s.re :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; norm_num)

open GppCausalKernels GppCausalNorms in
/-- **The identity-theorem step.** `lap Z = G_z` on the whole half-plane `Re s > 0`:
both sides are holomorphic on `Re s > 0` (the left by `Z ∈ L²`, the right because `Ê` is holomorphic
off `0`), the half-plane is open and preconnected, and they agree on the open set `Re s > 1/2`. -/
theorem lap_Z_eq {s : ℂ} (hs : 0 < s.re) : lap Z s = Gz s := by
  have han1 := differentiableOn_lap_Z.analyticOnNhd isOpen_re_pos
  have han2 := differentiableOn_Gz.analyticOnNhd isOpen_re_pos
  have h1 : (1 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : lap Z =ᶠ[𝓝 1] Gz := by
    filter_upwards [eventually_re_gt_half] with s hs using lap_Z_eq_right hs
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2 isPreconnected_re_pos h1 hev hs

open GppCausalKernels GppCausalNorms in
theorem lap_kk_eq {s : ℂ} (hs : 0 < s.re) : lap kk s = Gk s := by
  have han1 := differentiableOn_lap_kk.analyticOnNhd isOpen_re_pos
  have han2 := differentiableOn_Gk.analyticOnNhd isOpen_re_pos
  have h1 : (1 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : lap kk =ᶠ[𝓝 1] Gk := by
    filter_upwards [eventually_re_gt_half] with s hs using lap_kk_eq_right hs
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2 isPreconnected_re_pos h1 hev hs

theorem zetaRes_eq_zero_of_zero {r : ℂ} (hr : 0 < r.re) (hr' : r ≠ 1 / 2)
    (hz : riemannZeta (1 / 2 + r) = 0) : zetaRes (1 / 2 + r) = 0 := by
  have h0 : (1 / 2 + r) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : (1 / 2 + r) ≠ 1 := by
    intro h; apply hr'; linear_combination h
  rw [zetaRes_eq h0 h1, hz, mul_zero]

open GppCausalKernels GppCausalNorms in
/-- At a zero `r` of `ζ(1/2 + ·)` with `Re r > 0`, `r ≠ 1/2`: the transform of `k` vanishes. -/
theorem lap_kk_at_zero {r : ℂ} (hr : 0 < r.re) (hr' : r ≠ 1 / 2)
    (hz : riemannZeta (1 / 2 + r) = 0) : lap kk r = 0 := by
  rw [lap_kk_eq hr]
  unfold Gk
  rw [zetaRes_eq_zero_of_zero hr hr' hz]; simp

open GppCausalKernels GppCausalNorms in
theorem lap_Z_at_zero {r : ℂ} (hr : 0 < r.re) (hr' : r ≠ 1 / 2)
    (hz : riemannZeta (1 / 2 + r) = 0) : lap Z r = 0 := by
  rw [lap_Z_eq hr]
  unfold Gz
  rw [zetaRes_eq_zero_of_zero hr hr' hz]; simp


open GppCausalKernels GppCausalNorms in
/-- At a zero `r` (`Re r > 0`, `r ≠ 1/2`), `ĥ(r) = (r − 1/2)/(1 + r)⁴` for `h = w − cZ`. -/
theorem lap_hh_at_zero (c : ℝ) {r : ℂ} (hr : 0 < r.re) (hr' : r ≠ 1 / 2)
    (hz : riemannZeta (1 / 2 + r) = 0) : lap (hh c) r = (r - 1 / 2) / (1 + r) ^ 4 := by
  have iw : IntegrableOn (fun t : ℝ => Complex.exp (-r * (t : ℂ)) * (w t : ℂ)) (Ioi 0) :=
    GppCausalTail.integrableOn_exp_mul_of_sq w measurable_w.aemeasurable r hr 0
      (GppCausalTail.lintegral_enorm_sq_lt_top _ w w_sq_bound.1)
  have iZ : IntegrableOn (fun t : ℝ => Complex.exp (-r * (t : ℂ)) * (Z t : ℂ)) (Ioi 0) :=
    GppCausalTail.integrableOn_exp_mul_of_sq Z measurable_Z.aemeasurable r hr 0
      (GppCausalTail.lintegral_enorm_sq_lt_top _ Z Z_sq_bound.1)
  have e : ∀ t : ℝ, Complex.exp (-r * (t : ℂ)) * (hh c t : ℂ) =
      Complex.exp (-r * (t : ℂ)) * (w t : ℂ) - (c : ℂ) * (Complex.exp (-r * (t : ℂ)) * (Z t : ℂ)) := by
    intro t; simp only [hh]; push_cast; ring
  unfold lap
  simp_rw [e]
  rw [integral_sub iw (iZ.const_mul _), integral_const_mul]
  have hw : ∫ t : ℝ in Ioi 0, Complex.exp (-r * (t : ℂ)) * (w t : ℂ) = (r - 1 / 2) / (1 + r) ^ 4 :=
    lap_w (by linarith)
  have hZ : ∫ t : ℝ in Ioi 0, Complex.exp (-r * (t : ℂ)) * (Z t : ℂ) = 0 := lap_Z_at_zero hr hr' hz
  rw [hw, hZ]; ring



end GppCausalTransforms
