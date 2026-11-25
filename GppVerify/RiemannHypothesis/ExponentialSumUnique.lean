/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude Code)
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Uniqueness of the coefficients of an absolutely summable exponential sum

If `Σ_i c_i e^{i γ_i t} = 0` for every real `t`, with `Σ ‖c_i‖ < ∞` and the frequencies `γ_i`
pairwise distinct, then every `c_i = 0` (`eq_zero_of_exponential_sum_eq_zero`). The proof averages
over `[-T, T]` against `e^{-iγ_{i₀} t}` and lets `T → ∞`: the `i₀` term survives and every other
term is a Dirichlet-type kernel `sin(ΔT)/(ΔT) → 0`, dominated by `‖c_i‖`.
-/

open Filter Topology MeasureTheory intervalIntegral Complex
open scoped Real

noncomputable section

namespace GppExpSum

/-- The average of `e^{iΔt}` over `[-T, T]`. -/
def avg (T Δ : ℝ) : ℂ := ((1 / (2 * T) : ℝ) : ℂ) * ∫ t in (-T)..T, Complex.exp ((Δ : ℂ) * t * Complex.I)

theorem norm_avg_le_one {T : ℝ} (hT : 0 < T) (Δ : ℝ) : ‖avg T Δ‖ ≤ 1 := by
  unfold avg
  have h1 : ‖∫ t in (-T)..T, Complex.exp ((Δ : ℂ) * t * Complex.I)‖ ≤ 1 * |T - -T| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => ?_)
    have : (Δ : ℂ) * t * Complex.I = ((Δ * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : |T - -T| = 2 * T := by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
  rw [this] at h1
  calc 1 / (2 * T) * ‖∫ t in (-T)..T, Complex.exp ((Δ : ℂ) * t * Complex.I)‖
      ≤ 1 / (2 * T) * (1 * (2 * T)) := by gcongr
    _ = 1 := by field_simp

theorem avg_zero {T : ℝ} (hT : 0 < T) : avg T 0 = 1 := by
  unfold avg
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp
  ring

theorem tendsto_avg {Δ : ℝ} (hΔ : Δ ≠ 0) : Tendsto (fun T => avg T Δ) atTop (𝓝 0) := by
  have hI : ∀ T : ℝ, ∫ t in (-T)..T, Complex.exp ((Δ : ℂ) * t * Complex.I) =
      (Complex.exp ((Δ : ℂ) * T * Complex.I) - Complex.exp ((Δ : ℂ) * (-T : ℝ) * Complex.I)) /
        ((Δ : ℂ) * Complex.I) := by
    intro T
    have hc : (Δ : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hΔ) Complex.I_ne_zero
    have := integral_exp_mul_complex (a := -T) (b := T) hc
    simp only [mul_comm ((Δ : ℂ) * Complex.I)] at this
    convert this using 3 <;> first | ring_nf | simp
  have hb : ∀ T : ℝ, 0 < T → ‖avg T Δ‖ ≤ 1 / (|Δ| * T) := by
    intro T hT
    unfold avg
    rw [hI T, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_div,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    have hn : ‖Complex.exp ((Δ : ℂ) * T * Complex.I) -
        Complex.exp ((Δ : ℂ) * (-T : ℝ) * Complex.I)‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have e1 : (Δ : ℂ) * T * Complex.I = ((Δ * T : ℝ) : ℂ) * Complex.I := by push_cast; ring
      have e2 : (Δ : ℂ) * (-T : ℝ) * Complex.I = ((Δ * -T : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [e1, e2, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num
    have hΔ' : 0 < |Δ| := abs_pos.2 hΔ
    calc 1 / (2 * T) * (‖Complex.exp ((Δ : ℂ) * T * Complex.I) -
          Complex.exp ((Δ : ℂ) * (-T : ℝ) * Complex.I)‖ / |Δ|)
        ≤ 1 / (2 * T) * (2 / |Δ|) := by gcongr
      _ = 1 / (|Δ| * T) := by field_simp
  have hlim : Tendsto (fun T : ℝ => 1 / (|Δ| * T)) atTop (𝓝 0) := by
    have : Tendsto (fun T : ℝ => (|Δ| * T)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop (abs_pos.2 hΔ))
    simpa [one_div] using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with T hT using hb T hT


/-- The core statement, for a countable index type. -/
theorem eq_zero_of_exponential_sum_eq_zero_countable {ι : Type*} [Countable ι] (γ : ι → ℝ)
    (hγ : Function.Injective γ) (c : ι → ℂ) (hc : Summable fun i => ‖c i‖)
    (h : ∀ t : ℝ, ∑' i, c i * Complex.exp ((γ i : ℂ) * t * Complex.I) = 0) (i0 : ι) :
    c i0 = 0 := by
  classical
  have hn : ∀ (i : ι) (Δ t : ℝ), ‖c i * Complex.exp ((Δ : ℂ) * t * Complex.I)‖ = ‖c i‖ := by
    intro i Δ t
    have : (Δ : ℂ) * t * Complex.I = ((Δ * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h1 : ∀ t : ℝ, ∑' i, c i * Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I) = 0 := by
    intro t
    have h2 := congrArg (fun z => z * Complex.exp (-(γ i0 : ℂ) * t * Complex.I)) (h t)
    simp only [zero_mul] at h2
    rw [← tsum_mul_right] at h2
    rw [← h2]
    refine tsum_congr fun i => ?_
    have e : Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I) =
        Complex.exp ((γ i : ℂ) * t * Complex.I) * Complex.exp (-(γ i0 : ℂ) * t * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  have hzero : ∀ T : ℝ, 0 < T → ∑' i, c i * avg T (γ i - γ i0) = 0 := by
    intro T hT
    have hF : ∀ i, Continuous fun t : ℝ => c i * Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I) :=
      fun i => by fun_prop
    have hsum : HasSum (fun i => ∫ t in (-T)..T,
        c i * Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I))
        (∫ t in (-T)..T, (0 : ℂ)) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun i _ => ‖c i‖)
        (fun i => (hF i).aestronglyMeasurable)
        (fun i => Eventually.of_forall fun t _ => (hn i _ t).le)
        (Eventually.of_forall fun _ _ => hc)
        (by simpa using intervalIntegrable_const) ?_
      refine Eventually.of_forall fun t _ => ?_
      have hs : Summable fun i => c i * Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I) :=
        Summable.of_norm_bounded hc (fun i => (hn i _ t).le)
      have := hs.hasSum
      rwa [h1 t] at this
    have h3 : ∑' i, ∫ t in (-T)..T, c i * Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I) = 0 := by
      rw [hsum.tsum_eq]; simp
    have h4 : ∀ i, (∫ t in (-T)..T, c i * Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I)) =
        ((2 * T : ℝ) : ℂ) * (c i * avg T (γ i - γ i0)) := by
      intro i
      rw [intervalIntegral.integral_const_mul]
      unfold avg
      have hT' : ((2 * T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * T : ℝ) ≠ 0)
      have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      have : ((2 * T : ℝ) : ℂ) * ((1 / (2 * T) : ℝ) : ℂ) = 1 := by
        push_cast; field_simp
      calc c i * ∫ t in (-T)..T, Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I)
          = c i * (((2 * T : ℝ) : ℂ) * ((1 / (2 * T) : ℝ) : ℂ)) *
              ∫ t in (-T)..T, Complex.exp (((γ i - γ i0 : ℝ) : ℂ) * t * Complex.I) := by
            rw [this]; ring
        _ = _ := by ring
    simp_rw [h4] at h3
    rw [tsum_mul_left] at h3
    exact (mul_eq_zero.1 h3).resolve_left (by exact_mod_cast (by positivity : (2 * T : ℝ) ≠ 0))
  have hlim : Tendsto (fun T : ℝ => ∑' i, c i * avg T (γ i - γ i0)) atTop
      (𝓝 (∑' i, if i = i0 then c i0 else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun i => ‖c i‖) hc ?_ ?_
    · intro i
      by_cases hi : i = i0
      · subst hi
        have : Tendsto (fun T : ℝ => c i * avg T (γ i - γ i)) atTop (𝓝 (c i * 1)) := by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_gt_atTop 0] with T hT
          simp [avg_zero hT]
        simpa using this
      · have hne : γ i - γ i0 ≠ 0 := sub_ne_zero.2 fun e => hi (hγ e)
        have := (tendsto_avg hne).const_mul (c i)
        simpa [hi] using this
    · filter_upwards [eventually_gt_atTop 0] with T hT i
      rw [norm_mul]
      calc ‖c i‖ * ‖avg T (γ i - γ i0)‖ ≤ ‖c i‖ * 1 := by
            gcongr; exact norm_avg_le_one hT _
        _ = ‖c i‖ := mul_one _
  have hconst : Tendsto (fun T : ℝ => ∑' i, c i * avg T (γ i - γ i0)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with T hT using (hzero T hT).symm)
  have := tendsto_nhds_unique hlim hconst
  rwa [tsum_ite_eq] at this

/-- **Uniqueness of the coefficients of an absolutely summable exponential sum with distinct
frequencies.** -/
theorem eq_zero_of_exponential_sum_eq_zero {ι : Type*} (γ : ι → ℝ) (hγ : Function.Injective γ)
    (c : ι → ℂ) (hc : Summable fun i => ‖c i‖)
    (h : ∀ t : ℝ, ∑' i, c i * Complex.exp ((γ i : ℂ) * t * Complex.I) = 0) (i0 : ι) :
    c i0 = 0 := by
  by_contra hne
  have hs : i0 ∈ Function.support c := hne
  have hcs : (Function.support c).Countable := by
    have h0 := hc.countable_support
    have e : Function.support (fun i => ‖c i‖) = Function.support c := by ext i; simp
    rwa [e] at h0
  haveI : Countable (Function.support c) := hcs.to_subtype
  have key := eq_zero_of_exponential_sum_eq_zero_countable (fun i : Function.support c => γ i)
    (fun a b hab => Subtype.ext (hγ hab)) (fun i => c i) (hc.subtype _) (fun t => ?_) ⟨i0, hs⟩
  · exact hne key
  · rw [tsum_subtype_eq_of_support_subset (f := fun i => c i * Complex.exp ((γ i : ℂ) * t * Complex.I))]
    · exact h t
    · intro i hi
      exact fun h0 => hi (by simp [h0])

end GppExpSum

#print axioms GppExpSum.eq_zero_of_exponential_sum_eq_zero
