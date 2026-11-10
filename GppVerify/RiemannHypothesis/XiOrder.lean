/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GppVerify.Upstream.OrderOfGrowth
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree


/-!
# Explicit formula, stage E3a: the entire function `ξ` has finite order

`GppLogDerivZeroFree.xi s = (1 + s (s − 1) Λ₀(s)) / 2`, with `Λ₀` Mathlib's entire completed
zeta function. Mathlib has no growth bound for `Λ₀`, so this file proves one from the theta
kernel:

* `exists_kernel_bound`: `|evenKernel 0 t − 1|` and `|cosKernel 0 t − 1|` are `≤ C e^{−p t}` on
  `[1, ∞)` (continuity on the compact part, the `O(e^{−pt})` from Mathlib beyond it).
* `norm_f_modif_le`: pointwise bound of the modified kernel of `hurwitzEvenFEPair 0` on `(0, ∞)`.
* `norm_Lambda0_le`: `‖Λ₀(s)‖ ≤ K (2 (|Re s| + 2)/q)^{|Re s| + 2}`, uniform in `Im s`
  (the Mellin integral against `t^{σ − 1}`, with `u^R ≤ (2R/p)^R e^{pu/2}`).
* `xi_hasOrderLE_two`: `ξ` has order at most 2 (`Complex.HasOrderLE`). The true order is 1;
  the weaker exponent is all the zero counting needs.

With the Hadamard cluster (`HasOrderLE.sum_divisor_le`) this gives polynomial zero counting for `ξ`
(stage E3b). No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

open Real Set Filter MeasureTheory HurwitzZeta

namespace GppXiOrder

/-- `u ^ R ≤ (2R/p)^R · e^{p u / 2}` for `u > 0`, `R > 0`, `p > 0`. -/
theorem rpow_le_const_mul_exp {u R p : ℝ} (hu : 0 < u) (hR : 0 < R) (hp : 0 < p) :
    u ^ R ≤ (2 * R / p) ^ R * Real.exp (p * u / 2) := by
  have hc : 0 < 2 * R / p := by positivity
  rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hc, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : Real.log (p * u / (2 * R)) ≤ p * u / (2 * R) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log u = Real.log (p * u / (2 * R)) + Real.log (2 * R / p) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  rw [h2]
  have h3 : R * (p * u / (2 * R)) = p * u / 2 := by field_simp
  nlinarith

/-- A function continuous on `[1, ∞)` and `O(e^{-p t})` at infinity is bounded by `C e^{-p t}`
on all of `[1, ∞)`. -/
theorem exists_bound_of_isBigO {h : ℝ → ℝ} {p : ℝ} (hc : ContinuousOn h (Ici 1))
    (hO : h =O[atTop] fun t => Real.exp (-p * t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |h t| ≤ C * Real.exp (-p * t) := by
  obtain ⟨c, hcO⟩ := hO.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hcO
  set T' := max T 1 with hT'
  have hcomp : IsCompact (Icc 1 T') := isCompact_Icc
  have hcont : ContinuousOn (fun t => |h t| * Real.exp (p * t)) (Icc 1 T') := by
    refine ContinuousOn.mul ?_ (by fun_prop)
    exact (hc.mono Icc_subset_Ici_self).abs
  obtain ⟨B, hB⟩ := hcomp.bddAbove_image hcont
  refine ⟨max |c| (max B 0), by positivity, fun t ht => ?_⟩
  have hexp : 0 < Real.exp (-p * t) := Real.exp_pos _
  by_cases htT : t ≤ T'
  · have h1 : |h t| * Real.exp (p * t) ≤ B := hB ⟨t, ⟨ht, htT⟩, rfl⟩
    have h2 : |h t| = |h t| * Real.exp (p * t) * Real.exp (-p * t) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right (h1.trans ((le_max_left _ _).trans (le_max_right _ _))) hexp.le
  · have htT' : T ≤ t := (le_max_left T 1).trans (not_le.1 htT).le
    have h1 := hT t htT'
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hexp] at h1
    calc |h t| ≤ c * Real.exp (-p * t) := h1
      _ ≤ |c| * Real.exp (-p * t) := mul_le_mul_of_nonneg_right (le_abs_self c) hexp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hexp.le

/-- Exponential decay of `evenKernel 0 - 1` and `cosKernel 0 - 1` on `[1, ∞)`, with one pair of
constants. -/
theorem exists_kernel_bound :
    ∃ C p : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |evenKernel 0 t - 1| ≤ C * Real.exp (-p * t) ∧ |cosKernel 0 t - 1| ≤ C * Real.exp (-p * t) := by
  obtain ⟨p1, hp1, h1⟩ := isBigO_atTop_evenKernel_sub 0
  obtain ⟨p2, hp2, h2⟩ := isBigO_atTop_cosKernel_sub 0
  simp only [if_true] at h1
  have hsub : Ici (1 : ℝ) ⊆ Ioi 0 := fun t ht => mem_Ioi.2 (lt_of_lt_of_le one_pos (mem_Ici.1 ht))
  have hc1 : ContinuousOn (fun t => evenKernel 0 t - 1) (Ici 1) :=
    ((continuousOn_evenKernel 0).mono hsub).sub continuousOn_const
  have hc2 : ContinuousOn (fun t => cosKernel 0 t - 1) (Ici 1) :=
    ((continuousOn_cosKernel 0).mono hsub).sub continuousOn_const
  obtain ⟨C1, hC1, hb1⟩ := exists_bound_of_isBigO hc1 h1
  obtain ⟨C2, hC2, hb2⟩ := exists_bound_of_isBigO hc2 h2
  refine ⟨max C1 C2, min p1 p2, lt_min hp1 hp2, le_max_of_le_left hC1, fun t ht => ⟨?_, ?_⟩⟩
  · refine (hb1 t ht).trans (mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (le_max_of_le_left hC1))
    have : min p1 p2 ≤ p1 := min_le_left _ _
    nlinarith
  · refine (hb2 t ht).trans (mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (le_max_of_le_left hC1))
    have : min p1 p2 ≤ p2 := min_le_right _ _
    nlinarith

open Complex in
/-- Pointwise bound on the modified kernel of the even Hurwitz pair at `a = 0`. -/
theorem norm_f_modif_le {C p : ℝ}
    (hb : ∀ t : ℝ, 1 ≤ t →
      |evenKernel 0 t - 1| ≤ C * Real.exp (-p * t) ∧ |cosKernel 0 t - 1| ≤ C * Real.exp (-p * t))
    {t : ℝ} (ht : 0 < t) :
    ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      if 1 < t then C * Real.exp (-p * t)
      else C * t ^ (-(1 / 2 : ℝ)) * Real.exp (-p / t) := by
  unfold WeakFEPair.f_modif
  rcases lt_trichotomy t 1 with h | h | h
  · rw [if_neg (not_lt.2 h.le)]
    have h1 : t ∉ Ioi (1 : ℝ) := fun h' => absurd (mem_Ioi.1 h') (not_lt.2 h.le)
    have h2 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, h⟩
    simp only [Pi.add_apply, indicator_of_notMem h1, indicator_of_mem h2, zero_add]
    have hfe := evenKernel_functional_equation 0 t
    have hval : (hurwitzEvenFEPair 0).f t - ((hurwitzEvenFEPair 0).ε * ↑(t ^ (-(hurwitzEvenFEPair 0).k))) •
        (hurwitzEvenFEPair 0).g₀ = ((t ^ (-(1 / 2 : ℝ)) * (cosKernel 0 (1 / t) - 1) : ℝ) : ℂ) := by
      simp only [hurwitzEvenFEPair, Function.comp_apply, one_mul, smul_eq_mul, mul_one]
      rw [hfe]
      push_cast
      rw [Real.rpow_neg ht.le]
      push_cast
      ring
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    have hinv : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    have := (hb (1 / t) hinv).2
    have e : -p * (1 / t) = -p / t := by ring
    rw [e] at this
    calc t ^ (-(1 / 2 : ℝ)) * |cosKernel 0 (1 / t) - 1|
        ≤ t ^ (-(1 / 2 : ℝ)) * (C * Real.exp (-p / t)) :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ht.le _)
      _ = C * t ^ (-(1 / 2 : ℝ)) * Real.exp (-p / t) := by ring
  · subst h
    have h0 : 0 ≤ C * Real.exp (-p) :=
      le_trans (abs_nonneg _) (by simpa using (hb 1 le_rfl).1)
    have h1 : (1 : ℝ) ∉ Ioi (1 : ℝ) := by simp
    have h2 : (1 : ℝ) ∉ Ioo (0 : ℝ) 1 := by simp
    simp only [Pi.add_apply, indicator_of_notMem h1, indicator_of_notMem h2, add_zero, norm_zero,
      lt_irrefl, if_false, Real.one_rpow, mul_one, div_one]
    exact h0
  · rw [if_pos h]
    have h1 : t ∈ Ioi (1 : ℝ) := h
    have h2 : t ∉ Ioo (0 : ℝ) 1 := fun h' => absurd h'.2 (not_lt.2 h.le)
    simp only [Pi.add_apply, indicator_of_mem h1, indicator_of_notMem h2, add_zero]
    have hval : (hurwitzEvenFEPair 0).f t - (hurwitzEvenFEPair 0).f₀ =
        ((evenKernel 0 t - 1 : ℝ) : ℂ) := by
      simp [hurwitzEvenFEPair]
    rw [hval, Complex.norm_real, Real.norm_eq_abs]
    exact (hb t h.le).1

open Complex in
/-- **Growth of the entire completed zeta function (Mellin form).** -/
theorem norm_Lambda0_le :
    ∃ K q : ℝ, 0 < q ∧ 0 ≤ K ∧ ∀ s : ℂ,
      ‖(hurwitzEvenFEPair 0).Λ₀ s‖ ≤ K * (2 * (|s.re| + 2) / q) ^ (|s.re| + 2) := by
  obtain ⟨C, p, hp, hC, hb⟩ := exists_kernel_bound
  refine ⟨C * (1 + 2 / p), p, hp, by positivity, fun s => ?_⟩
  set R : ℝ := |s.re| + 2 with hR
  have hRpos : 0 < R := by positivity
  set A : ℝ := (2 * R / p) ^ R with hA
  have hApos : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  -- the majorant
  set b : ℝ → ℝ := fun t => C * A * ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t +
    Real.exp (-(p / 2) * t)) with hbdef
  have hbint : IntegrableOn b (Ioi 0) := by
    have h1 : Integrable (fun t : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
    refine Integrable.const_mul (Integrable.add h1.integrableOn ?_) _
    exact (integrableOn_exp_mul_Ioi (by linarith : -(p / 2) < 0) 0)
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • (hurwitzEvenFEPair 0).f_modif t‖ ≤ b t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (s - 1).re = s.re - 1 := by simp
    rw [hre]
    have hfm := norm_f_modif_le hb ht0
    have hσ : |s.re| = R - 2 := by rw [hR]; ring
    have hσle := le_abs_self s.re
    have hσge := neg_abs_le s.re
    by_cases h1 : 1 < t
    · rw [if_pos h1] at hfm
      have hpow : t ^ (s.re - 1) ≤ t ^ R :=
        Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
      have hexp := rpow_le_const_mul_exp ht0 hRpos hp
      have hind : (0 : ℝ) ≤ (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t :=
        indicator_nonneg (fun _ _ => zero_le_one) _
      calc t ^ (s.re - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
          ≤ t ^ R * (C * Real.exp (-p * t)) :=
            mul_le_mul hpow hfm (norm_nonneg _) (Real.rpow_nonneg ht0.le _)
        _ ≤ (A * Real.exp (p * t / 2)) * (C * Real.exp (-p * t)) :=
            mul_le_mul_of_nonneg_right hexp (by positivity)
        _ = C * A * Real.exp (-(p / 2) * t) := by
            have : Real.exp (p * t / 2) * Real.exp (-p * t) = Real.exp (-(p / 2) * t) := by
              rw [← Real.exp_add]; congr 1; ring
            calc A * Real.exp (p * t / 2) * (C * Real.exp (-p * t))
                = C * A * (Real.exp (p * t / 2) * Real.exp (-p * t)) := by ring
              _ = _ := by rw [this]
        _ ≤ b t := by
            simp only [hbdef]
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · rw [if_neg h1] at hfm
      push Not at h1
      have hu : (0 : ℝ) < 1 / t := by positivity
      have hu1 : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
      have hmem : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, h1⟩
      have hexp := rpow_le_const_mul_exp hu hRpos hp
      -- t^(σ-1) * t^(-1/2) = (1/t)^(3/2 - σ) ≤ (1/t)^R
      have hcomb : t ^ (s.re - 1) * t ^ (-(1 / 2 : ℝ)) = (1 / t) ^ (3 / 2 - s.re) := by
        rw [← Real.rpow_add ht0, show (1 / t) = t⁻¹ from one_div t, Real.inv_rpow ht0.le,
          ← Real.rpow_neg ht0.le]
        congr 1; ring
      have hpow : (1 / t) ^ (3 / 2 - s.re) ≤ (1 / t) ^ R :=
        Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
      calc t ^ (s.re - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
          ≤ t ^ (s.re - 1) * (C * t ^ (-(1 / 2 : ℝ)) * Real.exp (-p / t)) :=
            mul_le_mul_of_nonneg_left hfm (Real.rpow_nonneg ht0.le _)
        _ = C * ((1 / t) ^ (3 / 2 - s.re)) * Real.exp (-p / t) := by rw [← hcomb]; ring
        _ ≤ C * (A * Real.exp (p * (1 / t) / 2)) * Real.exp (-p / t) := by
            gcongr
            exact hpow.trans hexp
        _ = C * A * Real.exp (-(p / 2) / t) := by
            have : Real.exp (p * (1 / t) / 2) * Real.exp (-p / t) = Real.exp (-(p / 2) / t) := by
              rw [← Real.exp_add]; congr 1; field_simp; ring
            calc C * (A * Real.exp (p * (1 / t) / 2)) * Real.exp (-p / t)
                = C * A * (Real.exp (p * (1 / t) / 2) * Real.exp (-p / t)) := by ring
              _ = _ := by rw [this]
        _ ≤ C * A * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [Real.exp_le_one_iff]
            apply div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
        _ ≤ b t := by
            simp only [hbdef, indicator_of_mem hmem]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [Real.exp_pos (-(p / 2) * t)]
  have hmain : ‖(hurwitzEvenFEPair 0).Λ₀ s‖ ≤ ∫ t in Ioi (0 : ℝ), b t := by
    unfold WeakFEPair.Λ₀ mellin
    exact norm_integral_le_of_norm_le hbint
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbound))
  have hbval : ∫ t in Ioi (0 : ℝ), b t = C * A * (1 + 2 / p) := by
    have h1 : Integrable (fun t : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
    have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(p / 2) * t)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith : -(p / 2) < 0) 0
    have e1 : ∫ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t = 1 := by
      rw [setIntegral_indicator measurableSet_Ioc]
      have : Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; constructor
        · exact fun h => h.2
        · exact fun h => ⟨h.1, h⟩
      rw [this]; simp
    have e2 : ∫ t in Ioi (0 : ℝ), Real.exp (-(p / 2) * t) = 2 / p := by
      rw [integral_exp_mul_Ioi (by linarith : -(p / 2) < 0) 0]
      field_simp; simp
    simp only [hbdef]
    rw [integral_const_mul, integral_add h1.integrableOn h2, e1, e2]
  rw [hbval] at hmain
  calc ‖(hurwitzEvenFEPair 0).Λ₀ s‖ ≤ C * A * (1 + 2 / p) := hmain
    _ = C * (1 + 2 / p) * A := by ring

/-- A quadratic is dominated by `x ^ (2 + ε)` up to a constant. -/
theorem quad_le_rpow_add {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → c * (1 + x) ^ 2 ≤ x ^ (2 + ε) + C := by
  refine ⟨2 * c + 2 * c * (2 * c) ^ (2 / ε), fun x hx => ?_⟩
  have h1 : c * (1 + x) ^ 2 ≤ 2 * c + 2 * c * x ^ 2 := by nlinarith [sq_nonneg (1 - x)]
  have hpow : x ^ (2 + ε) = x ^ 2 * x ^ ε := by
    rcases hx.eq_or_lt with h | h
    · subst h; simp [Real.zero_rpow (by linarith : (2 + ε) ≠ 0), Real.zero_rpow hε.ne']
    · rw [Real.rpow_add h]; simp
  by_cases hx0 : 2 * c ≤ x ^ ε
  · have : 2 * c * x ^ 2 ≤ x ^ (2 + ε) := by
      rw [hpow]; nlinarith [sq_nonneg x]
    have hC : 0 ≤ 2 * c * (2 * c) ^ (2 / ε) := by positivity
    nlinarith
  · push Not at hx0
    have hxlt : x < (2 * c) ^ (1 / ε) := by
      by_contra hge
      push Not at hge
      have := Real.rpow_le_rpow (by positivity) hge hε.le
      rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at this
      linarith
    have hx2 : x ^ 2 ≤ ((2 * c) ^ (1 / ε)) ^ 2 :=
      pow_le_pow_left₀ hx hxlt.le 2
    have : ((2 * c) ^ (1 / ε)) ^ 2 = (2 * c) ^ (2 / ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
    have hnn : 0 ≤ x ^ (2 + ε) := Real.rpow_nonneg hx _
    nlinarith

open Complex in
/-- **`ξ` has order at most 2** (in fact 1; the weaker exponent is all the counting needs). -/
theorem xi_hasOrderLE_two : Complex.HasOrderLE GppLogDerivZeroFree.xi 2 := by
  intro ε hε
  obtain ⟨K, q, hq, hK, hΛ⟩ := norm_Lambda0_le
  set c : ℝ := 2 + 8 / q with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨C₁, hC₁⟩ := quad_le_rpow_add hcpos hε
  refine ⟨(1 + K) * Real.exp |C₁|, by positivity, fun z => ?_⟩
  set x : ℝ := ‖z‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg z
  -- bound on completedRiemannZeta₀
  have hL : ‖completedRiemannZeta₀ z‖ ≤ K * Real.exp (2 * (x / 2 + 2) ^ 2 / q) := by
    have h1 : completedRiemannZeta₀ z = (hurwitzEvenFEPair 0).Λ₀ (z / 2) / 2 := rfl
    rw [h1, norm_div]
    have h2 := hΛ (z / 2)
    set R : ℝ := |(z / 2).re| + 2 with hR
    have hRle : R ≤ x / 2 + 2 := by
      have : |(z / 2).re| ≤ ‖z / 2‖ := Complex.abs_re_le_norm _
      rw [norm_div] at this
      have e : (z / 2).re = z.re / 2 := by simp
      rw [e] at this
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2] at this
      rw [hR, e]; linarith
    have hRpos : 0 < R := by positivity
    have hlog : (2 * R / q) ^ R ≤ Real.exp (2 * R * R / q) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      apply Real.exp_le_exp.2
      have : Real.log (2 * R / q) ≤ 2 * R / q := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      calc Real.log (2 * R / q) * R ≤ (2 * R / q) * R := mul_le_mul_of_nonneg_right this hRpos.le
        _ = 2 * R * R / q := by ring
    have h3 : Real.exp (2 * R * R / q) ≤ Real.exp (2 * (x / 2 + 2) ^ 2 / q) := by
      apply Real.exp_le_exp.2
      have : R * R ≤ (x / 2 + 2) ^ 2 := by nlinarith
      have hq' : 0 < q := hq
      calc 2 * R * R / q = 2 * (R * R) / q := by ring
        _ ≤ 2 * (x / 2 + 2) ^ 2 / q := by gcongr
    have h4 : ‖(hurwitzEvenFEPair 0).Λ₀ (z / 2)‖ ≤ K * Real.exp (2 * (x / 2 + 2) ^ 2 / q) :=
      h2.trans (mul_le_mul_of_nonneg_left (hlog.trans h3) hK)
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    linarith [Real.exp_pos (2 * (x / 2 + 2) ^ 2 / q), mul_nonneg hK (Real.exp_pos (2 * (x / 2 + 2) ^ 2 / q)).le]
  -- assemble
  have hxi : ‖GppLogDerivZeroFree.xi z‖ ≤
      (1 + x * (x + 1) * (K * Real.exp (2 * (x / 2 + 2) ^ 2 / q))) / 2 := by
    unfold GppLogDerivZeroFree.xi
    rw [norm_div]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_mul]
    have hz1 : ‖z - 1‖ ≤ x + 1 := by
      simpa using norm_sub_le z 1
    gcongr
  have hpoly : x * (x + 1) ≤ Real.exp (2 * (1 + x)) := by
    have h1 : x * (x + 1) ≤ (1 + x) ^ 2 := by nlinarith
    have h2 : (1 + x) ^ 2 ≤ Real.exp (1 + x) ^ 2 := by
      have := Real.add_one_le_exp (1 + x)
      nlinarith
    calc x * (x + 1) ≤ (1 + x) ^ 2 := h1
      _ ≤ Real.exp (1 + x) ^ 2 := h2
      _ = Real.exp (2 * (1 + x)) := by rw [← Real.exp_nat_mul]; norm_num
  have hexp : 2 * (1 + x) + 2 * (x / 2 + 2) ^ 2 / q ≤ c * (1 + x) ^ 2 := by
    have hq' : 0 < q := hq
    have : 2 * (x / 2 + 2) ^ 2 / q ≤ 8 / q * (1 + x) ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hq'.le
      nlinarith
    have h1 : 2 * (1 + x) ≤ 2 * (1 + x) ^ 2 := by nlinarith
    rw [hc]; nlinarith
  have hfin : Real.exp (2 * (1 + x)) * (K * Real.exp (2 * (x / 2 + 2) ^ 2 / q)) ≤
      K * Real.exp (x ^ (2 + ε) + C₁) := by
    rw [mul_comm K, ← mul_assoc, ← Real.exp_add, mul_comm K (Real.exp (x ^ (2 + ε) + C₁))]
    apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 _) hK
    linarith [hC₁ x hx0]
  calc ‖GppLogDerivZeroFree.xi z‖ ≤ _ := hxi
    _ ≤ (1 + K * Real.exp (x ^ (2 + ε) + C₁)) / 2 := by
        have : x * (x + 1) * (K * Real.exp (2 * (x / 2 + 2) ^ 2 / q)) ≤
            K * Real.exp (x ^ (2 + ε) + C₁) :=
          (mul_le_mul_of_nonneg_right hpoly (by positivity)).trans hfin
        linarith
    _ ≤ (1 + K) * Real.exp |C₁| * Real.exp (x ^ (2 + ε)) := by
        have hx1 : 1 ≤ Real.exp (x ^ (2 + ε)) := Real.one_le_exp (Real.rpow_nonneg hx0 _)
        have hC1 : Real.exp C₁ ≤ Real.exp |C₁| := Real.exp_le_exp.2 (le_abs_self _)
        have hC2 : 1 ≤ Real.exp |C₁| := Real.one_le_exp (abs_nonneg _)
        rw [Real.exp_add]
        have e1 : K * (Real.exp (x ^ (2 + ε)) * Real.exp C₁) ≤
            K * (Real.exp (x ^ (2 + ε)) * Real.exp |C₁|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC1 (by positivity)) hK
        nlinarith [mul_nonneg hK (Real.exp_pos |C₁|).le, mul_nonneg (mul_nonneg hK (Real.exp_pos |C₁|).le) (Real.exp_pos (x ^ (2 + ε))).le]

end GppXiOrder
