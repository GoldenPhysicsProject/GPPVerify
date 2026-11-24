/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Complex.Order

/-!
# Positive-definite functions on `ℝ`

A function `φ : ℝ → ℂ` is *positive definite* if for every finite family of points `x i` and
coefficients `c i`,

  `0 ≤ ∑ i, ∑ j, conj (c i) * c j * φ (x i - x j)`,

where `≤` is the order `ComplexOrder` on `ℂ` (`0 ≤ z` iff `z` is real and nonnegative). This is
the same convention Mathlib uses for positive semidefinite complex matrices, and it packages the
two facts the definition is meant to express (the quadratic form is real, and it is nonnegative)
in one inequality. This file is the first layer towards Bochner's theorem.

## Main results

* `IsPositiveDefinite.zero_nonneg`: `0 ≤ φ 0`.
* `IsPositiveDefinite.apply_neg`: `φ (-x) = conj (φ x)`.
* `IsPositiveDefinite.norm_le`: `‖φ x‖ ≤ (φ 0).re`.
* Closure under addition, nonnegative real scaling, conjugation and dilation.
* `isPositiveDefinite_charFun`: the characteristic function of a finite measure on `ℝ` is
  positive definite.
* `isPositiveDefinite_exp_neg_sq_div_two`: `t ↦ exp (-t ^ 2 / 2)` is positive definite.
* `IsPositiveDefinite.intervalIntegral_nonneg`: for continuous positive-definite `φ` and
  continuous `g`, `0 ≤ ∫_a^b ∫_a^b conj (g x) * g y * φ (x - y)`, by comparison with Riemann
  sums on a uniform grid.
* `IsPositiveDefinite.integral_nonneg`: the same over `ℝ` for continuous compactly supported `g`.
-/

open MeasureTheory
open scoped ComplexOrder ComplexConjugate

namespace Complex

/-- A function `φ : ℝ → ℂ` is positive definite if every finite quadratic form
`∑ i, ∑ j, conj (c i) * c j * φ (x i - x j)` is real and nonnegative. -/
def IsPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, conj (c i) * c j * φ (x i - x j)

namespace IsPositiveDefinite

variable {φ ψ : ℝ → ℂ}

/-- The two-point form. -/
theorem two_point (hφ : IsPositiveDefinite φ) (a b : ℝ) (c₁ c₂ : ℂ) :
    0 ≤ conj c₁ * c₁ * φ 0 + conj c₁ * c₂ * φ (a - b) + conj c₂ * c₁ * φ (b - a) +
      conj c₂ * c₂ * φ 0 := by
  have h := hφ 2 ![a, b] ![c₁, c₂]
  convert h using 1
  simp [Fin.sum_univ_two]
  ring

/-- `φ 0` is real and nonnegative. -/
theorem zero_nonneg (hφ : IsPositiveDefinite φ) : 0 ≤ φ 0 := by
  have h := hφ 1 ![0] ![1]
  simpa using h

theorem im_zero (hφ : IsPositiveDefinite φ) : (φ 0).im = 0 :=
  ((nonneg_iff.mp hφ.zero_nonneg).2).symm

theorem re_zero_nonneg (hφ : IsPositiveDefinite φ) : 0 ≤ (φ 0).re :=
  (nonneg_iff.mp hφ.zero_nonneg).1

/-- **Hermitian symmetry.** `φ (-x) = conj (φ x)`. -/
theorem apply_neg (hφ : IsPositiveDefinite φ) (x : ℝ) : φ (-x) = conj (φ x) := by
  have h1 := (nonneg_iff.mp (hφ.two_point 0 x 1 1)).2
  have h2 := (nonneg_iff.mp (hφ.two_point 0 x 1 I)).2
  have h0 := hφ.im_zero
  simp only [zero_sub, sub_zero, map_one, one_mul, mul_one, add_im, conj_I, mul_im, I_re,
    I_im, neg_re, neg_im, zero_mul, mul_re] at h1 h2
  apply Complex.ext <;> simp only [conj_re, conj_im] <;> linarith

/-- **`‖φ x‖ ≤ φ 0`.** -/
theorem norm_le (hφ : IsPositiveDefinite φ) (x : ℝ) : ‖φ x‖ ≤ (φ 0).re := by
  set w := φ x with hw
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0]; exact hφ.re_zero_nonneg
  have hneg : φ (0 - x) = conj w := by rw [zero_sub, hφ.apply_neg]
  have h := (nonneg_iff.mp (hφ.two_point x 0 (‖w‖ : ℂ) (-conj w))).1
  rw [sub_zero, hneg, ← hw] at h
  have h0 := hφ.im_zero
  have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.sq_norm_sub_sq_re]; ring
  simp only [add_re, mul_re, conj_re, conj_im, ofReal_re, ofReal_im, neg_re, neg_im, mul_im,
    sub_zero, mul_zero, neg_neg, zero_add] at h
  rw [h0] at h
  -- h : 2 ‖w‖² (φ 0).re - 2 ‖w‖ (re² + im²) ≥ 0, up to arrangement
  nlinarith [hn, hpos, mul_pos hpos hpos]

/-- Sums of positive-definite functions are positive definite. -/
theorem add (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (φ + ψ) := by
  intro n x c
  have e : ∑ i, ∑ j, conj (c i) * c j * (φ + ψ) (x i - x j) =
      (∑ i, ∑ j, conj (c i) * c j * φ (x i - x j)) +
        ∑ i, ∑ j, conj (c i) * c j * ψ (x i - x j) := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [e]
  exact add_nonneg (hφ n x c) (hψ n x c)

/-- Nonnegative real multiples of positive-definite functions are positive definite. -/
theorem const_mul (hφ : IsPositiveDefinite φ) {r : ℝ} (hr : 0 ≤ r) :
    IsPositiveDefinite (fun x => (r : ℂ) * φ x) := by
  intro n x c
  have e : ∑ i, ∑ j, conj (c i) * c j * ((r : ℂ) * φ (x i - x j)) =
      (r : ℂ) * ∑ i, ∑ j, conj (c i) * c j * φ (x i - x j) := by
    rw [Finset.mul_sum]; congr 1; funext i
    rw [Finset.mul_sum]; congr 1; funext j; ring
  rw [e]
  exact mul_nonneg (zero_le_real.mpr hr) (hφ n x c)

/-- The conjugate of a positive-definite function is positive definite. -/
theorem star (hφ : IsPositiveDefinite φ) : IsPositiveDefinite (fun x => conj (φ x)) := by
  intro n x c
  have h := hφ n x (fun i => (starRingEnd ℂ) (c i))
  have e : ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (φ (x i - x j)) =
      (starRingEnd ℂ) (∑ i, ∑ j, (starRingEnd ℂ) ((starRingEnd ℂ) (c i)) *
        (starRingEnd ℂ) (c j) * φ (x i - x j)) := by
    simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [e]
  obtain ⟨h1, h2⟩ := nonneg_iff.mp h
  exact nonneg_iff.mpr ⟨by rwa [conj_re], by rw [conj_im, ← h2, neg_zero]⟩

/-- Dilations of positive-definite functions are positive definite. -/
theorem comp_mul (hφ : IsPositiveDefinite φ) (a : ℝ) :
    IsPositiveDefinite (fun x => φ (a * x)) := by
  intro n x c
  have h := hφ n (fun i => a * x i) c
  simpa only [mul_sub] using h

end IsPositiveDefinite

/-- **The characteristic function of a finite measure is positive definite.** -/
theorem isPositiveDefinite_charFun (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsPositiveDefinite (charFun μ) := by
  intro n x c
  have hint : ∀ t : ℝ, Integrable (fun y : ℝ => cexp (t * y * I)) μ := by
    intro t
    refine (integrable_const (1 : ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [← ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  set S : ℝ → ℂ := fun y => ∑ j, c j * cexp (-(x j * y) * I) with hS
  have hpt : ∀ y : ℝ, ∑ i, ∑ j, conj (c i) * c j * cexp (((x i - x j : ℝ) : ℂ) * y * I) =
      ((Complex.normSq (S y) : ℝ) : ℂ) := by
    intro y
    rw [Complex.normSq_eq_conj_mul_self, hS]
    simp only [map_sum, map_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.exp_conj]
    have e1 : (starRingEnd ℂ) (-((x i : ℂ) * y) * I) = (x i : ℂ) * y * I := by
      simp [map_mul, map_neg, conj_I, conj_ofReal]
    rw [e1]
    have e2 : cexp (((x i - x j : ℝ) : ℂ) * y * I) =
        cexp ((x i : ℂ) * y * I) * cexp (-((x j : ℂ) * y) * I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [e2]; ring
  have hsum : ∑ i, ∑ j, conj (c i) * c j * charFun μ (x i - x j) =
      ∫ y, ((Complex.normSq (S y) : ℝ) : ℂ) ∂μ := by
    simp only [charFun_apply_real]
    rw [← integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint (x i - x j)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint (x i - x j)).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  rw [hsum, integral_complex_ofReal]
  exact zero_le_real.mpr (integral_nonneg fun y => Complex.normSq_nonneg _)

/-- **The Gaussian `t ↦ exp (-t ^ 2 / 2)` is positive definite**, as the characteristic function
of the standard normal distribution. -/
theorem isPositiveDefinite_exp_neg_sq_div_two :
    IsPositiveDefinite (fun t : ℝ => cexp (-(t : ℂ) ^ 2 / 2)) := by
  have h := isPositiveDefinite_charFun (ProbabilityTheory.gaussianReal 0 1)
  have e : charFun (ProbabilityTheory.gaussianReal 0 1) = fun t : ℝ => cexp (-(t : ℂ) ^ 2 / 2) := by
    funext t
    rw [ProbabilityTheory.charFun_gaussianReal]
    congr 1
    push_cast
    ring
  rwa [e] at h

/-! ### Integral positivity -/

/-- A complex number that is approximated arbitrarily well by nonnegative ones is nonnegative. -/
theorem nonneg_of_forall_exists_norm_sub_le {w : ℂ}
    (h : ∀ ε > 0, ∃ z : ℂ, 0 ≤ z ∧ ‖w - z‖ ≤ ε) : 0 ≤ w := by
  refine nonneg_iff.mpr ⟨?_, ?_⟩
  · by_contra hneg
    push Not at hneg
    obtain ⟨z, hz, hd⟩ := h (-w.re / 2) (by linarith)
    have h1 := (nonneg_iff.mp hz).1
    have h2 : |(w - z).re| ≤ ‖w - z‖ := abs_re_le_norm _
    rw [sub_re] at h2
    have := (abs_le.mp h2).1
    linarith
  · by_contra hne
    have hpos : 0 < |w.im| := abs_pos.mpr (Ne.symm hne)
    obtain ⟨z, hz, hd⟩ := h (|w.im| / 2) (by linarith)
    have h1 := (nonneg_iff.mp hz).2
    have h2 : |(w - z).im| ≤ ‖w - z‖ := abs_im_le_norm _
    rw [sub_im, ← h1, sub_zero] at h2
    linarith

namespace IsPositiveDefinite

variable {φ : ℝ → ℂ}

/-- **Integral positivity on an interval.** For a continuous positive-definite `φ` and a
continuous `g`, the double integral `∫_a^b ∫_a^b conj (g x) * g y * φ (x - y)` is real and
nonnegative. The proof compares it with left-endpoint Riemann sums on a uniform grid; each sum is
a finite positive-definite form with coefficients `h * g (t k)`. -/
theorem intervalIntegral_nonneg (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) {g : ℝ → ℂ}
    (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ x in a..b, ∫ y in a..b, conj (g x) * g y * φ (x - y) := by
  set F : ℝ → ℝ → ℂ := fun x y => conj (g x) * g y * φ (x - y) with hF
  have hFc : Continuous (Function.uncurry F) :=
    ((continuous_conj.comp (hg.comp continuous_fst)).mul (hg.comp continuous_snd)).mul
      (hφc.comp (continuous_fst.sub continuous_snd))
  have hUC := (isCompact_Icc.prod (isCompact_Icc (a := a) (b := b))).uniformContinuousOn_of_continuous
    (hFc.continuousOn (s := Set.Icc a b ×ˢ Set.Icc a b))
  rw [Metric.uniformContinuousOn_iff] at hUC
  apply nonneg_of_forall_exists_norm_sub_le
  intro ε hε
  set C : ℝ := (b - a) ^ 2 + 1 with hC
  have hCpos : 0 < C := by positivity
  obtain ⟨δ, hδ, hδF⟩ := hUC (ε / C) (div_pos hε hCpos)
  obtain ⟨m, hm⟩ := exists_nat_gt ((b - a) / δ)
  set n : ℕ := m + 1 with hn_def
  have hn : (0 : ℝ) < n := by positivity
  set h : ℝ := (b - a) / n with hh
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hn.le
  have hnh : (n : ℝ) * h = b - a := by rw [hh]; field_simp
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hn]
    have h1 : (b - a) / δ < n := by rw [hn_def]; push_cast; linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  set t : ℕ → ℝ := fun k => a + k * h with ht
  have ht0 : t 0 = a := by simp [ht]
  have htn : t n = b := by simp only [ht]; rw [hnh]; ring
  have hdiff : ∀ k, t (k + 1) - t k = h := fun k => by simp only [ht]; push_cast; ring
  have htle : ∀ k, t k ≤ t (k + 1) := fun k => by linarith [hdiff k]
  have hmem : ∀ k < n, ∀ x ∈ Set.Icc (t k) (t (k + 1)), x ∈ Set.Icc a b := by
    intro k hk x hx
    have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    constructor
    · have : a ≤ t k := by simp only [ht]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
      linarith [hx.1]
    · have : t (k + 1) ≤ b := by
        rw [← htn]; simp only [ht]; push_cast; nlinarith
      linarith [hx.2]
  -- splitting an interval integral along the grid
  have hsplit : ∀ G : ℝ → ℂ, Continuous G →
      ∫ x in a..b, G x = ∑ k ∈ Finset.range n, ∫ x in t k..t (k + 1), G x := by
    intro G hG
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (a := t) (n := n) (fun k _ => hG.intervalIntegrable _ _)
    rw [ht0, htn] at this
    exact this.symm
  have hcont_inner : ∀ c d : ℝ, Continuous fun x => ∫ y in c..d, F x y :=
    fun c d => intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFc c d
  have hI : ∫ x in a..b, ∫ y in a..b, F x y =
      ∑ l ∈ Finset.range n, ∑ k ∈ Finset.range n,
        ∫ x in t k..t (k + 1), ∫ y in t l..t (l + 1), F x y := by
    have e1 : ∀ x, ∫ y in a..b, F x y = ∑ l ∈ Finset.range n, ∫ y in t l..t (l + 1), F x y :=
      fun x => hsplit (F x) (hFc.uncurry_left x)
    simp_rw [e1]
    rw [intervalIntegral.integral_finsetSum (fun l _ => (hcont_inner _ _).intervalIntegrable _ _)]
    exact Finset.sum_congr rfl fun l _ => hsplit _ (hcont_inner _ _)
  -- the Riemann sum
  set S : ℂ := ∑ l ∈ Finset.range n, ∑ k ∈ Finset.range n,
    (h : ℂ) * ((h : ℂ) * F (t k) (t l)) with hS
  have hSnn : 0 ≤ S := by
    have hpd := hφ n (fun k => t k) (fun k => (h : ℂ) * g (t k))
    have e : S = ∑ i : Fin n, ∑ j : Fin n,
        conj ((h : ℂ) * g (t i)) * ((h : ℂ) * g (t j)) * φ (t i - t j) := by
      rw [hS, Finset.sum_comm, Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hF, map_mul, conj_ofReal]
      ring
    rw [e]; exact hpd
  refine ⟨S, hSnn, ?_⟩
  -- the error per cell
  have hcell : ∀ k < n, ∀ l < n,
      ‖(∫ x in t k..t (k + 1), ∫ y in t l..t (l + 1), F x y) -
        (h : ℂ) * ((h : ℂ) * F (t k) (t l))‖ ≤ h * (h * (ε / C)) := by
    intro k hk l hl
    set c := F (t k) (t l) with hc
    have hinner : ∀ x, (∫ y in t l..t (l + 1), F x y) - (h : ℂ) * c =
        ∫ y in t l..t (l + 1), (F x y - c) := by
      intro x
      rw [intervalIntegral.integral_sub ((hFc.uncurry_left x).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, hdiff l, Complex.real_smul]
    have hout : (∫ x in t k..t (k + 1), ∫ y in t l..t (l + 1), F x y) - (h : ℂ) * ((h : ℂ) * c) =
        ∫ x in t k..t (k + 1), ((∫ y in t l..t (l + 1), F x y) - (h : ℂ) * c) := by
      rw [intervalIntegral.integral_sub ((hcont_inner _ _).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, hdiff k, Complex.real_smul]
    rw [hout]
    have hb : ∀ x ∈ Set.uIoc (t k) (t (k + 1)),
        ‖(∫ y in t l..t (l + 1), F x y) - (h : ℂ) * c‖ ≤ (ε / C) * |t (l + 1) - t l| := by
      intro x hx
      rw [hinner x]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      rw [Set.uIoc_of_le (htle k)] at hx
      rw [Set.uIoc_of_le (htle l)] at hy
      have hxK := hmem k hk x ⟨hx.1.le, hx.2⟩
      have hyK := hmem l hl y ⟨hy.1.le, hy.2⟩
      have htkK := hmem k hk (t k) ⟨le_rfl, htle k⟩
      have htlK := hmem l hl (t l) ⟨le_rfl, htle l⟩
      have hd : dist (x, y) (t k, t l) < δ := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        have h1 : |x - t k| ≤ h := by
          rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.2, hdiff k]
        have h2 : |y - t l| ≤ h := by
          rw [abs_of_pos (by linarith [hy.1])]; linarith [hy.2, hdiff l]
        exact max_lt (lt_of_le_of_lt h1 hhδ) (lt_of_le_of_lt h2 hhδ)
      have := hδF (x, y) ⟨hxK, hyK⟩ (t k, t l) ⟨htkK, htlK⟩ hd
      rw [dist_eq_norm] at this
      exact this.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [hdiff l, hdiff k, abs_of_nonneg hh0] at this
    linarith [this]
  -- summing the errors
  have htot : ‖(∫ x in a..b, ∫ y in a..b, F x y) - S‖ ≤ (n : ℝ) * ((n : ℝ) * (h * (h * (ε / C)))) := by
    rw [hI, hS, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ l ∈ Finset.range n, ‖∑ k ∈ Finset.range n, (∫ x in t k..t (k + 1),
        ∫ y in t l..t (l + 1), F x y) - ∑ k ∈ Finset.range n, (h : ℂ) * ((h : ℂ) * F (t k) (t l))‖
        ≤ (n : ℝ) * (h * (h * (ε / C))) := by
      intro l hl
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_sum fun k (hk : k ∈ Finset.range n) =>
        hcell k (Finset.mem_range.mp hk) l (Finset.mem_range.mp hl)
      simpa using this
    have := Finset.sum_le_sum this
    simpa using this
  have hfin : (n : ℝ) * ((n : ℝ) * (h * (h * (ε / C)))) ≤ ε := by
    have e : (n : ℝ) * ((n : ℝ) * (h * (h * (ε / C)))) = (n * h) ^ 2 * (ε / C) := by ring
    rw [e, hnh, mul_div_assoc', div_le_iff₀ hCpos, hC]
    nlinarith [sq_nonneg (b - a)]
  exact htot.trans hfin

/-- **Integral positivity.** For a continuous positive-definite `φ` and a continuous compactly
supported `g`, `∫ ∫ conj (g x) * g y * φ (x - y)` is real and nonnegative. -/
theorem integral_nonneg (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) {g : ℝ → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    0 ≤ ∫ x, ∫ y, conj (g x) * g y * φ (x - y) := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hR0 : ∀ x : ℝ, x ∉ Set.Ioc (-(|R| + 1)) (|R| + 1) → g x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have := hR hxs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    apply hx
    constructor
    · have := neg_abs_le x; linarith [le_abs_self R]
    · linarith [le_abs_self x, le_abs_self R]
  set M := |R| + 1 with hM
  have hle : -M ≤ M := by rw [hM]; linarith [abs_nonneg R]
  have hinner : ∀ x, ∫ y, conj (g x) * g y * φ (x - y) =
      ∫ y in -M..M, conj (g x) * g y * φ (x - y) := by
    intro x
    rw [intervalIntegral.integral_of_le hle]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [hR0 y hy, mul_zero, zero_mul]
  have houter : ∫ x, ∫ y, conj (g x) * g y * φ (x - y) =
      ∫ x in -M..M, ∫ y in -M..M, conj (g x) * g y * φ (x - y) := by
    simp_rw [hinner]
    rw [intervalIntegral.integral_of_le hle]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    simp [hR0 x hx]
  rw [houter]
  exact hφ.intervalIntegral_nonneg hφc hg hle

end IsPositiveDefinite

end Complex
