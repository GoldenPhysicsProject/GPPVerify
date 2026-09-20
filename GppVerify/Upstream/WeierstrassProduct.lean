/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.WeierstrassFactor
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Weierstrass products

Given a sequence `a : ℕ → ℂ` of nonzero points with `∑ ‖a n‖⁻¹ ^ (p + 1) < ∞`, the infinite
product

  `W p a z = ∏' n, E p (z / a n)`

converges locally uniformly on `ℂ` and defines an entire function.

This is the constructive half of the Weierstrass factorisation theorem: it produces an entire
function with any prescribed zero set that is not too dense. It rests entirely on
`Complex.norm_one_sub_weierstrassFactor_le`: on the disc `‖z‖ < R` and for every `n` with
`R ≤ ‖a n‖`,

  `‖E p (z / a n) - 1‖ ≤ (R / ‖a n‖) ^ (p + 1)`,

which is summable, so Mathlib's `hasProdLocallyUniformlyOn_nat_one_add` applies on each disc,
and a locally uniform limit of holomorphic functions is holomorphic.

## Main results

* `Complex.hasProdLocallyUniformlyOn_weierstrassProduct` : local uniform convergence on each
  disc.
* `Complex.differentiable_weierstrassProduct` : the product is entire.
* `Complex.weierstrassProduct_eq_zero_iff` : it vanishes exactly at the prescribed points.
* `Complex.weierstrassProduct_zero` : its value at the origin is `1`, so it is not identically
  zero.
-/

open Filter Metric Topology

namespace Complex

/-- The Weierstrass product of genus `p` attached to a sequence of nonzero points `a`. -/
noncomputable def weierstrassProduct (p : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n, weierstrassFactor p (z / a n)

@[simp]
theorem weierstrassProduct_zero (p : ℕ) (a : ℕ → ℂ) : weierstrassProduct p a 0 = 1 := by
  simp [weierstrassProduct]

variable {p : ℕ} {a : ℕ → ℂ}

/-- Summability of `‖a n‖⁻¹ ^ (p + 1)` forces `‖a n‖` past any bound. -/
theorem eventually_lt_norm (ha : ∀ n, a n ≠ 0)
    (hs : Summable fun n => ‖a n‖⁻¹ ^ (p + 1)) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in atTop, R < ‖a n‖ := by
  have h0 : Tendsto (fun n => ‖a n‖⁻¹ ^ (p + 1)) atTop (𝓝 0) := hs.tendsto_atTop_zero
  have hpos : (0 : ℝ) < (R⁻¹) ^ (p + 1) := by positivity
  filter_upwards [h0.eventually (eventually_lt_nhds hpos)] with n hn
  have hnpos : 0 < ‖a n‖ := norm_pos_iff.2 (ha n)
  have h1 : ‖a n‖⁻¹ < R⁻¹ := lt_of_pow_lt_pow_left₀ (p + 1) (le_of_lt (by positivity)) hn
  exact (inv_lt_inv₀ hnpos hR).1 h1

/-- On the disc of radius `R`, the factors differ from `1` by a summable amount, so the
product converges locally uniformly there. -/
theorem hasProdLocallyUniformlyOn_weierstrassProduct (ha : ∀ n, a n ≠ 0)
    (hs : Summable fun n => ‖a n‖⁻¹ ^ (p + 1)) {R : ℝ} (hR : 0 < R) :
    HasProdLocallyUniformlyOn (fun n z => weierstrassFactor p (z / a n))
      (weierstrassProduct p a) (ball (0 : ℂ) R) := by
  have hu : Summable fun n => R ^ (p + 1) * ‖a n‖⁻¹ ^ (p + 1) := hs.mul_left _
  have hbound : ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) R,
      ‖weierstrassFactor p (z / a n) - 1‖ ≤ R ^ (p + 1) * ‖a n‖⁻¹ ^ (p + 1) := by
    filter_upwards [eventually_lt_norm ha hs hR] with n hn z hz
    have hnpos : 0 < ‖a n‖ := norm_pos_iff.2 (ha n)
    have hzR : ‖z‖ < R := by simpa using mem_ball_zero_iff.1 hz
    have hq : ‖z / a n‖ ≤ 1 := by
      rw [norm_div]
      rw [div_le_one hnpos]
      exact le_of_lt (hzR.trans hn)
    have h := norm_one_sub_weierstrassFactor_le p hq
    rw [← norm_neg, neg_sub] at h
    refine h.trans ?_
    rw [norm_div, div_pow, div_eq_mul_inv, ← inv_pow]
    gcongr
  have hcts : ∀ n : ℕ, ContinuousOn (fun z : ℂ => weierstrassFactor p (z / a n) - 1)
      (ball (0 : ℂ) R) := fun n =>
    (((differentiable_weierstrassFactor p).comp
      (differentiable_id.div_const (a n))).continuous.sub continuous_const).continuousOn
  have h := Summable.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun n z => weierstrassFactor p (z / a n) - 1) isOpen_ball hu hbound hcts
  have hrw : ∀ (n : ℕ) (z : ℂ),
      1 + (weierstrassFactor p (z / a n) - 1) = weierstrassFactor p (z / a n) := by
    intro n z; ring
  simp only [hrw] at h
  exact h

/-- The Weierstrass product is holomorphic on every disc, hence entire. -/
theorem differentiable_weierstrassProduct (ha : ∀ n, a n ≠ 0)
    (hs : Summable fun n => ‖a n‖⁻¹ ^ (p + 1)) :
    Differentiable ℂ (weierstrassProduct p a) := by
  intro z
  set R : ℝ := ‖z‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  have hmem : z ∈ ball (0 : ℂ) R := by
    simp only [mem_ball_zero_iff, hRdef]
    linarith
  have htl := (hasProdLocallyUniformlyOn_weierstrassProduct ha hs hR).tendstoLocallyUniformlyOn_finsetRange
  have hFdiff : ∀ᶠ N in atTop, DifferentiableOn ℂ
      (fun z : ℂ => ∏ i ∈ Finset.range N, weierstrassFactor p (z / a i)) (ball (0 : ℂ) R) := by
    filter_upwards with N
    exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiable_weierstrassFactor p).comp (differentiable_id.div_const (a i))).differentiableOn
  have hdiff : DifferentiableOn ℂ (weierstrassProduct p a) (ball (0 : ℂ) R) :=
    htl.differentiableOn hFdiff isOpen_ball
  exact hdiff.differentiableAt (isOpen_ball.mem_nhds hmem)

/-! ### The zero set -/

/-- If one factor vanishes, the whole product converges to `0`: every large enough partial
product contains that factor. -/
theorem _root_.hasProd_zero_of_eq_zero {ι M : Type*} [CommMonoidWithZero M] [TopologicalSpace M]
    {f : ι → M} {i₀ : ι} (h : f i₀ = 0) : HasProd f 0 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ({i₀} : Finset ι)] with s hs
  exact (Finset.prod_eq_zero (hs (Finset.mem_singleton_self i₀)) h).symm

/-- At a fixed point the factors differ from `1` by an absolutely summable amount. -/
theorem summable_norm_weierstrassFactor_sub_one (ha : ∀ n, a n ≠ 0)
    (hs : Summable fun n => ‖a n‖⁻¹ ^ (p + 1)) (z : ℂ) :
    Summable fun n => ‖weierstrassFactor p (z / a n) - 1‖ := by
  have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
  refine Summable.of_norm_bounded_eventually
    (g := fun n => (‖z‖ + 1) ^ (p + 1) * ‖a n‖⁻¹ ^ (p + 1)) (hs.mul_left _) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_lt_norm ha hs hR] with n hn
  have hnpos : 0 < ‖a n‖ := norm_pos_iff.2 (ha n)
  have hzR : ‖z‖ < ‖z‖ + 1 := by linarith
  have hq : ‖z / a n‖ ≤ 1 := by
    rw [norm_div, div_le_one hnpos]
    exact le_of_lt (hzR.trans hn)
  have h := norm_one_sub_weierstrassFactor_le p hq
  rw [← norm_neg, neg_sub] at h
  refine (norm_norm _).le.trans (h.trans ?_)
  rw [norm_div, div_pow, div_eq_mul_inv, ← inv_pow]
  gcongr

/-- **The zero set of a Weierstrass product.** It vanishes exactly at the prescribed points. -/
theorem weierstrassProduct_eq_zero_iff (ha : ∀ n, a n ≠ 0)
    (hs : Summable fun n => ‖a n‖⁻¹ ^ (p + 1)) {z : ℂ} :
    weierstrassProduct p a z = 0 ↔ ∃ n, a n = z := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hne : ∀ n, 1 + (weierstrassFactor p (z / a n) - 1) ≠ 0 := by
      intro n
      have : z / a n ≠ 1 := fun hq => hcon n (div_eq_one_iff_eq (ha n) |>.mp hq).symm
      simpa using weierstrassFactor_ne_zero (p := p) this
    have hsum : Summable fun n => ‖weierstrassFactor p (z / a n) - 1‖ :=
      summable_norm_weierstrassFactor_sub_one ha hs z
    have hnz := tprod_one_add_ne_zero_of_summable hne hsum
    have hrw : ∀ n : ℕ, 1 + (weierstrassFactor p (z / a n) - 1)
        = weierstrassFactor p (z / a n) := fun n => by ring
    simp only [hrw] at hnz
    exact hnz h
  · rintro ⟨n, rfl⟩
    have hfac : weierstrassFactor p (a n / a n) = 0 := by
      rw [div_self (ha n)]
      exact weierstrassFactor_one p
    exact (hasProd_zero_of_eq_zero (f := fun k => weierstrassFactor p (a n / a k)) hfac).tprod_eq

end Complex
