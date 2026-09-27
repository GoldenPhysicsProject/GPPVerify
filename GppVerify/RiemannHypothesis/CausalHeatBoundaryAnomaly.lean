import GppVerify.RiemannHypothesis.HeatTraceCriterion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Causal Dirichlet-heat boundary anomaly: scalar core

The causal replacement in the arithmetic heat-trace program uses the Dirichlet heat kernel
on the positive half-line and the unilateral translation by `a > 0`. On the diagonal, the
commutator kernel has the two pieces

  g(a) - g(a + 2x),             0 < x < a,
  g(2x - a) - g(2x + a),       x >= a,

where for the heat problem `g = g_t` is the normalized Gaussian.

For a continuous kernel, finite-interval integrability justifies the affine substitutions and
additivity steps, giving exactly

  T_R(a) = a g(a) - (1/2) integral_[2R-a,2R+a] g.

If in addition `g(x) -> 0` as `x -> +infinity`, the moving window has fixed width `2a` and
vanishes. The normalized heat Gaussian is continuous and has this decay for every `t > 0`, so
the scalar anomaly is exactly

  lim_R T_R(a) = a / sqrt(4*pi*t) * exp(-a^2/(4t)).

This file does not yet package the Dirichlet heat operators or prove trace-classness of their
commutator. It closes the scalar diagonal-integral part of that operator theorem.
-/

namespace intervalIntegral

/-- Real-valued multiplicative specialization of the current Lean 4.19 affine
interval-integral substitution theorem. -/
@[simp] theorem mul_integral_comp_add_mul_real
    (f : ℝ → ℝ) (c d : ℝ) {a b : ℝ} :
    c * (∫ x in a..b, f (d + c * x)) =
      ∫ x in d + c * a..d + c * b, f x := by
  simpa [smul_eq_mul] using
    (smul_integral_comp_add_mul f c d (a := a) (b := b))

/-- Real-valued multiplicative specialization for `f (c*x-d)`. -/
@[simp] theorem mul_integral_comp_mul_sub_real
    (f : ℝ → ℝ) (c d : ℝ) {a b : ℝ} :
    c * (∫ x in a..b, f (c * x - d)) =
      ∫ x in c * a - d..c * b - d, f x := by
  simpa [smul_eq_mul] using
    (smul_integral_comp_mul_sub f c d (a := a) (b := b))

/-- Real-valued multiplicative specialization for `f (c*x+d)`. -/
@[simp] theorem mul_integral_comp_mul_add_real
    (f : ℝ → ℝ) (c d : ℝ) {a b : ℝ} :
    c * (∫ x in a..b, f (c * x + d)) =
      ∫ x in c * a + d..c * b + d, f x := by
  simpa [smul_eq_mul] using
    (smul_integral_comp_mul_add f c d (a := a) (b := b))

end intervalIntegral

namespace GppCausalHeatBoundaryAnomaly

open Filter Set intervalIntegral
open scoped Interval

/-- The normalized one-dimensional heat Gaussian. -/
noncomputable def heatKernelGaussian (t x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (4 * t)) / Real.sqrt (4 * Real.pi * t)

/-- Finite-cutoff diagonal integral of the causal heat/translation commutator. -/
noncomputable def truncatedBoundaryTrace (g : ℝ → ℝ) (a R : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..a, (g a - g (a + 2 * x))) +
    ∫ x in a..R, (g (2 * x - a) - g (2 * x + a))

/-- Affine substitution for the boundary piece `g(a+2x)`. -/
theorem two_mul_integral_zero_a_add_two
    (g : ℝ → ℝ) (a : ℝ) :
    2 * (∫ x in (0 : ℝ)..a, g (a + 2 * x)) = ∫ y in a..(3 * a), g y := by
  have h := intervalIntegral.mul_integral_comp_add_mul_real g 2 a
    (a := (0 : ℝ)) (b := a)
  convert h using 1 <;> ring

/-- Affine substitution for `g(2x-a)` on the bulk interval. -/
theorem two_mul_integral_a_R_two_sub
    (g : ℝ → ℝ) (a R : ℝ) :
    2 * (∫ x in a..R, g (2 * x - a)) =
      ∫ y in a..(2 * R - a), g y := by
  have h := intervalIntegral.mul_integral_comp_mul_sub_real g 2 a (a := a) (b := R)
  convert h using 1 <;> ring

/-- Affine substitution for `g(2x+a)` on the bulk interval. -/
theorem two_mul_integral_a_R_two_add
    (g : ℝ → ℝ) (a R : ℝ) :
    2 * (∫ x in a..R, g (2 * x + a)) =
      ∫ y in (3 * a)..(2 * R + a), g y := by
  have h := intervalIntegral.mul_integral_comp_mul_add_real g 2 a (a := a) (b := R)
  convert h using 1 <;> ring

/-- **Exact finite-cutoff boundary cancellation.** Continuity supplies the finite-interval
integrability needed by subtraction and adjacent-interval additivity. The only remainder is a
moving window of the underlying kernel at the far endpoint. -/
theorem truncatedBoundaryTrace_eq_boundary_minus_tail
    (g : ℝ → ℝ) (hgc : Continuous g) (a R : ℝ) :
    truncatedBoundaryTrace g a R =
      a * g a - (1 / 2 : ℝ) * (∫ y in (2 * R - a)..(2 * R + a), g y) := by
  unfold truncatedBoundaryTrace
  have hga : Continuous (fun x : ℝ => g (a + 2 * x)) := by fun_prop
  have hgm : Continuous (fun x : ℝ => g (2 * x - a)) := by fun_prop
  have hgp : Continuous (fun x : ℝ => g (2 * x + a)) := by fun_prop
  have hc0 : IntervalIntegrable (fun _x : ℝ => g a) MeasureTheory.volume (0 : ℝ) a :=
    continuous_const.intervalIntegrable (0 : ℝ) a
  have hga0 : IntervalIntegrable (fun x : ℝ => g (a + 2 * x)) MeasureTheory.volume (0 : ℝ) a :=
    hga.intervalIntegrable (0 : ℝ) a
  have hgmaR : IntervalIntegrable (fun x : ℝ => g (2 * x - a)) MeasureTheory.volume a R :=
    hgm.intervalIntegrable a R
  have hgpaR : IntervalIntegrable (fun x : ℝ => g (2 * x + a)) MeasureTheory.volume a R :=
    hgp.intervalIntegrable a R
  rw [integral_sub hc0 hga0, integral_sub hgmaR hgpaR]
  have hconst : (∫ _x in (0 : ℝ)..a, g a) = a * g a := by
    simp [intervalIntegral.integral_const]
  rw [hconst]
  have h1 := two_mul_integral_zero_a_add_two g a
  have h2 := two_mul_integral_a_R_two_sub g a R
  have h3 := two_mul_integral_a_R_two_add g a R
  have hadd1 :
      (∫ y in a..(3 * a), g y) + (∫ y in (3 * a)..(2 * R + a), g y) =
        ∫ y in a..(2 * R + a), g y := by
    exact integral_add_adjacent_intervals
      (hgc.intervalIntegrable a (3 * a))
      (hgc.intervalIntegrable (3 * a) (2 * R + a))
  have hadd2 :
      (∫ y in a..(2 * R - a), g y) +
        (∫ y in (2 * R - a)..(2 * R + a), g y) =
        ∫ y in a..(2 * R + a), g y := by
    exact integral_add_adjacent_intervals
      (hgc.intervalIntegrable a (2 * R - a))
      (hgc.intervalIntegrable (2 * R - a) (2 * R + a))
  have htail :
      (∫ y in a..(2 * R - a), g y) -
          (∫ y in a..(3 * a), g y) -
          (∫ y in (3 * a)..(2 * R + a), g y) =
        -(∫ y in (2 * R - a)..(2 * R + a), g y) := by
    linarith [hadd1, hadd2]
  linarith [h1, h2, h3, htail]

/-- **Fixed-width moving windows vanish for continuous kernels decaying at `+infinity`.** -/
theorem movingWindowIntegral_tendsto_zero
    {g : ℝ → ℝ} (_hgc : Continuous g) (hg : Tendsto g atTop (nhds 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ y in (2 * R - a)..(2 * R + a), g y) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := ε / (4 * a)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hev : ∀ᶠ y : ℝ in atTop, dist (g y) 0 < C :=
    hg.eventually (Metric.ball_mem_nhds 0 hC)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine Filter.eventually_atTop.2 ⟨(N + a) / 2, ?_⟩
  intro R hR
  have hlow : N ≤ 2 * R - a := by linarith
  have hle : 2 * R - a ≤ 2 * R + a := by linarith
  have hpt : ∀ y ∈ Ι (2 * R - a) (2 * R + a), ‖g y‖ ≤ C := by
    intro y hy
    rw [uIoc_of_le hle] at hy
    have hNy : N ≤ y := le_trans hlow (le_of_lt hy.1)
    have hyC : dist (g y) 0 < C := hN y hNy
    simpa [Real.dist_eq, Real.norm_eq_abs] using le_of_lt hyC
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hwidth : |(2 * R + a) - (2 * R - a)| = 2 * a := by
    rw [show (2 * R + a) - (2 * R - a) = 2 * a by ring,
      abs_of_pos (mul_pos (by norm_num) ha)]
  rw [hwidth] at hbound
  have hcalc : C * (2 * a) = ε / 2 := by
    dsimp [C]
    field_simp [ha.ne']
    ring
  rw [hcalc] at hbound
  have hlt : ‖∫ y in (2 * R - a)..(2 * R + a), g y‖ < ε := by
    linarith
  simpa [dist_zero_right] using hlt

/-- **Generic scalar boundary anomaly limit.** For a continuous kernel decaying at positive
infinity, the finite-cutoff diagonal trace converges to the boundary value `a*g(a)`. -/
theorem truncatedBoundaryTrace_tendsto_boundary
    {g : ℝ → ℝ} (hgc : Continuous g) (hg : Tendsto g atTop (nhds 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => truncatedBoundaryTrace g a R) atTop (nhds (a * g a)) := by
  have htail := movingWindowIntegral_tendsto_zero hgc hg ha
  have hhalf :
      Tendsto
        (fun R : ℝ => (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), g y))
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul htail)
  have hmain :
      Tendsto
        (fun R : ℝ => a * g a - (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), g y))
        atTop (nhds (a * g a)) := by
    simpa using (tendsto_const_nhds.sub hhalf)
  have heq :
      (fun R : ℝ => truncatedBoundaryTrace g a R) =
        (fun R : ℝ => a * g a - (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), g y)) := by
    funext R
    exact truncatedBoundaryTrace_eq_boundary_minus_tail g hgc a R
  rw [heq]
  exact hmain

/-- The normalized Gaussian is continuous for every fixed heat parameter. -/
theorem heatKernelGaussian_continuous (t : ℝ) : Continuous (heatKernelGaussian t) := by
  unfold heatKernelGaussian
  fun_prop

/-- For every positive heat time, the normalized Gaussian decays at positive infinity. -/
theorem heatKernelGaussian_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (heatKernelGaussian t) atTop (nhds 0) := by
  have hden : 0 < 4 * t := by positivity
  have harg : Tendsto (fun x : ℝ => x ^ 2 / (4 * t)) atTop atTop := by
    have hev : ∀ᶠ x : ℝ in atTop, x ≤ x ^ 2 / (4 * t) := by
      filter_upwards [eventually_ge_atTop (max 0 (4 * t))] with x hx
      have hx0 : 0 ≤ x := (le_max_left 0 (4 * t)).trans hx
      have hxt : 4 * t ≤ x := (le_max_right 0 (4 * t)).trans hx
      rw [le_div_iff₀ hden]
      nlinarith
    exact tendsto_atTop_mono' atTop hev tendsto_id
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (-(x ^ 2 / (4 * t)))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp harg
  change Tendsto
    (fun x : ℝ => Real.exp (-(x ^ 2) / (4 * t)) /
      Real.sqrt (4 * Real.pi * t)) atTop (nhds 0)
  have hfun :
      (fun x : ℝ => Real.exp (-(x ^ 2) / (4 * t)) /
        Real.sqrt (4 * Real.pi * t)) =
      (fun x : ℝ => Real.exp (-(x ^ 2 / (4 * t))) /
        Real.sqrt (4 * Real.pi * t)) := by
    funext x
    have hexponent : -(x ^ 2) / (4 * t) = -(x ^ 2 / (4 * t)) := by ring
    rw [hexponent]
  rw [hfun]
  simpa using (hexp.div_const (Real.sqrt (4 * Real.pi * t)))

/-- Specialization of the finite-cutoff identity to the normalized heat Gaussian. -/
theorem truncatedHeatBoundaryTrace_eq
    (t a R : ℝ) :
    truncatedBoundaryTrace (heatKernelGaussian t) a R =
      a * heatKernelGaussian t a -
        (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), heatKernelGaussian t y) := by
  exact truncatedBoundaryTrace_eq_boundary_minus_tail
    (heatKernelGaussian t) (heatKernelGaussian_continuous t) a R

/-- **Exact scalar causal heat-boundary anomaly.** -/
theorem truncatedHeatBoundaryTrace_tendsto
    {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    Tendsto (fun R : ℝ => truncatedBoundaryTrace (heatKernelGaussian t) a R)
      atTop
      (nhds (a / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t)))) := by
  have h := truncatedBoundaryTrace_tendsto_boundary
    (heatKernelGaussian_continuous t) (heatKernelGaussian_tendsto_zero ht) ha
  convert h using 1
  unfold heatKernelGaussian
  ring

end GppCausalHeatBoundaryAnomaly

#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_zero_a_add_two
#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_a_R_two_sub
#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_a_R_two_add
#print axioms GppCausalHeatBoundaryAnomaly.truncatedBoundaryTrace_eq_boundary_minus_tail
#print axioms GppCausalHeatBoundaryAnomaly.movingWindowIntegral_tendsto_zero
#print axioms GppCausalHeatBoundaryAnomaly.truncatedBoundaryTrace_tendsto_boundary
#print axioms GppCausalHeatBoundaryAnomaly.heatKernelGaussian_continuous
#print axioms GppCausalHeatBoundaryAnomaly.heatKernelGaussian_tendsto_zero
#print axioms GppCausalHeatBoundaryAnomaly.truncatedHeatBoundaryTrace_tendsto