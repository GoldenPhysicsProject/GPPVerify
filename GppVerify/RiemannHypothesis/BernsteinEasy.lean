import GppVerify.RiemannHypothesis.HeatTraceModeSum
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Bernstein's easy direction: a Laplace transform of a positive measure is completely monotone

The converse (completely monotone => Laplace transform of a positive measure) is the
Bernstein-Widder theorem and is NOT in Mathlib. This direction needs only differentiation
under the integral sign, which is, and it is the half the shadow programme actually uses:

  W positive-type  =>  W = Fourier transform of a positive measure ν       [Bochner]
  K(t) = <W, gaussian_t>/sqrt(4 pi t) = ∫ exp(-λ t) dμ(λ), μ ≥ 0           [gaussian self-dual]
  => K completely monotone                                                 [THIS FILE]

Combined with `arithmetic_principal_series_RH_program`'s `RH <=> K completely monotone`, this
is the bridge making Weil positivity and the heat-trace criterion the same condition rather
than two parallel criteria.

The analytic input is named, not hidden. `LaplaceMoments` asks that `μ` sit on `[0,∞)` and that
every exponentially damped moment converge on `(0,∞)`. On the spectral side that is exactly the
trace-class condition, and it is carried as a hypothesis visible in the type.

`HeatTraceModeSum.completelyMonotone_heatTrace` is the finite/atomic case of this theorem; this
file is the measure-level statement it was a shadow of.
-/

namespace GppHeatTrace

open MeasureTheory Set Filter
open scoped Topology

variable {μ : Measure ℝ}

/-- The analytic input, named. -/
structure LaplaceMoments (μ : Measure ℝ) : Prop where
  nonneg : ∀ᵐ l ∂μ, 0 ≤ l
  integrable : ∀ (n : ℕ) {t : ℝ}, 0 < t → Integrable (fun l => l ^ n * Real.exp (-l * t)) μ

/-- The Laplace transform of `μ`. -/
noncomputable def laplace (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ l, Real.exp (-l * t) ∂μ

/-- The `n`-th integrand `(-l)^n exp(-l t)`, integrated. The family is closed under `d/dt`,
    which is what makes the induction below clean. -/
noncomputable def lapInt (μ : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ l, (-l) ^ n * Real.exp (-l * t) ∂μ

theorem lapInt_zero (μ : Measure ℝ) : lapInt μ 0 = laplace μ := by
  funext t; simp [lapInt, laplace]

/-- `|(-l)^(n+1) exp(-l t)| ≤ l^(n+1) exp(-l t₀)` for `l ≥ 0` and `t₀ ≤ t`. -/
theorem lap_bound {n : ℕ} {l t t₀ : ℝ} (hl : 0 ≤ l) (ht : t₀ ≤ t) :
    ‖(-l) ^ (n + 1) * Real.exp (-l * t)‖ ≤ l ^ (n + 1) * Real.exp (-l * t₀) := by
  have habs : ‖(-l) ^ (n + 1) * Real.exp (-l * t)‖ = l ^ (n + 1) * Real.exp (-l * t) := by
    rw [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg hl,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [habs]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hl (sub_nonneg.mpr ht)]))
    (pow_nonneg hl _)

/-- Each integrand differentiates into the next. -/
theorem hasDerivAt_integrand (l : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => (-l) ^ n * Real.exp (-l * x)) ((-l) ^ (n + 1) * Real.exp (-l * t)) t := by
  have h0 : HasDerivAt (fun x : ℝ => -l * x) (-l) t := by
    simpa using (hasDerivAt_id t).const_mul (-l)
  have h2 := (h0.exp).const_mul ((-l) ^ n)
  have heq : (-l) ^ n * (Real.exp (-l * t) * -l) = (-l) ^ (n + 1) * Real.exp (-l * t) := by ring
  rwa [heq] at h2

/-- The signed integrand is integrable wherever the unsigned one is. -/
theorem integrable_integrand (h : LaplaceMoments μ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun l => (-l) ^ n * Real.exp (-l * t)) μ := by
  have hI := (h.integrable n ht).const_mul ((-1 : ℝ) ^ n)
  refine hI.congr ?_
  filter_upwards with l
  rw [neg_pow]; ring

/-- **Differentiation under the integral sign.** -/
theorem hasDerivAt_lapInt (h : LaplaceMoments μ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (lapInt μ n) (lapInt μ (n + 1) t) t := by
  have hhalf : (0 : ℝ) < t / 2 := by linarith
  have hs : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x l =>
      (-l) ^ n * Real.exp (-l * x)) (F' := fun x l => (-l) ^ (n + 1) * Real.exp (-l * x))
      (bound := fun l => l ^ (n + 1) * Real.exp (-l * (t / 2))) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with x hx
    exact (integrable_integrand h n (lt_trans hhalf hx)).aestronglyMeasurable
  · exact integrable_integrand h n ht
  · exact (integrable_integrand h (n + 1) ht).aestronglyMeasurable
  · filter_upwards [h.nonneg] with l hl x hx
    exact lap_bound hl (le_of_lt hx)
  · exact h.integrable (n + 1) hhalf
  · filter_upwards with l x _ using hasDerivAt_integrand l n x

/-- The `n`-th derivative of the Laplace transform is the `n`-th integral, on `(0,∞)`. -/
theorem eqOn_iteratedDeriv_lapInt (h : LaplaceMoments μ) :
    ∀ n : ℕ, EqOn (iteratedDeriv n (laplace μ)) (lapInt μ n) (Ioi 0) := by
  intro n
  induction n with
  | zero => intro t _; simp [lapInt_zero]
  | succ n ih =>
      intro t ht
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv n (laplace μ) =ᶠ[𝓝 t] lapInt μ n :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) ih
      rw [hev.deriv_eq]
      exact (hasDerivAt_lapInt h n ht).deriv

/-- **Bernstein, easy direction.** The Laplace transform of a positive measure on `[0,∞)` is
    completely monotone on `(0,∞)`. -/
theorem completelyMonotone_laplace (h : LaplaceMoments μ) : CompletelyMonotone (laplace μ) := by
  intro n t ht
  rw [eqOn_iteratedDeriv_lapInt h n ht]
  have hrw : (-1 : ℝ) ^ n * lapInt μ n t = ∫ l, l ^ n * Real.exp (-l * t) ∂μ := by
    rw [lapInt, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with l
    have hp : (-1 : ℝ) ^ n * (-l) ^ n = l ^ n := by
      rw [← mul_pow]; congr 1; ring
    calc (-1 : ℝ) ^ n * ((-l) ^ n * Real.exp (-l * t))
        = ((-1 : ℝ) ^ n * (-l) ^ n) * Real.exp (-l * t) := by ring
      _ = l ^ n * Real.exp (-l * t) := by rw [hp]
  rw [hrw]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h.nonneg] with l hl
  positivity

end GppHeatTrace
