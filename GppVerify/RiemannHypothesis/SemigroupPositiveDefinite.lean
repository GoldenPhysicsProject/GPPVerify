import GppVerify.RiemannHypothesis.BernsteinEasy

/-!
# Positive-definiteness on the additive semigroup (0,∞), and why it removes Bochner

The bridge from Weil positivity to the heat-trace criterion was written in `BernsteinEasy` as

  W positive-type => W = Fourier transform of a positive measure ν   [Bochner]
  => K(t) = ∫ exp(-λt) dμ(λ) => K completely monotone.

Bochner's theorem is not in Mathlib and is a large formalisation. **It is also avoidable.**

The heat kernel is a convolution SEMIGROUP: `heat_s * heat_t = heat_{s+t}`. Therefore

  K(t_i + t_j) = <W, heat_{t_i} * heat_{t_j}>,

so the Gram matrix `[K(t_i + t_j)]` is exactly the Weil form evaluated on the finite family
`{heat_{t_i}}`. Weil positivity — nonnegativity on convolution squares — gives that matrix
positive semi-definite DIRECTLY, with no Fourier representation and no Bochner.

That identifies the correct intermediate object. It is not "W is a Fourier transform of a
positive measure", it is:

  **K is positive-definite on the additive semigroup (0,∞).**

This file defines that notion and proves the direction that is available now: a Laplace
transform is semigroup-positive-definite, because `K(s+t) = ∫ e^{-λs} e^{-λt} dμ` exhibits the
Gram matrix as the Gram matrix of the vectors `λ ↦ e^{-λ t_i}` in `L²(μ)`.

**The converse is FALSE**, and `ExponentialConvexity.semigroupPosDef_not_imp_completelyMonotone`
proves it false: `exp` is semigroup positive-definite (its Gram form is a perfect square) and is
not completely monotone. An earlier version of this docstring asserted that converse as
"Hausdorff-Bernstein-Widder" and called it the single remaining gap. That was wrong.

Semigroup positive-definiteness is *exponential convexity*, whose representation theorem puts
the measure on all of `ℝ`; complete monotonicity is the same formula with the measure supported
on `[0,∞)`. The chain therefore needs TWO inputs: Widder's representation, and a support
condition forcing the measure onto `[0,∞)` — equivalently boundedness of `K` on `(0,∞)`. See
`ExponentialConvexity` for the correction.
-/

namespace GppHeatTrace

open MeasureTheory Finset

variable {μ : Measure ℝ}

/-- **Positive-definiteness on the additive semigroup `(0,∞)`**: every Gram matrix
    `[K (t i + t j)]` built from positive parameters is positive semi-definite. -/
def SemigroupPosDef (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ), (∀ i, 0 < t i) → ∀ c : Fin n → ℝ,
    0 ≤ ∑ i, ∑ j, c i * c j * K (t i + t j)

/-- The exponential splits across the semigroup law. -/
theorem laplace_add (μ : Measure ℝ) (s t : ℝ) :
    laplace μ (s + t) = ∫ l, Real.exp (-l * s) * Real.exp (-l * t) ∂μ := by
  rw [laplace]
  refine integral_congr_ae ?_
  filter_upwards with l
  rw [← Real.exp_add]
  ring_nf

/-- **A Laplace transform is positive-definite on `(0,∞)`.** The Gram matrix is the Gram
    matrix of the vectors `λ ↦ e^{-λ t_i}` in `L²(μ)`, so it is PSD for the same reason any
    Gram matrix is: the quadratic form is the integral of a square. -/
theorem semigroupPosDef_laplace (h : LaplaceMoments μ) : SemigroupPosDef (laplace μ) := by
  intro n t ht c
  have hint : ∀ i j : Fin n, Integrable
      (fun l => c i * c j * (Real.exp (-l * t i) * Real.exp (-l * t j))) μ := by
    intro i j
    have h0 := h.integrable 0 (show (0:ℝ) < t i + t j by have := ht i; have := ht j; linarith)
    simp only [pow_zero, one_mul] at h0
    refine ((h0.const_mul (c i * c j)).congr ?_)
    filter_upwards with l
    rw [← Real.exp_add]
    ring_nf
  have key : ∑ i, ∑ j, c i * c j * laplace μ (t i + t j)
      = ∫ l, (∑ i, c i * Real.exp (-l * t i)) ^ 2 ∂μ := by
    have step : ∀ i j : Fin n, c i * c j * laplace μ (t i + t j)
        = ∫ l, c i * c j * (Real.exp (-l * t i) * Real.exp (-l * t j)) ∂μ := by
      intro i j
      rw [laplace_add, integral_const_mul]
    have inner : ∀ i : Fin n,
        (∑ j, ∫ l, c i * c j * (Real.exp (-l * t i) * Real.exp (-l * t j)) ∂μ)
          = ∫ l, ∑ j, c i * c j * (Real.exp (-l * t i) * Real.exp (-l * t j)) ∂μ := by
      intro i
      rw [integral_finsetSum _ (fun j _ => hint i j)]
    simp only [step, inner]
    rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    refine integral_congr_ae ?_
    filter_upwards with l
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  exact integral_nonneg fun l => sq_nonneg _

end GppHeatTrace
