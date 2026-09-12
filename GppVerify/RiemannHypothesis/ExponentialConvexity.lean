import GppVerify.RiemannHypothesis.SemigroupPositiveDefinite

/-!
# Semigroup positive-definiteness does NOT imply complete monotonicity

This file corrects an overclaim made in `SemigroupPositiveDefinite`. That file observed,
correctly, that the heat semigroup turns Weil positivity into positive-definiteness of
`K` on the additive semigroup `(0,∞)`, and proved that a Laplace transform has that property.
It then asserted that the only remaining gap was the converse, "Hausdorff-Bernstein-Widder".

**That converse is false**, and this file proves it false.

`exp` is a counterexample. Its Gram form is a perfect square,

  `∑ᵢⱼ cᵢcⱼ exp(tᵢ + tⱼ) = (∑ᵢ cᵢ exp tᵢ)² ≥ 0`,

so `exp` is semigroup positive-definite. But `(-1)¹ · exp'(1) = -e < 0`, so `exp` is not
completely monotone.

## What the correct statement is

Semigroup positive-definiteness is *exponential convexity*. Its representation theorem
(Widder) gives

  `K(t) = ∫_ℝ exp(-λt) dμ(λ)`,   μ ≥ 0 on **all of ℝ**,

whereas complete monotonicity is equivalent to the same formula with μ supported on
**[0,∞)**. The two differ exactly by where the measure lives, and `exp` is the witness: it is
the transform of a point mass at `λ = -1`.

So the chain from Weil positivity to the heat-trace criterion needs **two** inputs, not one:

  (a) Widder's representation for exponentially convex functions, and
  (b) a support condition forcing μ onto `[0,∞)` — equivalently boundedness or monotonicity
      of `K` on `(0,∞)`.

On the arithmetic side (b) is a genuine analytic statement about the explicit formula, not a
formality. Recording it as one theorem called "HBW" hid a real hypothesis. That is the exact
failure mode the honesty gates exist to catch, and it was caught here by trying to prove the
claim rather than by inspecting it.

The direction that IS true and IS proved remains `semigroupPosDef_laplace`: every Laplace
transform of a positive measure on `[0,∞)` is semigroup positive-definite. Necessary, not
sufficient.
-/

namespace GppHeatTrace

open MeasureTheory Finset

/-- `exp` is positive-definite on the additive semigroup: its Gram form is a perfect square. -/
theorem semigroupPosDef_exp : SemigroupPosDef (fun t => Real.exp t) := by
  intro n t _ c
  have key : ∑ i, ∑ j, c i * c j * Real.exp (t i + t j)
      = (∑ i, c i * Real.exp (t i)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.exp_add]; ring
  rw [key]
  exact sq_nonneg _

/-- `exp` is not completely monotone: the first derivative already has the wrong sign. -/
theorem not_completelyMonotone_exp : ¬ CompletelyMonotone (fun t => Real.exp t) := by
  intro h
  have h1 := h 1 1 one_pos
  rw [iteratedDeriv_one] at h1
  simp only [Real.deriv_exp, pow_one] at h1
  nlinarith [Real.exp_pos (1 : ℝ)]

/-- **The separation.** Semigroup positive-definiteness does not imply complete monotonicity.
    This refutes the converse asserted in `SemigroupPositiveDefinite`'s module docstring. -/
theorem semigroupPosDef_not_imp_completelyMonotone :
    ¬ (∀ K : ℝ → ℝ, SemigroupPosDef K → CompletelyMonotone K) := by
  intro h
  exact not_completelyMonotone_exp (h _ semigroupPosDef_exp)

end GppHeatTrace
