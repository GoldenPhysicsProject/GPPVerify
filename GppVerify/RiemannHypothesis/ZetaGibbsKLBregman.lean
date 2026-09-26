import GppVerify.RiemannHypothesis.ZetaGibbsKLOrientationKernel
import Mathlib.Tactic

/-!
# Algebraic Bregman identities for directed Gibbs KL

For a differentiable log-partition function `A`, the directed Gibbs relative
entropy has the one-dimensional Bregman form

`D(β ‖ γ) = A γ - A β - (γ - β) * A' β`.

This file isolates the exact algebraic identities behind the orientation
problem.  No analytic assumption is used here; later files can instantiate
`A = log ζ` and identify `A''` with the genuine Gibbs Fisher metric.
-/

namespace GppZetaGibbsKLBregman

/-- One-dimensional Bregman/Gibbs KL expression with derivative data `dA`. -/
def gibbsKL (A dA : ℝ → ℝ) (β γ : ℝ) : ℝ :=
  A γ - A β - (γ - β) * dA β

/-- Exact antisymmetry formula for directed Gibbs KL. -/
theorem gibbsKL_sub_reverse
    (A dA : ℝ → ℝ) (β γ : ℝ) :
    gibbsKL A dA β γ - gibbsKL A dA γ β =
      2 * (A γ - A β) - (γ - β) * (dA β + dA γ) := by
  unfold gibbsKL
  ring

/-- Exact symmetric sum formula.  For a convex log-partition function this
becomes the standard nonnegative Jeffreys divergence identity. -/
theorem gibbsKL_add_reverse
    (A dA : ℝ → ℝ) (β γ : ℝ) :
    gibbsKL A dA β γ + gibbsKL A dA γ β =
      (γ - β) * (dA γ - dA β) := by
  unfold gibbsKL
  ring

/-- The directed-KL asymmetry is twice the secant-minus-endpoint-trapezoid
defect of the derivative.  This is the exact algebraic target for the
Fisher-metric integral/reflection argument. -/
theorem gibbsKL_asymmetry_trapezoid
    (A dA : ℝ → ℝ) (β γ : ℝ) :
    gibbsKL A dA β γ - gibbsKL A dA γ β =
      2 * ((A γ - A β) - ((γ - β) / 2) * (dA β + dA γ)) := by
  rw [gibbsKL_sub_reverse]
  ring

end GppZetaGibbsKLBregman

#print axioms GppZetaGibbsKLBregman.gibbsKL_sub_reverse
#print axioms GppZetaGibbsKLBregman.gibbsKL_add_reverse
#print axioms GppZetaGibbsKLBregman.gibbsKL_asymmetry_trapezoid
