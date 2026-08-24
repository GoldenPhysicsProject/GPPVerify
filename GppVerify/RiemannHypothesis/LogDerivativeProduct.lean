import GppVerify.RiemannHypothesis.FiniteCompletedFactorNonvanishing
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Product completion has additive logarithmic derivative

At the local-factor level Tate completion is multiplicative.  The logarithmic derivative
linearizes that product: there is no extra bilinear "cross term" at this stage.  Any
prime--Archimedean interference appearing in a squared Dirac/operator model therefore
comes from the operator realization of the additive logarithmic derivative, not from an
ordinary finite product of local scalar factors.

No RH claim is made here.
-/

namespace GppLogDerivativeProduct

/-- Pure scalar identity underlying logarithmic differentiation of a product. -/
theorem neg_logDeriv_mul_algebra (f fp g gp : ℂ) (hf : f ≠ 0) (hg : g ≠ 0) :
    -(fp * g + f * gp) / (f * g) = (-fp / f) + (-gp / g) := by
  field_simp
  ring

/-- Genuine derivative form: if `f` and `g` are differentiable with nonzero values at `s`,
then the negative logarithmic derivative of their product is the sum of the two negative
logarithmic derivatives. -/
theorem neg_logDeriv_product_of_hasDerivAt
    (f g : ℂ → ℂ) (fp gp s : ℂ)
    (hfder : HasDerivAt f fp s) (hgder : HasDerivAt g gp s)
    (hf : f s ≠ 0) (hg : g s ≠ 0) :
    -((fp * g s + f s * gp) / (f s * g s)) =
      -(fp / f s) - (gp / g s) := by
  field_simp
  ring

/-- The derivative of the scalar completed product itself has the usual Leibniz form. -/
theorem hasDerivAt_completed_product
    (f g : ℂ → ℂ) (fp gp s : ℂ)
    (hfder : HasDerivAt f fp s) (hgder : HasDerivAt g gp s) :
    HasDerivAt (fun z => f z * g z) (fp * g s + f s * gp) s := by
  simpa [add_comm] using hfder.mul hgder

end GppLogDerivativeProduct

#print axioms GppLogDerivativeProduct.neg_logDeriv_mul_algebra
#print axioms GppLogDerivativeProduct.neg_logDeriv_product_of_hasDerivAt
#print axioms GppLogDerivativeProduct.hasDerivAt_completed_product
