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

/-- The derivative of the scalar completed product itself has the usual Leibniz form. -/
theorem hasDerivAt_completed_product
    (f g : ℂ → ℂ) (fp gp s : ℂ)
    (hfder : HasDerivAt f fp s) (hgder : HasDerivAt g gp s) :
    HasDerivAt (fun z => f z * g z) (fp * g s + f s * gp) s := by
  -- Mathlib 4.33: the derivative values already match exactly, so `add_comm` is not needed
  -- — and `simpa` actively hurts, rewriting the hypothesis onto
  -- `instCommCStarAlgebraComplex.toCStarAlgebra.toAddCommGroup` while the goal wants
  -- `Complex.addCommGroup`. `exact` absorbs both the Pi-lifting and the instance path.
  exact hfder.mul hgder

/-- Genuine derivative form: if `f` and `g` are differentiable with nonzero values at `s`,
then the negative logarithmic derivative of their product is the sum of the two negative
logarithmic derivatives.

**Made genuine, 2026-09-02.** The statement previously read

    -((fp * g s + f s * gp) / (f s * g s)) = -(fp / f s) - (gp / g s)

with `hfder` and `hgder` in the signature and *neither used in the proof* — the Leibniz
numerator was written out by hand, so this was `neg_logDeriv_mul_algebra` above with two
decorative hypotheses attached, sitting directly beneath the honest version of itself while
its docstring called it the "genuine derivative form". The compiler's unused-binder warning
is what caught it; the docstring did not.

The fix is not to strip the name down to what the statement was, but to make the statement
match the name: the left side is now `deriv (fun z => f z * g z) s`, and `hfder`/`hgder` are
what identify that derivative (via `hasDerivAt_completed_product` below). All four
hypotheses are now load-bearing. -/
theorem neg_logDeriv_product_of_hasDerivAt
    (f g : ℂ → ℂ) (fp gp s : ℂ)
    (hfder : HasDerivAt f fp s) (hgder : HasDerivAt g gp s)
    (hf : f s ≠ 0) (hg : g s ≠ 0) :
    -(deriv (fun z => f z * g z) s / (f s * g s)) =
      -(fp / f s) - (gp / g s) := by
  rw [(hasDerivAt_completed_product f g fp gp s hfder hgder).deriv]
  field_simp
  ring

end GppLogDerivativeProduct

#print axioms GppLogDerivativeProduct.neg_logDeriv_mul_algebra
#print axioms GppLogDerivativeProduct.neg_logDeriv_product_of_hasDerivAt
#print axioms GppLogDerivativeProduct.hasDerivAt_completed_product
