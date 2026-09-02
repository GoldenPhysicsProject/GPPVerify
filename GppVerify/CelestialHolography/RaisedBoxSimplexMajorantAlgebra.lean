import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Pointwise majorant algebra for the raised-box simplex limit

In the Euclidean four-point chamber the massless box Symanzik polynomial has the
form

  Q = A*x1*x3 + B*x2*x4,  A>0, B>=0.

For a fixed `0 < delta < 1` and `0 <= eps <= delta`, dominated convergence can use
one channel monomial only:

  Q^(-eps) <= 1 + (A*x1*x3)^(-delta).

The measure-theoretic statement that the right-hand side is integrable on the
3-simplex is a separate Dirichlet/Beta-integral layer.  This file proves the exact
pointwise real-power inequalities.
-/

namespace GppRaisedBoxSimplexMajorantAlgebra

/-- For a positive base and `0 <= eps <= delta`, the negative power at `eps` is
bounded by `1 + q^(-delta)`. -/
theorem rpow_neg_eps_le_one_add_rpow_neg_delta
    {q ε δ : ℝ} (hq : 0 < q) (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ) :
    q ^ (-ε) ≤ 1 + q ^ (-δ) := by
  by_cases hq1 : q ≤ 1
  · have hpow : q ^ (-ε) ≤ q ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith)
    linarith [Real.rpow_nonneg hq.le (-δ)]
  · have h1q : 1 ≤ q := le_of_lt (lt_of_not_ge hq1)
    have hpow : q ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1q (neg_nonpos.mpr hε0)
    linarith [Real.rpow_nonneg hq.le (-δ)]

/-- A positive channel monomial lower-bounds the Euclidean Symanzik polynomial. -/
theorem channel_monomial_le_symanzik
    {A B x1 x2 x3 x4 : ℝ}
    (hB : 0 ≤ B) (hx2 : 0 ≤ x2) (hx4 : 0 ≤ x4) :
    A * x1 * x3 ≤ A * x1 * x3 + B * x2 * x4 := by
  have : 0 ≤ B * x2 * x4 := by positivity
  linarith

/-- For negative exponent, the Symanzik lower bound reverses after taking the real
power. -/
theorem symanzik_neg_rpow_le_channel
    {A B x1 x2 x3 x4 δ : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx3 : 0 < x3) (hx4 : 0 ≤ x4)
    (hδ : 0 < δ) :
    (A * x1 * x3 + B * x2 * x4) ^ (-δ) ≤
      (A * x1 * x3) ^ (-δ) := by
  have hm : 0 < A * x1 * x3 := by positivity
  have hmq : A * x1 * x3 ≤ A * x1 * x3 + B * x2 * x4 :=
    channel_monomial_le_symanzik hB hx2 hx4
  have hQ : 0 < A * x1 * x3 + B * x2 * x4 := lt_of_lt_of_le hm hmq
  exact (Real.rpow_le_rpow_iff_of_neg hQ hm (by linarith)).2 hmq

/-- **One-channel raised-box majorant.** This is the pointwise inequality needed
for the simplex dominated-convergence proof. -/
theorem symanzik_neg_eps_majorized
    {A B x1 x2 x3 x4 ε δ : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx3 : 0 < x3) (hx4 : 0 ≤ x4)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ) (hδ : 0 < δ) :
    (A * x1 * x3 + B * x2 * x4) ^ (-ε) ≤
      1 + (A * x1 * x3) ^ (-δ) := by
  have hm : 0 < A * x1 * x3 := by positivity
  have hmq : A * x1 * x3 ≤ A * x1 * x3 + B * x2 * x4 :=
    channel_monomial_le_symanzik hB hx2 hx4
  have hQ : 0 < A * x1 * x3 + B * x2 * x4 := lt_of_lt_of_le hm hmq
  have h1 := rpow_neg_eps_le_one_add_rpow_neg_delta hQ hε0 hεδ
  have h2 := symanzik_neg_rpow_le_channel hA hB hx1 hx2 hx3 hx4 hδ
  linarith

end GppRaisedBoxSimplexMajorantAlgebra

#print axioms GppRaisedBoxSimplexMajorantAlgebra.rpow_neg_eps_le_one_add_rpow_neg_delta
#print axioms GppRaisedBoxSimplexMajorantAlgebra.symanzik_neg_rpow_le_channel
#print axioms GppRaisedBoxSimplexMajorantAlgebra.symanzik_neg_eps_majorized
