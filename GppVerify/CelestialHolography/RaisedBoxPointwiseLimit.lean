import GppVerify.CelestialHolography.RaisedBoxSimplexMajorantAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Pointwise regulator limit for the raised-box simplex integrand

The majorant layer already proves an epsilon-uniform domination of the Euclidean
Symanzik integrand on the simplex interior.  The other pointwise ingredient for
dominated convergence is elementary but should be explicit in the formal chain:
for every strictly positive Symanzik value `Q`,

  Q^(-eps) -> 1  as eps -> 0.

This file proves exactly that continuity statement.  The remaining analytic layer
is integrability of the fixed boundary majorant and the measure-theoretic dominated
convergence passage over the 3-simplex.
-/

namespace GppRaisedBoxPointwiseLimit

open Filter
open scoped Topology

/-- A positive constant raised to the vanishing negative regulator tends to one. -/
theorem tendsto_neg_rpow_one {q : ℝ} (hq : 0 < q) :
    Tendsto (fun ε : ℝ => q ^ (-ε)) (𝓝 0) (𝓝 1) := by
  have hcont : Continuous (fun ε : ℝ => q ^ (-ε)) :=
    (Real.continuous_const_rpow hq.ne').comp continuous_neg
  have h :
      Tendsto (fun ε : ℝ => q ^ (-ε)) (𝓝 0) (𝓝 (q ^ (-(0 : ℝ)))) :=
    hcont.continuousAt
  simpa using h

/-- Pointwise convergence of the Euclidean four-point Symanzik integrand on the
simplex interior. -/
theorem symanzik_neg_regulator_tendsto_one
    {A B x1 x2 x3 x4 : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx3 : 0 < x3) (hx4 : 0 ≤ x4) :
    Tendsto
      (fun ε : ℝ => (A * x1 * x3 + B * x2 * x4) ^ (-ε))
      (𝓝 0) (𝓝 1) := by
  have hm : 0 < A * x1 * x3 := by positivity
  have hmq : A * x1 * x3 ≤ A * x1 * x3 + B * x2 * x4 :=
    GppRaisedBoxSimplexMajorantAlgebra.channel_monomial_le_symanzik hB hx2 hx4
  have hQ : 0 < A * x1 * x3 + B * x2 * x4 := lt_of_lt_of_le hm hmq
  exact tendsto_neg_rpow_one hQ

end GppRaisedBoxPointwiseLimit

#print axioms GppRaisedBoxPointwiseLimit.tendsto_neg_rpow_one
#print axioms GppRaisedBoxPointwiseLimit.symanzik_neg_regulator_tendsto_one
