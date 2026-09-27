import Mathlib.Tactic

/-!
# Massive-vector state-sum algebra

This file records the exact scalar algebra behind the four-dimensional massive-vector
representation of the nonzero-`mu` generalized-unitarity state sum.  It deliberately
formalizes only the invariant polynomial identities; the tree-amplitude normalization
and propagator sewing remain separate analytic input.
-/

namespace GppMassiveVectorStateSum

/-- The spin-one `Sym^2` little-group contraction reduces to the invariant polynomial
`(s - 2 μ²)² - μ⁴ = s² - 4 s μ² + 3 μ⁴`. -/
theorem sym2_s_channel_polynomial (s μ : ℝ) :
    (s - 2 * μ ^ 2) ^ 2 - μ ^ 4 =
      s ^ 2 - 4 * s * μ ^ 2 + 3 * μ ^ 4 := by
  ring

/-- The invariant polynomial factors into the two physical quadratic thresholds. -/
theorem sym2_s_channel_factorization (s μ : ℝ) :
    s ^ 2 - 4 * s * μ ^ 2 + 3 * μ ^ 4 =
      (s - μ ^ 2) * (s - 3 * μ ^ 2) := by
  ring

/-- At two-particle threshold `s = 4 μ²`, the massive-vector state sum reduces to
three equal polarization weights, namely `3 μ⁴`. -/
theorem sym2_threshold_three_polarizations (μ : ℝ) :
    ((4 * μ ^ 2) - 2 * μ ^ 2) ^ 2 - μ ^ 4 = 3 * μ ^ 4 := by
  ring

/-- In the physical two-particle region `s ≥ 4 μ²`, the spin-one state-sum
polynomial is bounded below by its threshold value `3 μ⁴`. -/
theorem sym2_physical_region_ge_threshold
    {s μ : ℝ} (hs : 4 * μ ^ 2 ≤ s) :
    3 * μ ^ 4 ≤ s ^ 2 - 4 * s * μ ^ 2 + 3 * μ ^ 4 := by
  have hs0 : 0 ≤ s := le_trans (by positivity : 0 ≤ 4 * μ ^ 2) hs
  have hgap : 0 ≤ s - 4 * μ ^ 2 := sub_nonneg.mpr hs
  nlinarith [mul_nonneg hs0 hgap]

/-- Consequently the spin-one state-sum polynomial itself is nonnegative
throughout the physical two-particle region. -/
theorem sym2_physical_region_nonneg
    {s μ : ℝ} (hs : 4 * μ ^ 2 ≤ s) :
    0 ≤ s ^ 2 - 4 * s * μ ^ 2 + 3 * μ ^ 4 := by
  have hμ : 0 ≤ 3 * μ ^ 4 := by positivity
  exact le_trans hμ (sym2_physical_region_ge_threshold hs)

/-- Algebraic equivalence of the two dimensional-reconstruction parameterizations.
If `C_V = C_4 + C_S`, then
`C_V + (D_s-5) C_S = C_4 + (D_s-4) C_S`. -/
theorem dimensional_reconstruction_equiv
    (Ds C4 CS CV : ℝ) (hV : CV = C4 + CS) :
    CV + (Ds - 5) * CS = C4 + (Ds - 4) * CS := by
  rw [hV]
  ring

/-- The `D_s=4` baseline is massive-vector minus one real scalar state. -/
theorem ds4_baseline_from_vector_minus_scalar
    (C4 CS CV : ℝ) (hV : CV = C4 + CS) :
    C4 = CV - CS := by
  rw [hV]
  ring

/-- Formal HV specialization of the reconstruction law. -/
theorem hv_specialization
    (ε C4 CS CV : ℝ) (hV : CV = C4 + CS) :
    CV + ((4 - 2 * ε) - 5) * CS = C4 - 2 * ε * CS := by
  rw [hV]
  ring

end GppMassiveVectorStateSum

#print axioms GppMassiveVectorStateSum.sym2_s_channel_polynomial
#print axioms GppMassiveVectorStateSum.sym2_s_channel_factorization
#print axioms GppMassiveVectorStateSum.sym2_threshold_three_polarizations
#print axioms GppMassiveVectorStateSum.sym2_physical_region_ge_threshold
#print axioms GppMassiveVectorStateSum.sym2_physical_region_nonneg
#print axioms GppMassiveVectorStateSum.dimensional_reconstruction_equiv
#print axioms GppMassiveVectorStateSum.ds4_baseline_from_vector_minus_scalar
#print axioms GppMassiveVectorStateSum.hv_specialization
