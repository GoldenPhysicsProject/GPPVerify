import Mathlib.Tactic

/-!
# Finite zeta-gauge Gram positivity

The finite arithmetic gauge picture uses an incidence/synthesis matrix `Z`, a nonnegative
length-energy diagonal `d`, and the two quadratic forms

  G = Z^T Z,
  H = Z^T diag(d) Z.

For every vector `x`,

  x^T G x = sum_k (sum_i Z_{k i} x_i)^2 >= 0,
  x^T H x = sum_k d_k (sum_i Z_{k i} x_i)^2 >= 0.

This is the finite algebraic positivity behind the similarity transform
`B = Z^{-1} D Z`: in the `G` metric, the gauged operator has form matrix `H` and is
positive.  The arithmetic specialization takes `Z` to divisor/zeta synthesis and `D` to
logarithmic length.  The difficult RH step is not this finite positivity; it is the
nondegenerate causal completion at the critical half-density after the Archimedean channel
is attached.
-/

namespace GppZetaGaugeGramPositivity

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Synthesis of a finite coefficient vector through an arbitrary real incidence matrix. -/
def synth (Z : κ → ι → ℝ) (x : ι → ℝ) (k : κ) : ℝ :=
  ∑ i, Z k i * x i

/-- Ordinary Gram quadratic form `||Zx||^2`. -/
def gramQuadratic (Z : κ → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ k, (synth Z x k)^2

/-- Energy-weighted Gram form `||D^(1/2) Zx||^2`. -/
def weightedGramQuadratic
    (Z : κ → ι → ℝ) (d : κ → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ k, d k * (synth Z x k)^2

/-- Every finite synthesis Gram form is positive semidefinite. -/
theorem gramQuadratic_nonneg (Z : κ → ι → ℝ) (x : ι → ℝ) :
    0 ≤ gramQuadratic Z x := by
  unfold gramQuadratic
  exact sum_nonneg fun k _ => sq_nonneg (synth Z x k)

/-- Nonnegative one-particle energies make the weighted gauge form positive. -/
theorem weightedGramQuadratic_nonneg
    (Z : κ → ι → ℝ) (d : κ → ℝ) (hd : ∀ k, 0 ≤ d k)
    (x : ι → ℝ) :
    0 ≤ weightedGramQuadratic Z d x := by
  unfold weightedGramQuadratic
  exact sum_nonneg fun k _ => mul_nonneg (hd k) (sq_nonneg (synth Z x k))

/-- If one synthesized component is nonzero at a strictly positive energy, the weighted
form is strictly positive. -/
theorem weightedGramQuadratic_pos_of_channel
    (Z : κ → ι → ℝ) (d : κ → ℝ) (hd : ∀ k, 0 ≤ d k)
    (x : ι → ℝ) (k0 : κ)
    (hdk : 0 < d k0) (hxk : synth Z x k0 ≠ 0) :
    0 < weightedGramQuadratic Z d x := by
  classical
  unfold weightedGramQuadratic
  have hterm : 0 < d k0 * (synth Z x k0)^2 := by
    exact mul_pos hdk (sq_pos_of_ne_zero hxk)
  have hrest : ∀ k ∈ (Finset.univ.erase k0),
      0 ≤ d k * (synth Z x k)^2 := by
    intro k hk
    exact mul_nonneg (hd k) (sq_nonneg _)
  rw [← Finset.add_sum_erase (s := Finset.univ)
    (f := fun k => d k * (synth Z x k)^2) (Finset.mem_univ k0)]
  exact add_pos_of_pos_of_nonneg hterm (sum_nonneg hrest)

end GppZetaGaugeGramPositivity
