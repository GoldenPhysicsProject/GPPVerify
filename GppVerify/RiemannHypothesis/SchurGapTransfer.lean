import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Schur-complement gap transfer

Source: Codex, GPPDiscovery2 `codex/discovery-workbench`,
`research/2026-09-28_rh_ym_vacuum_quotient_gap_principle.md` (commit `9916c1b`), §5, and its
checker `DiscoveryLean/SchurGapTransfer.lean` (`490c659`).

The note writes a positive block operator as `H = [[A, B], [Bᴴ, C]]` with a massive bulk block
`A > 0`, eliminates the bulk, and names the Schur complement `S = C − Bᴴ A⁻¹ B` as the channel
where the physical gap lives. Codex's checker proved the scalar `2 × 2` case (one inequality
direction). Here the statement is proved for matrices of any size, as an equivalence:

* `schur_gap_iff`: for `A` positive definite, the block form satisfies `H ≥ m · P_phys`
  (i.e. `H − diag(0, m·I)` is positive semidefinite) **iff** the Schur complement satisfies
  `S ≥ m·I`.
* `schur_gap_quadratic`: the same statement read on vectors: `⟪(x, y), H (x, y)⟫ ≥ m ‖y‖²`
  for all `x, y` when `S ≥ m·I`.
* `scalar_schur_gap`: Codex's scalar core, kept for reference.

So the bulk block can be arbitrarily massive and still transfer no gap: whether the physical
channel is gapped is decided entirely by `S`. That is the note's point, and it is exact.

## Scope

Finite-dimensional linear algebra only. The note's identifications of `A`, `B`, `C` with the
causal prime Koszul bulk, the determinant-line coupling and the pole/Archimedean channel, and
the statement "RH is positivity of this Schur complement", are not formalized here. The note's
§6 Yang–Mills programme is, as the note says, a research template and is not claimed.
-/

open Matrix

namespace GppSchurGapTransfer

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [Fintype n] [DecidableEq m] in
/-- `H − diag(0, m·I) = [[A, B], [Bᴴ, C − m·I]]`. -/
theorem fromBlocks_sub_gap (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ) (μ : ℝ) :
    fromBlocks A B Bᴴ C - fromBlocks 0 0 0 (μ • (1 : Matrix n n ℝ)) =
      fromBlocks A B Bᴴ (C - μ • 1) := by
  rw [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]; simp [sub_eq_add_neg]

/-- **Schur-complement gap transfer.** With a positive-definite bulk block `A`, the physical
channel of `H = [[A, B], [Bᴴ, C]]` carries the gap `μ` exactly when the Schur complement does:
`H − diag(0, μ·I) ⪰ 0 ↔ C − Bᴴ A⁻¹ B − μ·I ⪰ 0`. -/
theorem schur_gap_iff (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ) (μ : ℝ)
    (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ C - fromBlocks 0 0 0 (μ • (1 : Matrix n n ℝ))).PosSemidef ↔
      (C - Bᴴ * A⁻¹ * B - μ • 1).PosSemidef := by
  rw [fromBlocks_sub_gap, hA.fromBlocks₁₁ B (C - μ • 1), sub_right_comm]

/-- **The gap on vectors.** If the Schur complement satisfies `S ⪰ μ·I`, then for every bulk
vector `x` and physical vector `y`, `⟪(x, y), H (x, y)⟫ ≥ μ ‖y‖²`. -/
theorem schur_gap_quadratic (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ) (μ : ℝ)
    (hA : A.PosDef) [Invertible A] (hS : (C - Bᴴ * A⁻¹ * B - μ • 1).PosSemidef)
    (x : m → ℝ) (y : n → ℝ) :
    μ * (y ⬝ᵥ y) ≤ (Sum.elim x y) ⬝ᵥ (fromBlocks A B Bᴴ C *ᵥ Sum.elim x y) := by
  have h := ((schur_gap_iff A B C μ hA).mpr hS)
  have h2 := (posSemidef_iff_dotProduct_mulVec.mp h).2 (Sum.elim x y)
  simp only [star_trivial] at h2
  rw [sub_mulVec, dotProduct_sub, sub_nonneg] at h2
  refine le_trans (le_of_eq ?_) h2
  rw [fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.smul_apply, Matrix.one_apply,
    Finset.mul_sum, mul_comm, mul_left_comm]

/-- Codex's scalar core: `a > 0` and `b² ≤ a (c − μ)` give `μ y² ≤ a x² + 2bxy + c y²`. -/
theorem scalar_schur_gap (a b c μ x y : ℝ) (ha : 0 < a) (hSchur : b ^ 2 ≤ a * (c - μ)) :
    μ * y ^ 2 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  have hprod : 0 ≤ (a * (c - μ) - b ^ 2) * y ^ 2 := mul_nonneg (by linarith) (sq_nonneg y)
  have hsq : 0 ≤ (a * x + b * y) ^ 2 := sq_nonneg _
  nlinarith

end GppSchurGapTransfer
