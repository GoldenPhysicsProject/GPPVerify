import GppVerify.RiemannHypothesis.RankOneThresholdControls
import Mathlib.Tactic

/-!
# Rank-one Weil pole: full negative-threshold Schur inequality

Extend the existing equality-only pole_threshold_neg theorem to
a scalar inequality equivalent to PSD of the rank-one update,
assuming A is symmetric invertible and positive on c-perp, and
s=c^T A^-1 c<0.

Proof by exact decomposition x=alpha u+y with y perpendicular to c.
Then x^T (A+cc^T/2)x=y^T A y+alpha^2 s(1+s/2).
The threshold is s<=-2, not merely s=-2.
No zeta-zero or Weil form positivity is assumed.
-/

open Matrix

namespace GppRankOneControls

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem pole_threshold_neg_iff (A : Matrix n n ℝ) (hsymm : A.IsSymm)
    (hdet : IsUnit A.det) (c : n → ℝ)
    (hsneg : c ⬝ᵥ (A⁻¹ *ᵥ c) < 0)
    (hpd : ∀ y : n → ℝ, y ⬝ᵥ c = 0 → y ≠ 0 →
      0 < y ⬝ᵥ (A *ᵥ y)) :
    (∀ x : n → ℝ,
      0 ≤ x ⬝ᵥ ((A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x)) ↔
        c ⬝ᵥ (A⁻¹ *ᵥ c) ≤ -2 := by
  set u : n → ℝ := A⁻¹ *ᵥ c with hu
  set s : ℝ := c ⬝ᵥ u with hs
  have hAu : A *ᵥ u = c := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have huAu : u ⬝ᵥ (A *ᵥ u) = s := by
    rw [hAu, dotProduct_comm]
    exact hs.symm
  have hsneg' : s < 0 := hsneg
  have hsne : s ≠ 0 := ne_of_lt hsneg'
  have htotal : ∀ x : n → ℝ,
      ∃ (α : ℝ) (y : n → ℝ),
        y ⬝ᵥ c = 0 ∧
        x ⬝ᵥ ((A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x) =
          y ⬝ᵥ (A *ᵥ y) + α ^ 2 * (s + s ^ 2 / 2) := by
    intro x
    let α : ℝ := (c ⬝ᵥ x) / s
    let y : n → ℝ := x - α • u
    have hαs : α * s = c ⬝ᵥ x := by
      dsimp [α]
      field_simp [hsne]
    have hyc : y ⬝ᵥ c = 0 := by
      rw [show y = x - α • u from rfl, sub_dotProduct, smul_dotProduct,
        dotProduct_comm u c, ← hs, dotProduct_comm x c, ← hαs]
      ring
    have hx : x = y + α • u := by
      dsimp [y]
      abel
    have hyAu : y ⬝ᵥ (A *ᵥ u) = 0 := by
      rw [hAu]
      exact hyc
    have hquad : x ⬝ᵥ (A *ᵥ x) =
        y ⬝ᵥ (A *ᵥ y) + α ^ 2 * s := by
      conv_lhs => rw [hx]
      rw [quad_add A hsymm]
      simp only [Matrix.mulVec_smul, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      rw [hyAu, huAu]
      ring
    have hrank : x ⬝ᵥ (((1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x) =
        α ^ 2 * s ^ 2 / 2 := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        quad_vecMulVec c x, ← hαs]
      ring
    refine ⟨α, y, hyc, ?_⟩
    rw [Matrix.add_mulVec, dotProduct_add, hquad, hrank]
    ring
  constructor
  · intro hnon
    have hqu : u ⬝ᵥ ((A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ u) =
        s + s ^ 2 / 2 := by
      rw [Matrix.add_mulVec, dotProduct_add, huAu,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        quad_vecMulVec c u, ← hs]
      ring
    have hu := hnon u
    rw [hqu] at hu
    have : s ≤ -2 := by
      by_contra h
      have hgt : -2 < s := lt_of_not_ge h
      have hnegprod : s * (s + 2) < 0 :=
        mul_neg_of_neg_of_pos hsneg' (by linarith)
      nlinarith
    exact this
  · intro hle x
    obtain ⟨α, y, hyc, hform⟩ := htotal x
    have hpos : 0 ≤ y ⬝ᵥ (A *ᵥ y) := by
      by_cases hy : y = 0
      · rw [hy]
        simp
      · exact (hpd y hyc hy).le
    have hprod : 0 ≤ s * (s + 2) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hcoeff : 0 ≤ s + s ^ 2 / 2 := by nlinarith
    rw [hform]
    nlinarith [mul_nonneg (sq_nonneg α) hcoeff]

end GppRankOneControls
