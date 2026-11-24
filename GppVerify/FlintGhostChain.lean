import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Flint ghost hunt, deliverable (0), first piece: the prime-power chain

Paper-forced data (Shadow Euler Identity v3.6, as tasked 2026-11-23): for a
prime-power chain the normalized divisor states obey
  ⟨v_a, v_b⟩ = p^(-|a-b|/2).
Writing `q = p^(-1/2) ∈ (0,1)`, the Gram matrix is the Kac–Murdock–Szegő
matrix `G a b = q ^ (natDist a b)`. Its inverse is the tridiagonal precision
operator stated below; `A_N` for the chain is that precision operator and
`C_N = 1/4 + A_N⁻¹ = 1/4 + G`, so the 1/4 floor for the chain is exactly
positive-semidefiniteness of `G`. The vacuum quotient and the Archimedean
channel for general `N` are NOT fixed by the chain case and are not claimed
here.
-/

namespace FlintGhost

open Matrix

/-- The chain Gram matrix: `G a b = q ^ |a - b|` on `Fin m`. -/
def chainGram (q : ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  of fun a b => q ^ (Int.natAbs ((a.1 : ℤ) - (b.1 : ℤ)))

theorem chainGram_apply (q : ℝ) (m : ℕ) (a b : Fin m) :
    chainGram q m a b = q ^ (Int.natAbs ((a.1 : ℤ) - (b.1 : ℤ))) := rfl

theorem chainGram_diag (q : ℝ) (m : ℕ) (a : Fin m) :
    chainGram q m a a = 1 := by
  simp [chainGram_apply]

theorem chainGram_symm (q : ℝ) (m : ℕ) (a b : Fin m) :
    chainGram q m a b = chainGram q m b a := by
  have h : Int.natAbs ((a.1 : ℤ) - (b.1 : ℤ)) = Int.natAbs ((b.1 : ℤ) - (a.1 : ℤ)) := by
    rw [← Int.natAbs_neg]; congr 1; ring
  rw [chainGram_apply, chainGram_apply, h]

/-- The chain precision operator (the inverse covariance), tridiagonal:
diagonal `1` at the two ends and `1 + q^2` in the interior, all scaled by
`1 / (1 - q^2)`; off-diagonal `-q / (1 - q^2)` on the two adjacent diagonals,
`0` elsewhere. Stated with `Fin m` adjacency via `Nat.dist = 1`. -/
noncomputable def chainPrecision (q : ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  of fun a b =>
    if a = b then
      (if a.1 = 0 ∨ a.1 = m - 1 then 1 else 1 + q ^ 2) / (1 - q ^ 2)
    else if Int.natAbs ((a.1 : ℤ) - (b.1 : ℤ)) = 1 then
      (-q) / (1 - q ^ 2)
    else 0

theorem chainPrecision_diag_end (q : ℝ) {m : ℕ} (a : Fin m) (ha : a.1 = 0) :
    chainPrecision q m a a = 1 / (1 - q ^ 2) := by
  simp [chainPrecision, ha]

theorem chainPrecision_offdiag_far (q : ℝ) (m : ℕ) (a b : Fin m)
    (hab : a ≠ b) (hdist : Int.natAbs ((a.1 : ℤ) - (b.1 : ℤ)) ≠ 1) :
    chainPrecision q m a b = 0 := by
  simp [chainPrecision, hab, hdist]

/-- The product identity that makes `chainPrecision` the inverse of
`chainGram`, stated as a proposition (the named obligation for this lane;
the entrywise sum has at most three nonzero terms, so the proof route is
`Finset.sum` over the tridiagonal support, not new mathematics). -/
def ChainInverseIdentity (q : ℝ) (m : ℕ) : Prop :=
  chainGram q m * chainPrecision q m = 1

end FlintGhost
