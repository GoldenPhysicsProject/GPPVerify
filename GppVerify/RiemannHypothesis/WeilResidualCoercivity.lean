import Mathlib.Tactic

/-!
# Conditional residual-matrix coercivity

The numerical S36/S38 cholres and S37 ldlt_exact programs produce
an approximate Gram/LDL factorization plus a rigorous residual bound.
These elementary theorems isolate the exact coercivity implication.

The hypotheses explicitly INCLUDE the quadratic residual inequality:
this file does not import or verify any numerical certificate,
matrix entry, Frobenius bound, or Weil trace formula.
-/

namespace GppWeilResidualCoercivity

/-- Every real finite Cholesky Gram quadratic is nonnegative. -/
theorem cholesky_gram_nonneg {m n : ℕ}
    (R : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    0 ≤ ∑ k : Fin m, (∑ i : Fin n, R k i * x i) ^ 2 := by
  apply Finset.sum_nonneg
  intro k hk
  exact sq_nonneg _

/-- Every real finite nonnegative-diagonal LDL quadratic is nonnegative. -/
theorem ldlt_gram_nonneg {m n : ℕ}
    (R : Fin m → Fin n → ℝ) (d : Fin m → ℝ)
    (hd : ∀ k, 0 ≤ d k) (x : Fin n → ℝ) :
    0 ≤ ∑ k : Fin m, d k * (∑ i : Fin n, R k i * x i) ^ 2 := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hd k) (sq_nonneg _)

/-- Rump-style residual coercivity conditional on the actual residual
quadratic bound. No unproved computational assertions are introduced. -/
theorem cholesky_residual_lower {m n : ℕ}
    (R : Fin m → Fin n → ℝ)
    (A : (Fin n → ℝ) → ℝ)
    (lam eps : ℝ) (x : Fin n → ℝ)
    (hres :
      |A x - (lam * (∑ i : Fin n, (x i) ^ 2) +
        ∑ k : Fin m, (∑ i : Fin n, R k i * x i) ^ 2)| ≤
        eps * (∑ i : Fin n, (x i) ^ 2)) :
    (lam - eps) * (∑ i : Fin n, (x i) ^ 2) ≤ A x := by
  have hgram := cholesky_gram_nonneg R x
  have hlow := (abs_le.mp hres).1
  linarith

/-- Transfer for an LDL factorization with a verified nonnegative diagonal.
No unit-triangularity is needed for this implication. -/
theorem ldlt_residual_lower {m n : ℕ}
    (R : Fin m → Fin n → ℝ) (d : Fin m → ℝ)
    (hd : ∀ k, 0 ≤ d k)
    (A : (Fin n → ℝ) → ℝ)
    (lam eps : ℝ) (x : Fin n → ℝ)
    (hres :
      |A x - (lam * (∑ i : Fin n, (x i) ^ 2) +
        ∑ k : Fin m, d k * (∑ i : Fin n, R k i * x i) ^ 2)| ≤
        eps * (∑ i : Fin n, (x i) ^ 2)) :
    (lam - eps) * (∑ i : Fin n, (x i) ^ 2) ≤ A x := by
  have hgram := ldlt_gram_nonneg R d hd x
  have hlow := (abs_le.mp hres).1
  linarith

/-- Strict positivity when the norm is nonzero and lam > eps. -/
theorem cholesky_residual_pos {m n : ℕ}
    (R : Fin m → Fin n → ℝ)
    (A : (Fin n → ℝ) → ℝ)
    (lam eps : ℝ) (x : Fin n → ℝ)
    (hlam : eps < lam)
    (hx : 0 < ∑ i : Fin n, (x i) ^ 2)
    (hres :
      |A x - (lam * (∑ i : Fin n, (x i) ^ 2) +
        ∑ k : Fin m, (∑ i : Fin n, R k i * x i) ^ 2)| ≤
        eps * (∑ i : Fin n, (x i) ^ 2)) :
    0 < A x := by
  have hbound := cholesky_residual_lower R A lam eps x hres
  have hpos : 0 < (lam - eps) * (∑ i : Fin n, (x i) ^ 2) :=
    mul_pos (sub_pos.mpr hlam) hx
  linarith

end GppWeilResidualCoercivity
