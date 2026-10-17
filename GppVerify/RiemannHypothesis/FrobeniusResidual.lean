import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Frobenius residual bounds imply quadratic residual bounds

The S36/S38 Cholesky and S37 exact LDL certificates bound a finite
matrix residual. This module proves the transfer to the quadratic
bound used by WeilResidualCoercivity. No symmetry is required.

No matrix data, interval certificate, Weil formula, or RH assumption
is asserted here. The hypotheses are explicit finite inequalities.
-/

namespace GppFrobeniusResidual

/-- A squared Frobenius bound controls every real quadratic evaluation.
The squared formulation avoids unnecessary square roots in rational certificates. -/
theorem abs_quadratic_le_of_sum_sq_le {n : ℕ}
    (E : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (eps : ℝ)
    (heps : 0 ≤ eps)
    (hE : (∑ i, ∑ j, E i j ^ 2) ≤ eps ^ 2) :
    |∑ i, ∑ j, E i j * x i * x j| ≤ eps * ∑ i, x i ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => E ij.1 ij.2) (fun ij => x ij.1 * x ij.2)
  simp only [Fintype.sum_prod_type] at hcs
  have hxx : (∑ i : Fin n, ∑ j : Fin n, (x i * x j) ^ 2) =
      (∑ i : Fin n, x i ^ 2) ^ 2 := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hn : 0 ≤ ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  rw [hxx] at hcs
  have hbound := mul_le_mul_of_nonneg_right hE
    (sq_nonneg (∑ i : Fin n, x i ^ 2))
  have hs : |∑ i, ∑ j, E i j * x i * x j| ^ 2 ≤
      (eps * ∑ i, x i ^ 2) ^ 2 := by
    rw [sq_abs, mul_pow]
    simpa only [mul_assoc] using hcs.trans hbound
  have hp : 0 ≤ eps * ∑ i : Fin n, x i ^ 2 := mul_nonneg heps hn
  nlinarith [abs_nonneg (∑ i, ∑ j, E i j * x i * x j)]

/-- Entrywise residual equality plus a finite Frobenius certificate supplies
the precise residual hypothesis expected by the coercivity bridge. -/
theorem residual_bound {n : ℕ}
    (E : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (A G lam eps : ℝ) (heps : 0 ≤ eps)
    (hE : (∑ i, ∑ j, E i j ^ 2) ≤ eps ^ 2)
    (hres : A - (lam * (∑ i, x i ^ 2) + G) =
      ∑ i, ∑ j, E i j * x i * x j) :
    |A - (lam * (∑ i, x i ^ 2) + G)| ≤ eps * ∑ i, x i ^ 2 := by
  rw [hres]
  exact abs_quadratic_le_of_sum_sq_le E x eps heps hE

/-- Complete coercivity transfer once the Gram contribution is nonnegative. -/
theorem lower_bound {n : ℕ}
    (E : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (A G lam eps : ℝ) (hG : 0 ≤ G) (heps : 0 ≤ eps)
    (hE : (∑ i, ∑ j, E i j ^ 2) ≤ eps ^ 2)
    (hres : A - (lam * (∑ i, x i ^ 2) + G) =
      ∑ i, ∑ j, E i j * x i * x j) :
    (lam - eps) * (∑ i, x i ^ 2) ≤ A := by
  have h := (abs_le.mp (residual_bound E x A G lam eps heps hE hres)).1
  linarith

end GppFrobeniusResidual

#print axioms GppFrobeniusResidual.abs_quadratic_le_of_sum_sq_le
#print axioms GppFrobeniusResidual.lower_bound
