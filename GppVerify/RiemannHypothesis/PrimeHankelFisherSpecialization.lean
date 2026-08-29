import GppVerify.RiemannHypothesis.PrimeHankelInfiniteLift
import GppVerify.RiemannHypothesis.GlobalVonMangoldtBridge
import Mathlib.Tactic

/-!
# Prime-gas Fisher specialization of the infinite polynomial Gram theorem

This file instantiates the abstract infinite weighted-polynomial positivity theorem
with the actual arithmetic Fisher weights

  Λ(n) log(n) exp(-β log n).

It is deliberately independent of the older cumulant/Fisher import chain, so that the
all-order Gram specialization remains usable on the current merged source tree.
-/

namespace GppPrimeHankelFisherSpecialization

open Polynomial BigOperators
open GppPrimeHankelInfiniteLift

/-- The positive arithmetic weight underlying the zeta prime-gas Fisher metric. -/
noncomputable def fisherWeight (β : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log n * Real.exp (-Real.log n * β)

/-- Every prime-gas Fisher weight is nonnegative. -/
theorem fisherWeight_nonneg (β : ℝ) (n : ℕ) : 0 ≤ fisherWeight β n := by
  unfold fisherWeight
  have hlog : 0 ≤ Real.log n := by
    rcases n with _ | n
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  exact mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog)
    (Real.exp_pos _).le

/-- Strict positivity for the actual prime-gas Fisher weights, once a finite
positive-support witness and summability of the polynomial-square series are given. -/
theorem fisher_polynomial_tsum_pos
    {β : ℝ} (p : ℝ[X]) (S : Finset ℕ) (N : ℕ)
    (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N)
    (hcard : N < (S.image (fun n : ℕ => Real.log n)).card)
    (hwS : ∀ n ∈ S, 0 < fisherWeight β n)
    (hsum : Summable
      (fun n : ℕ => fisherWeight β n * (p.eval (Real.log n)) ^ 2)) :
    0 < ∑' n : ℕ, fisherWeight β n * (p.eval (Real.log n)) ^ 2 := by
  exact weighted_polynomial_tsum_pos
    p (fun n : ℕ => Real.log n) (fisherWeight β) S N
    hp hdeg hcard
    (fisherWeight_nonneg β)
    hwS hsum

end GppPrimeHankelFisherSpecialization

#print axioms GppPrimeHankelFisherSpecialization.fisherWeight_nonneg
#print axioms GppPrimeHankelFisherSpecialization.fisher_polynomial_tsum_pos
