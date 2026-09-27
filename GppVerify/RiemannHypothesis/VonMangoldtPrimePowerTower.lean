import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Finite von-Mangoldt prime-power towers

This is the finite regrouping layer needed before the global countable prime-power
rearrangement. On a fixed prime tower every positive power carries the same
von-Mangoldt coefficient `log p`.
-/

namespace GppVonMangoldtPrimePowerTower

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction

/-- Every positive power of a prime has von-Mangoldt weight `log p`. -/
theorem vonMangoldt_prime_pow (p k : ℕ) (hp : p.Prime) :
    ArithmeticFunction.vonMangoldt (p ^ (k + 1)) = Real.log p := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k)]
  exact ArithmeticFunction.vonMangoldt_apply_prime hp

/-- A finite prime-power tower factors out its constant von-Mangoldt weight for
an arbitrary real test weight. -/
theorem sum_vonMangoldt_primePowers_mul
    (p K : ℕ) (hp : p.Prime) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range K,
        ArithmeticFunction.vonMangoldt (p ^ (k + 1)) * f (p ^ (k + 1)) =
      Real.log p * ∑ k ∈ Finset.range K, f (p ^ (k + 1)) := by
  simp_rw [vonMangoldt_prime_pow p _ hp]
  rw [Finset.mul_sum]

/-- The same tower identity in the more compact single-binder range notation. -/
theorem sum_vonMangoldt_primePowers_mul_range
    (p K : ℕ) (hp : p.Prime) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range K,
      ArithmeticFunction.vonMangoldt (p ^ (k + 1)) * f (p ^ (k + 1))) =
    (∑ k ∈ Finset.range K,
      Real.log p * f (p ^ (k + 1))) := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [vonMangoldt_prime_pow p k hp]

end GppVonMangoldtPrimePowerTower

#print axioms GppVonMangoldtPrimePowerTower.vonMangoldt_prime_pow
#print axioms GppVonMangoldtPrimePowerTower.sum_vonMangoldt_primePowers_mul
