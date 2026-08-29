import GppVerify.RiemannHypothesis.PrimeHankelPolynomialSummability
import GppVerify.RiemannHypothesis.PrimeHankelRootEscape
import GppVerify.RiemannHypothesis.PrimeHankelInfiniteLift
import Mathlib.Tactic

/-!
# Unconditional all-order strict prime-gas Hankel Gram positivity

The remaining finite-support witness can be supplied uniformly by the prime powers

  2, 4, 8, ..., 2^(N+1).

Their von Mangoldt values are all `log 2`, while their logarithmic support points are

  log(2^(k+1)) = (k+1) log 2,

so a nonzero degree-`N` polynomial cannot vanish on all `N+1` of them.  Together with
polynomial-square summability, this closes the strict weighted polynomial Gram theorem
for the actual arithmetic Fisher measure on every `β > 1`.
-/

namespace GppPrimeHankelAllOrderStrict

open Polynomial BigOperators ArithmeticFunction
open GppPrimeHankelRootEscape
open GppPrimeHankelInfiniteLift
open GppPrimeHankelFisherSpecialization
open GppPrimeHankelPolynomialSummability

/-- The arithmetic progression `(k+1) log 2` is injective. -/
theorem logTwo_support_injective :
    Function.Injective (fun k : ℕ => (((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ))) := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  intro a b hab
  have hab' : (((a + 1 : ℕ) : ℝ)) = (((b + 1 : ℕ) : ℝ)) :=
    (mul_left_inj' hlog2).mp hab
  exact Nat.succ.inj (by exact_mod_cast hab')

/-- The first `N+1` powers of two provide `N+1` distinct logarithmic support values. -/
theorem logTwo_support_card (N : ℕ) :
    ((Finset.range (N + 1)).image
      (fun k : ℕ => (((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)))).card = N + 1 := by
  rw [Finset.card_image_iff.mpr logTwo_support_injective.injOn]
  exact Finset.card_range (N + 1)

/-- Every positive power of two has strictly positive actual Fisher weight. -/
theorem fisherWeight_two_pow_pos
    {β : ℝ} (k : ℕ) :
    0 < fisherWeight β (2 ^ (k + 1)) := by
  have hk : k + 1 ≠ 0 := by omega
  have hvm :
      ArithmeticFunction.vonMangoldt (2 ^ (k + 1)) = Real.log (2 : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk]
    simpa using (ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two)
  have hlogpow :
      Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) =
        (((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (Real.log_pow (2 : ℝ) (k + 1))
  unfold fisherWeight
  rw [hvm, hlogpow]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkreal : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  positivity

/-- **All-order strict prime-gas polynomial Gram positivity.**  For every `β>1`
and every nonzero real polynomial `p`, the full von-Mangoldt/Fisher weighted square
is strictly positive. -/
theorem fisher_polynomial_tsum_pos_unconditional
    {β : ℝ} (hβ : 1 < β) (p : ℝ[X]) (hp : p ≠ 0) :
    0 < ∑' n : ℕ,
      fisherWeight β n * (p.eval (Real.log n)) ^ 2 := by
  let T : Finset ℝ :=
    (Finset.range (p.natDegree + 1)).image
      (fun k : ℕ => (((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)))
  have hcard : p.natDegree < T.card := by
    have hT : T.card = p.natDegree + 1 := by
      simpa [T] using logTwo_support_card p.natDegree
    omega
  rcases exists_eval_ne_zero_of_natDegree_lt_card p T hp hcard with
    ⟨y, hy, hpy⟩
  rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
  let n : ℕ := 2 ^ (k + 1)
  have hlogn :
      Real.log (n : ℝ) = (((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)) := by
    dsimp [n]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (Real.log_pow (2 : ℝ) (k + 1))
  have hpeval : p.eval (Real.log n) ≠ 0 := by
    simpa [hlogn] using hpy
  have hw : 0 < fisherWeight β n := by
    dsimp [n]
    exact fisherWeight_two_pow_pos k
  have hsingle :
      0 < ∑ i ∈ ({n} : Finset ℕ),
        fisherWeight β i * (p.eval (Real.log i)) ^ 2 := by
    simp only [Finset.sum_singleton]
    exact mul_pos hw (sq_pos_of_ne_zero hpeval)
  apply weighted_sq_tsum_pos
    (fisherWeight β) (fun i : ℕ => p.eval (Real.log i)) ({n} : Finset ℕ)
    (summable_fisherWeight_mul_polynomial_eval_sq hβ p)
    (fisherWeight_nonneg β)
    hsingle

end GppPrimeHankelAllOrderStrict

#print axioms GppPrimeHankelAllOrderStrict.logTwo_support_injective
#print axioms GppPrimeHankelAllOrderStrict.fisherWeight_two_pow_pos
#print axioms GppPrimeHankelAllOrderStrict.fisher_polynomial_tsum_pos_unconditional
