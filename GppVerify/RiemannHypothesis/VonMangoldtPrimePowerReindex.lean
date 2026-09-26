import GppVerify.RiemannHypothesis.VonMangoldtCosineBridge
import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerTower
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

/-!
# Countable von-Mangoldt prime-power reindexing

The von-Mangoldt cosine summand is supported on prime powers. Mathlib provides the
canonical equivalence
`Nat.Primes × ℕ ≃ {n : ℕ // IsPrimePow n}`, `(p,k) ↦ p^(k+1)`.
This file uses that equivalence to perform the global countable reindexing exactly.
-/

namespace GppVonMangoldtPrimePowerReindex

open Set Complex
open ArithmeticFunction
open GppVonMangoldtCosine

noncomputable def cosineSummand (a t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    Real.exp (-Real.log n * a) * Real.cos (Real.log n * t)

theorem cosineSummand_eq_zero_of_not_primePow
    (a t : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) :
    cosineSummand a t n = 0 := by
  rw [cosineSummand, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  simp

theorem support_cosineSummand_subset_primePowers (a t : ℝ) :
    Function.support (cosineSummand a t) ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpp
  exact hn (cosineSummand_eq_zero_of_not_primePow a t hpp)

/-- Exact geometric-cosine form of a single prime-power summand. -/
theorem cosineSummand_primePower
    (p : Nat.Primes) (k : ℕ) (a t : ℝ) :
    cosineSummand a t ((p : ℕ) ^ (k + 1)) =
      Real.log (p : ℕ) *
        Real.exp (-(k + 1 : ℝ) * Real.log (p : ℕ) * a) *
        Real.cos ((k + 1 : ℝ) * Real.log (p : ℕ) * t) := by
  rw [cosineSummand]
  rw [GppVonMangoldtPrimePowerTower.vonMangoldt_prime_pow (p : ℕ) k p.prop]
  norm_cast
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  congr 2 <;> ring

/-- Exact global reindexing from natural numbers to canonical prime-power coordinates. -/
theorem cosine_tsum_eq_primePower_pair_tsum (a t : ℝ) :
    (∑' n : ℕ, cosineSummand a t n) =
      ∑' pk : Nat.Primes × ℕ,
        cosineSummand a t ((pk.1 : ℕ) ^ (pk.2 + 1)) := by
  let S : Set ℕ := {n : ℕ | IsPrimePow n}
  have hsupp : Function.support (cosineSummand a t) ⊆ S :=
    support_cosineSummand_subset_primePowers a t
  calc
    (∑' n : ℕ, cosineSummand a t n) =
        ∑' n : S, cosineSummand a t n :=
      (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' pk : Nat.Primes × ℕ,
        cosineSummand a t ((pk.1 : ℕ) ^ (pk.2 + 1)) := by
      simpa [S] using
        (Nat.Primes.prodNatEquiv.tsum_eq
          (fun n : {n : ℕ // IsPrimePow n} => cosineSummand a t n)).symm

/-- The canonical pair sum in explicit geometric-cosine coordinates. -/
theorem cosine_tsum_eq_primePower_geometric_tsum (a t : ℝ) :
    (∑' n : ℕ, cosineSummand a t n) =
      ∑' pk : Nat.Primes × ℕ,
        Real.log (pk.1 : ℕ) *
          Real.exp (-(pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) * a) *
          Real.cos ((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) * t) := by
  rw [cosine_tsum_eq_primePower_pair_tsum]
  apply tsum_congr
  intro pk
  exact cosineSummand_primePower pk.1 pk.2 a t

/-- The real logarithmic derivative is therefore exactly the canonical double
prime-power sum on `a>1`. -/
theorem neg_zeta_logDeriv_re_eq_primePower_geometric_tsum
    {a t : ℝ} (ha : 1 < a) :
    (-(deriv riemannZeta
      ((a : ℂ) + (t : ℂ) * I) /
      riemannZeta ((a : ℂ) + (t : ℂ) * I))).re =
      ∑' pk : Nat.Primes × ℕ,
        Real.log (pk.1 : ℕ) *
          Real.exp (-(pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) * a) *
          Real.cos ((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) * t) := by
  rw [GppVonMangoldtCosine.neg_zeta_logDeriv_re_eq_vonMangoldt_cosine_tsum ha]
  exact cosine_tsum_eq_primePower_geometric_tsum a t

end GppVonMangoldtPrimePowerReindex

#print axioms GppVonMangoldtPrimePowerReindex.cosineSummand_primePower
#print axioms GppVonMangoldtPrimePowerReindex.cosine_tsum_eq_primePower_pair_tsum
#print axioms GppVonMangoldtPrimePowerReindex.neg_zeta_logDeriv_re_eq_primePower_geometric_tsum
