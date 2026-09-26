import GppVerify.RiemannHypothesis.CausalHeatPrimePowerAnomaly
import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerReindex
import Mathlib.Tactic

/-!
# Causal heat anomaly and the global von Mangoldt Gaussian sum

This file formalizes the zero-independent arithmetic reindexing behind the causal
Dirichlet-heat proposal.  The operator trace identity

  Tr(E_t V_a - V_a E_t) = a / sqrt(4*pi*t) * exp(-a^2/(4t))

is deliberately NOT assumed here.  Starting only from its scalar profile already
isolated in `CausalHeatPrimePowerAnomaly`, we prove that the Euler-log `1/m`
coefficient produces exactly the Gaussian von Mangoldt prime-power term and that the
resulting natural-number `tsum` reindexes canonically over `(prime, exponent)`.

No RH claim and no prime--Archimedean trace-class claim is made.
-/

namespace GppCausalHeatVonMangoldtReindex

open Real
open ArithmeticFunction
open GppCausalHeatPrimePowerAnomaly

/-- The prime-side Gaussian heat summand occurring in the completed relative heat
formula, written in exponential half-density form `exp(-log n / 2)` rather than
`1/sqrt n`.  For positive integers these are equal; the exponential form interacts
cleanly with prime powers. -/
noncomputable def primeHeatSummand (t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    Real.exp (-(Real.log n) / 2) /
      Real.sqrt (4 * Real.pi * t) *
    Real.exp (-((Real.log n) ^ 2) / (4 * t))

/-- The Gaussian heat summand is supported on prime powers because the von Mangoldt
function is. -/
theorem primeHeatSummand_eq_zero_of_not_primePow
    (t : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) :
    primeHeatSummand t n = 0 := by
  rw [primeHeatSummand, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  simp

/-- Support inclusion needed for the canonical prime-power reindexing. -/
theorem support_primeHeatSummand_subset_primePowers (t : ℝ) :
    Function.support (primeHeatSummand t) ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpp
  exact hn (primeHeatSummand_eq_zero_of_not_primePow t hpp)

/-- Exact form of one Gaussian heat summand on the prime power `p^(k+1)`. -/
theorem primeHeatSummand_primePower
    (p : Nat.Primes) (k : ℕ) (t : ℝ) :
    primeHeatSummand t ((p : ℕ) ^ (k + 1)) =
      Real.log (p : ℕ) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) / 2) /
          Real.sqrt (4 * Real.pi * t) *
        Real.exp (-((((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) ^ 2) / (4 * t)) := by
  rw [primeHeatSummand]
  rw [GppVonMangoldtPrimePowerTower.vonMangoldt_prime_pow (p : ℕ) k p.prop]
  norm_cast
  rw [Nat.cast_pow, Real.log_pow]

/-- The `m`th Euler-log weighted causal anomaly is exactly the corresponding global
von Mangoldt Gaussian summand.  This is the precise local-to-arithmetic coefficient
matching required by the August relative-heat program. -/
theorem eulerWeightedAnomaly_eq_primeHeatSummand
    (p : Nat.Primes) (k : ℕ) (t : ℝ) :
    (1 / ((k + 1 : ℕ) : ℝ)) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) / 2) *
        boundaryAnomaly t (((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) =
      primeHeatSummand t ((p : ℕ) ^ (k + 1)) := by
  rw [eulerLog_boundaryAnomaly_eq_vonMangoldt_primePower]
  rw [primeHeatSummand_primePower]
  rw [GppVonMangoldtPrimePowerTower.vonMangoldt_prime_pow (p : ℕ) k p.prop]

/-- Exact countable reindexing of the Gaussian von Mangoldt heat sum from natural
numbers to canonical prime-power coordinates.  This uses only support and the standard
`Nat.Primes × Nat` equivalence; no exchange of two independently defined infinite sums
is being asserted. -/
theorem primeHeat_tsum_eq_primePower_pair_tsum (t : ℝ) :
    (∑' n : ℕ, primeHeatSummand t n) =
      ∑' pk : Nat.Primes × ℕ,
        primeHeatSummand t ((pk.1 : ℕ) ^ (pk.2 + 1)) := by
  let S : Set ℕ := {n : ℕ | IsPrimePow n}
  have hsupp : Function.support (primeHeatSummand t) ⊆ S :=
    support_primeHeatSummand_subset_primePowers t
  calc
    (∑' n : ℕ, primeHeatSummand t n) =
        ∑' n : S, primeHeatSummand t n :=
      (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' pk : Nat.Primes × ℕ,
        primeHeatSummand t ((pk.1 : ℕ) ^ (pk.2 + 1)) := by
      simpa [S] using
        (Nat.Primes.prodNatEquiv.tsum_eq
          (fun n : {n : ℕ // IsPrimePow n} => primeHeatSummand t n)).symm

/-- Combined form: the canonical prime-power sum may be written directly with the
Euler-log weighted causal anomaly profile term-by-term. -/
theorem primeHeat_tsum_eq_eulerWeightedAnomaly_pair_tsum (t : ℝ) :
    (∑' n : ℕ, primeHeatSummand t n) =
      ∑' pk : Nat.Primes × ℕ,
        (1 / ((pk.2 + 1 : ℕ) : ℝ)) *
          Real.exp (-(((pk.2 + 1 : ℕ) : ℝ) * Real.log (pk.1 : ℕ)) / 2) *
          boundaryAnomaly t
            (((pk.2 + 1 : ℕ) : ℝ) * Real.log (pk.1 : ℕ)) := by
  rw [primeHeat_tsum_eq_primePower_pair_tsum]
  apply tsum_congr
  intro pk
  exact (eulerWeightedAnomaly_eq_primeHeatSummand pk.1 pk.2 t).symm

end GppCausalHeatVonMangoldtReindex

#print axioms GppCausalHeatVonMangoldtReindex.primeHeatSummand_primePower
#print axioms GppCausalHeatVonMangoldtReindex.eulerWeightedAnomaly_eq_primeHeatSummand
#print axioms GppCausalHeatVonMangoldtReindex.primeHeat_tsum_eq_primePower_pair_tsum
#print axioms GppCausalHeatVonMangoldtReindex.primeHeat_tsum_eq_eulerWeightedAnomaly_pair_tsum
