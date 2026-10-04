import GppVerify.RiemannHypothesis.HalfDensityZetaGauge
import Mathlib.Tactic

/-!
# Positive covariant logarithmic generator in the finite zeta-graph metric

The half-density gauge identity says

  M D Z - D = L_Λ.

Equivalently, with H := D + L_Λ,

  Z H = D Z

on every finite divisor-closed positive set.

This file records the corresponding positive-energy identity.  In the
zeta-graph metric G = Zᵀ Z, the covariant logarithmic generator H is
positive because it is similar to the nonnegative multiplication operator
D through the exact zeta synthesis.

This is finite, zero-independent arithmetic algebra.  It does not prove
that the completed Weil form is this positive energy; identifying the
Archimedean/Tate boundary subtraction with the remaining free channel is
the open sewing problem.
-/

namespace GppZetaGaugePositiveConnection

open Finset GppHalfDensityZetaGauge

/-- The covariant logarithmic generator H = D + L_Λ. -/
noncomputable def covariantLog (S : Finset ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  logMul f n + halfVonMangoldt S f n

/-- Exact intertwining: Z (D + L_Λ) = D Z.

This is the gauge identity after applying the inverse synthesis. -/
theorem halfZeta_covariantLog
    {S : Finset ℕ} (hS : DivisorClosed S) (f : ℕ → ℝ)
    {n : ℕ} (hn : n ∈ S) :
    halfZeta S (covariantLog S f) n = logMul (halfZeta S f) n := by
  calc
    halfZeta S (covariantLog S f) n
        = halfZeta S (halfMobius S (logMul (halfZeta S f))) n := by
            unfold halfZeta
            refine Finset.sum_congr rfl ?_
            intro d hd
            have hdS : d ∈ S := (Finset.mem_filter.mp hd).1
            have hg := half_density_gauge hS f hdS
            have hm :
                covariantLog S f d =
                  halfMobius S (logMul (halfZeta S f)) d := by
              unfold covariantLog
              linarith
            rw [hm]
    _ = logMul (halfZeta S f) n := halfZeta_halfMobius hS _ hn

/-- The zeta-graph quadratic form of the covariant generator is exactly a
sum of nonnegative logarithmic energies:
<Zf, ZHf> = Σ log(n) |Zf(n)|². -/
theorem covariantLog_energy_eq
    {S : Finset ℕ} (hS : DivisorClosed S) (f : ℕ → ℝ) :
    (∑ n ∈ S, halfZeta S f n * halfZeta S (covariantLog S f) n) =
      ∑ n ∈ S, Real.log n * (halfZeta S f n) ^ 2 := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [halfZeta_covariantLog hS f hn]
  unfold logMul
  ring

/-- Finite Euler-product positivity in the exact zeta-graph metric.

For a divisor-closed set, every index is a positive integer, hence log n ≥ 0.
Therefore the covariant generator D + L_Λ is positive in the ZᵀZ metric. -/
theorem covariantLog_energy_nonneg
    {S : Finset ℕ} (hS : DivisorClosed S) (f : ℕ → ℝ) :
    0 ≤ ∑ n ∈ S, halfZeta S f n * halfZeta S (covariantLog S f) n := by
  rw [covariantLog_energy_eq hS f]
  apply Finset.sum_nonneg
  intro n hn
  have hn0 : n ≠ 0 := fun h => hS.zero_not_mem (h ▸ hn)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  exact mul_nonneg hlog (sq_nonneg _)

end GppZetaGaugePositiveConnection
