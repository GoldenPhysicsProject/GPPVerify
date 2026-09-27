import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerTower
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Causal heat anomaly: exact prime-power coefficient cancellation

The latest arithmetic-principal-series program replaces bilateral Gaussian heat by the
Dirichlet heat semigroup on the positive half-line.  The operator trace identity itself
is not asserted here.  This file isolates the exact scalar algebra which explains why
its Euler-log expansion produces the von Mangoldt coefficient with no extra factor of
`m`.

If the boundary commutator anomaly of a shift by `a` is

  a / sqrt(4*pi*t) * exp(-a^2/(4*t)),

then the `m`th term of

  -log(1 - p^(-1/2) V_(log p))
    = sum_{m>=1} p^(-m/2) V_(m log p) / m

contains a `1/m`.  Substituting `a = m log p`, that coefficient cancels the `m`
from the boundary anomaly and leaves exactly `log p = Lambda(p^m)`.

No trace-class, convergence, completed-zeta, or RH statement is made here.
-/

namespace GppCausalHeatPrimePowerAnomaly

open Real
open ArithmeticFunction

/-- Scalar boundary-anomaly profile associated with a positive heat time.  The formula
is defined for all real `t`; analytic use will later impose `0 < t`. -/
noncomputable def boundaryAnomaly (t a : ℝ) : ℝ :=
  a / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t))

/-- `m = k+1` is always nonzero as a real scalar. -/
theorem natSucc_cast_ne_zero (k : ℕ) : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
  positivity

/-- Exact cancellation of the Euler-log `1/m` coefficient against the shift length
`m log p` in the causal boundary anomaly.  No hypothesis on the heat denominator is
needed: only the positive integer `m=k+1` is cancelled. -/
theorem eulerLog_boundaryAnomaly_cancel
    (p : Nat.Primes) (k : ℕ) (t : ℝ) :
    (1 / ((k + 1 : ℕ) : ℝ)) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) / 2) *
        boundaryAnomaly t (((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) =
      Real.log (p : ℕ) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) / 2) /
          Real.sqrt (4 * Real.pi * t) *
        Real.exp (-((((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) ^ 2) / (4 * t)) := by
  let m : ℝ := ((k + 1 : ℕ) : ℝ)
  let L : ℝ := Real.log (p : ℕ)
  let E : ℝ := Real.exp (-(m * L) / 2)
  let D : ℝ := Real.sqrt (4 * Real.pi * t)
  let G : ℝ := Real.exp (-((m * L) ^ 2) / (4 * t))
  have hm : m ≠ 0 := by
    dsimp [m]
    exact natSucc_cast_ne_zero k
  have hcancel : (1 / m) * (m * L) = L := by
    field_simp [hm]
  change (1 / m) * E * ((m * L) / D * G) = L * E / D * G
  calc
    (1 / m) * E * ((m * L) / D * G) =
        ((1 / m) * (m * L)) * E / D * G := by ring
    _ = L * E / D * G := by rw [hcancel]

/-- The coefficient left after the `1/m` cancellation is exactly the von Mangoldt
value of the corresponding prime power. -/
theorem eulerLog_boundaryAnomaly_eq_vonMangoldt_primePower
    (p : Nat.Primes) (k : ℕ) (t : ℝ) :
    (1 / ((k + 1 : ℕ) : ℝ)) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) / 2) *
        boundaryAnomaly t (((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) =
      ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1)) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) / 2) /
          Real.sqrt (4 * Real.pi * t) *
        Real.exp (-((((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ)) ^ 2) / (4 * t)) := by
  rw [GppVonMangoldtPrimePowerTower.vonMangoldt_prime_pow (p : ℕ) k p.prop]
  exact eulerLog_boundaryAnomaly_cancel p k t

end GppCausalHeatPrimePowerAnomaly

#print axioms GppCausalHeatPrimePowerAnomaly.eulerLog_boundaryAnomaly_cancel
#print axioms GppCausalHeatPrimePowerAnomaly.eulerLog_boundaryAnomaly_eq_vonMangoldt_primePower
