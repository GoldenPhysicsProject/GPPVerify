import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import GppVerify.RiemannHypothesis.PrimeOccupationBridge

/-!
# Prime-gas partition function

For a prime mode `p`, the local Euler factor

  Z_p(s) = (1 - p^{-s})^{-1}

has exactly the algebra of a noninteracting bosonic partition factor with mode energy
`epsilon_p = log p`.  Mathlib proves that the infinite product of these factors converges
to the Riemann zeta function on `Re s > 1`.

This file records that equality explicitly as the prime-gas partition identity.  The
statistical-mechanical interpretation is a dictionary; the product identity itself is the
classical Euler product and is machine checked.
-/

namespace GppPrimeGas

open Complex Nat

/-- Local prime partition factor. -/
noncomputable def localPartition (p : Primes) (s : ℂ) : ℂ :=
  (1 - (p : ℂ) ^ (-s))⁻¹

/-- **Prime-gas partition identity.** On the half-plane of absolute convergence, the
thermodynamic-limit product of the independent prime factors is exactly Riemann zeta. -/
theorem partition_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Primes, localPartition p s = riemannZeta s := by
  exact riemannZeta_eulerProduct_tprod hs

/-- The corresponding finite-cutoff products converge to the same global partition function. -/
theorem finite_partition_tendsto_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto
      (fun n : ℕ => ∏ p ∈ primesBelow n, localPartition ⟨p, (mem_primesBelow.mp ‹p ∈ primesBelow n›).1⟩ s)
      Filter.atTop (nhds (riemannZeta s)) := by
  simpa [localPartition] using riemannZeta_eulerProduct hs

end GppPrimeGas

#print axioms GppPrimeGas.partition_eq_riemannZeta
