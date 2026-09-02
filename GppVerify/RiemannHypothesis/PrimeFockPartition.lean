import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The primon gas: occupation-basis partition function is `ζ`

`PrimeGasPartition.lean` records the *product* side of the prime-gas dictionary — the Euler
product `∏_p (1 - p^{-s})⁻¹ = ζ(s)`, which is Mathlib's `riemannZeta_eulerProduct_tprod`.
This file supplies the **sum** side, over the Fock occupation basis, which the product form
does not give:

  `∑_{configurations n} e^{-s E(n)} = ζ(s)`   for `Re s > 1`.

A *configuration* is a finitely-supported assignment of an occupation number `n_p` to each
prime mode `p`, with mode energy `ε_p = log p`. Its total energy is `E(n) = ∑_p n_p log p`.

## What is actually proved, and what is dictionary

The mathematics here is **unique factorization**, in two steps:

* `occEnergy_eq_log_occNumber` — energy is the logarithm of an integer. The sum
  `∑_p n_p log p` collapses to `log N` for `N = ∏_p p^{n_p}`, so a configuration's energy is
  never an independent quantity: it is determined by the integer the configuration encodes.
* `occNumber_eq_factorizationEquiv` — that encoding is exactly Mathlib's
  `Nat.factorizationEquiv`, so configurations **biject with the positive integers**.

Given those, `e^{-sE(n)} = N^{-s}` (`boltzmann_eq_inv_cpow`) and the partition sum is
`∑_{N ≥ 1} N^{-s}`, which is `ζ(s)` on `Re s > 1`.

The statistical-mechanical reading — that this is a free bosonic gas whose modes are the
primes, whose states are the positive integers, and whose partition function is `ζ` — is a
**dictionary**, as in `PrimeGasPartition.lean`. Nothing here constructs a Fock space, a
Hamiltonian, or a Hilbert space; `dΓ(L)` does not appear. What is machine-checked is the
combinatorial identity that dictionary rests on. Reporting this as "the prime Fock
Hamiltonian is formalized" would overstate it.

**No RH content.** `Re s > 1` is the half-plane of absolute convergence, strictly to the
right of the critical strip. Nothing here says anything about zeros.
-/

namespace GppPrimeFock

open Finset

/-- A configuration of the primon gas: an occupation number for each prime mode, finitely
    many nonzero. This is the occupation ("Fock") basis label, not an element of a
    constructed Fock space. -/
abbrev PrimeOccupation := { f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p }

/-- The positive integer a configuration encodes, `N(n) = ∏_p p^{n_p}`. -/
def occNumber (f : PrimeOccupation) : ℕ := f.1.prod (· ^ ·)

/-- Total energy of a configuration, `E(n) = ∑_p n_p log p`, for mode energies
    `ε_p = log p`. -/
noncomputable def occEnergy (f : PrimeOccupation) : ℝ :=
  ∑ p ∈ f.1.support, (f.1 p : ℝ) * Real.log p

lemma occNumber_pos (f : PrimeOccupation) : 0 < occNumber f := by
  unfold occNumber Finsupp.prod
  exact Finset.prod_pos (fun p hp => pow_pos (f.2 p hp).pos _)

/-- **Energy is the logarithm of the encoded integer:** `E(n) = log N(n)`.

    The physical content is that a configuration's energy is not an independent quantity —
    additivity of energy over modes is exactly multiplicativity of `N` over prime powers,
    turned into a sum by `log`. -/
theorem occEnergy_eq_log_occNumber (f : PrimeOccupation) :
    occEnergy f = Real.log (occNumber f) := by
  unfold occEnergy occNumber Finsupp.prod
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (f.2 p hp).ne_zero)

/-- **Unique factorization is the state count.** The encoding `n ↦ N(n)` is precisely
    Mathlib's `Nat.factorizationEquiv`, so configurations biject with the positive integers:
    the primon gas has exactly one state per integer `N ≥ 1`. -/
theorem occNumber_eq_factorizationEquiv (f : PrimeOccupation) :
    occNumber f = (Nat.factorizationEquiv.symm f : ℕ+) :=
  (Nat.factorizationEquiv_symm_apply_coe f).symm

/-- **The Boltzmann weight of a configuration is `N^{-s}`.** Immediate from
    `occEnergy_eq_log_occNumber`, and the step that makes the partition sum a Dirichlet
    series rather than merely a sum of exponentials. -/
theorem boltzmann_eq_inv_cpow (s : ℂ) (f : PrimeOccupation) :
    Complex.exp (-s * ((occEnergy f : ℝ) : ℂ)) = 1 / (occNumber f : ℂ) ^ s := by
  have hpos : (0:ℝ) < (occNumber f : ℝ) := by exact_mod_cast occNumber_pos f
  have hne : ((occNumber f : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (occNumber_pos f).ne'
  rw [occEnergy_eq_log_occNumber, Complex.cpow_def_of_ne_zero hne, one_div, ← Complex.exp_neg]
  congr 1
  have hlog : Complex.log ((occNumber f : ℕ) : ℂ)
      = ((Real.log ((occNumber f : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hpos.le]
  rw [hlog]
  ring

/-- **The primon-gas partition function is the Riemann zeta function.**

    `∑_{configurations} e^{-sE(n)} = ζ(s)` for `Re s > 1`.

    This is the occupation-basis counterpart of `GppPrimeGas.partition_eq_riemannZeta`,
    which gives the Euler-product form. The two are the standard sum/product pair, and
    neither is derived from the other here: the product side is Mathlib's Euler product,
    this side is unique factorization plus a reindexing.

    `Re s > 1` is the half-plane of absolute convergence — no zero-free or critical-strip
    content is involved. -/
theorem partition_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    ∑' f : PrimeOccupation, Complex.exp (-s * ((occEnergy f : ℝ) : ℂ)) = riemannZeta s := by
  have step1 : ∑' f : PrimeOccupation, Complex.exp (-s * ((occEnergy f : ℝ) : ℂ))
      = ∑' f : PrimeOccupation, 1 / (((Nat.factorizationEquiv.symm f : ℕ+) : ℕ) : ℂ) ^ s := by
    refine tsum_congr (fun f => ?_)
    rw [boltzmann_eq_inv_cpow, occNumber_eq_factorizationEquiv]
  rw [step1]
  -- Reindex configurations by the positive integers they encode.
  rw [Nat.factorizationEquiv.symm.tsum_eq (fun n : ℕ+ => 1 / ((n : ℕ) : ℂ) ^ s)]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1 / ((n : ℕ) : ℂ) ^ s)]
  refine tsum_congr (fun n => ?_)
  push_cast
  ring

end GppPrimeFock

#print axioms GppPrimeFock.partition_eq_riemannZeta
