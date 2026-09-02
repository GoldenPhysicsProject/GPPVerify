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

Everything else is a consequence of those two, in two groups.

**The spectrum.** `occEnergy_injective` — distinct configurations have distinct energies, so
the occupation-basis spectrum is **non-degenerate**: exactly one state per level, no
multiplicity anywhere. `occEnergy_range` — the set of energies is exactly `{log N : N ≥ 1}`,
equivalently `exp_occEnergy_range`: exponentiating the spectrum gives precisely the positive
integers, which is the sense in which the spectrum is "integer". Both directions are needed
and both are unique factorization read one way and then the other — injectivity is
uniqueness of the factorization, surjectivity is existence of it.

**The partition function.** `e^{-sE(n)} = N^{-s}` (`boltzmann_eq_inv_cpow`), so the partition
sum is `∑_{N ≥ 1} N^{-s}`, which is `ζ(s)` on `Re s > 1`.

The statistical-mechanical reading — that this is a free bosonic gas whose modes are the
primes, whose states are the positive integers, and whose partition function is `ζ` — is a
**dictionary**, as in `PrimeGasPartition.lean`. Nothing here constructs a Fock space, a
Hamiltonian, or a Hilbert space; `dΓ(L)` does not appear. In particular `occEnergy_injective`
and `occEnergy_range` describe the **occupation-basis labels**, not the spectrum of a
self-adjoint operator: no operator is defined, so no spectral theorem is invoked and no claim
is made that the label set equals `spec(H_B)` for any `H_B` in this tree. What is
machine-checked is the combinatorial identity the dictionary rests on. Reporting this as "the
prime Fock Hamiltonian is formalized" would overstate it.

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

/-! ### The occupation-basis spectrum

`occNumber` is a bijection from configurations onto the positive integers — injective by
uniqueness of prime factorization, surjective by its existence. Transported through `log`,
that says the energy levels are non-degenerate and are exactly `{log N : N ≥ 1}`.
-/

/-- Every positive integer is realised: `factorizationEquiv m` is the configuration
    encoding `m`. This is *existence* of a prime factorization. -/
theorem occNumber_factorizationEquiv (m : ℕ+) :
    occNumber (Nat.factorizationEquiv m) = (m : ℕ) := by
  rw [occNumber_eq_factorizationEquiv, Equiv.symm_apply_apply]

/-- Distinct configurations encode distinct integers. This is *uniqueness* of the prime
    factorization, in the form the spectrum needs. -/
theorem occNumber_injective : Function.Injective occNumber := by
  intro a b hab
  rw [occNumber_eq_factorizationEquiv a, occNumber_eq_factorizationEquiv b] at hab
  have h2 : Nat.factorizationEquiv.symm a = Nat.factorizationEquiv.symm b :=
    PNat.coe_injective (by exact_mod_cast hab)
  simpa using congrArg Nat.factorizationEquiv h2

/-- The configurations encode **exactly** the positive integers. -/
theorem occNumber_range : Set.range occNumber = {n : ℕ | 0 < n} := by
  ext n
  constructor
  · rintro ⟨f, rfl⟩
    exact occNumber_pos f
  · intro hn
    exact ⟨Nat.factorizationEquiv ⟨n, hn⟩, occNumber_factorizationEquiv ⟨n, hn⟩⟩

/-- **The occupation-basis spectrum is non-degenerate.** Distinct configurations have
    distinct energies — exactly one state per level, no multiplicity anywhere.

    Physically this is the statement that the primon gas has no accidental degeneracy: the
    additive structure `∑_p n_p log p` never collides, because `log` is injective on the
    positive integers and the integers are uniquely factorable. It is the reason the level
    counting of the gas is the divisor-free count `#{N ≤ x} = ⌊x⌋` rather than something
    with multiplicities. -/
theorem occEnergy_injective : Function.Injective occEnergy := by
  intro a b hab
  rw [occEnergy_eq_log_occNumber, occEnergy_eq_log_occNumber] at hab
  refine occNumber_injective ?_
  have ha : (0:ℝ) < (occNumber a : ℝ) := by exact_mod_cast occNumber_pos a
  have hb : (0:ℝ) < (occNumber b : ℝ) := by exact_mod_cast occNumber_pos b
  exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) hab

/-- **The spectrum is exactly `{log N : N ≥ 1}`.** Nothing is missing and nothing extra
    appears. -/
theorem occEnergy_range :
    Set.range occEnergy = Real.log '' {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = n} := by
  ext E
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨(occNumber f : ℝ), ⟨occNumber f, occNumber_pos f, rfl⟩,
      (occEnergy_eq_log_occNumber f).symm⟩
  · rintro ⟨x, ⟨n, hn, rfl⟩, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℕ+, (m : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
    exact ⟨Nat.factorizationEquiv m, by
      rw [occEnergy_eq_log_occNumber, occNumber_factorizationEquiv]⟩

/-- **The spectrum is "integer" in the only sense that is literally true:** exponentiating
    it gives exactly the positive integers.

    The energies themselves are logarithms, not integers — `occEnergy_range` says so. What
    is integral is `e^{E}`, which is the state's occupation number `N`. Stating it this way
    keeps the claim checkable rather than resting on a choice of units. -/
theorem exp_occEnergy_range :
    Set.range (fun f => Real.exp (occEnergy f)) = {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = n} := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨occNumber f, occNumber_pos f, ?_⟩
    dsimp only
    rw [occEnergy_eq_log_occNumber, Real.exp_log]
    exact_mod_cast occNumber_pos f
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℕ+, (m : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
    refine ⟨Nat.factorizationEquiv m, ?_⟩
    dsimp only
    rw [occEnergy_eq_log_occNumber, occNumber_factorizationEquiv, Real.exp_log]
    exact_mod_cast m.pos

/-! ### The partition function -/

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

#print axioms GppPrimeFock.occEnergy_injective
#print axioms GppPrimeFock.occEnergy_range
#print axioms GppPrimeFock.exp_occEnergy_range
#print axioms GppPrimeFock.partition_eq_riemannZeta
