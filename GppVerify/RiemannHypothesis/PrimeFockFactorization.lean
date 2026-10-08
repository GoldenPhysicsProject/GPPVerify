import GppVerify.RiemannHypothesis.EulerFactorizationCoherent
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction

/-!
# The multi-prime Fock factorization `ℓ²(ℕ₊) ≅ ⊗_p ℓ²(ℕ₀)` at the level of occupation numbers

Unique factorization identifies a positive integer `n` with its occupation numbers
`k_p = v_p(n)`, a finitely supported function on the primes. This file records the exact content of
that identification for the arithmetic Hardy space, without building the infinite tensor product:

* `ofFock`, `toFock` and `ofFock_toFock`, `toFock_ofFock`: a sequence on `n ≥ 1` is the same thing as a
  function of the occupation numbers (`ℕ →₀ ℕ` supported on primes); the two maps are inverse.
* `annihilate_fock`: the Hecke operator `A_p f(n) = f(pn)` is, in occupation numbers, the lowering shift
  `k ↦ k + e_p` in the single mode `p` (`factorization (p n) = factorization n + e_p`).
* `numberOp p`: the occupation number `N_p f(n) = v_p(n) f(n)`, with the bosonic relations
  `[A_p, N_p] = A_p` and `[A_p, N_q] = 0` for `q ≠ p` prime (pointwise at `n ≠ 0`).
* `coh_fock`: the coherent vector is the product vector, `e_z(n) = ∏_p (p^{-1/2-z})^{v_p(n)}`
  (`eigenvalue`), i.e. a pure tensor of single-mode geometric vectors.

## Scope

**Not formalized:** the infinite tensor product Hilbert space itself, and the isometric isomorphism onto
it (only the norm identity of `EulerFactorizationCoherent` and the pointwise occupation-number
structure). These are bookkeeping facts about unique factorization; they do not locate zeros. No RH claim.
-/

open GppArithmeticHardy

namespace GppPrimeFock

/-- Occupation-number configurations: finitely supported on primes. -/
def IsFock (k : ℕ →₀ ℕ) : Prop := ∀ p ∈ k.support, p.Prime

open Classical in
/-- A sequence on `ℕ` as a function of occupation numbers (zero off prime-supported configurations). -/
noncomputable def toFock (f : ℕ → ℂ) (k : ℕ →₀ ℕ) : ℂ :=
  if IsFock k then f (k.prod (· ^ ·)) else 0

/-- A function of occupation numbers as a sequence (zero at `n = 0`). -/
noncomputable def ofFock (g : (ℕ →₀ ℕ) → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else g n.factorization

theorem ofFock_toFock (f : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) : ofFock (toFock f) n = f n := by
  have hf : IsFock n.factorization := fun p hp => Nat.prime_of_mem_primeFactors hp
  simp [ofFock, toFock, hn, hf, Nat.prod_factorization_pow_eq_self hn]

theorem toFock_ofFock (g : (ℕ →₀ ℕ) → ℂ) (k : ℕ →₀ ℕ) (hk : IsFock k) :
    toFock (ofFock g) k = g k := by
  have hn : k.prod (· ^ ·) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hk p hp).ne_zero
  have hfac : (k.prod (· ^ ·)).factorization = k := Nat.prod_pow_factorization_eq_self hk
  simp [toFock, ofFock, hk, hn, hfac]

/-- **Annihilation is the single-mode lowering shift.** -/
theorem annihilate_fock (p : ℕ) (hp : p.Prime) (g : (ℕ →₀ ℕ) → ℂ) (n : ℕ) (hn : n ≠ 0) :
    annihilate p (ofFock g) n = ofFock (fun k => g (k + Finsupp.single p 1)) n := by
  have hpn : p * n ≠ 0 := mul_ne_zero hp.ne_zero hn
  have hf : (p * n).factorization = n.factorization + Finsupp.single p 1 := by
    rw [Nat.factorization_mul hp.ne_zero hn, hp.factorization, add_comm]
  simp [annihilate, ofFock, hn, hpn, hf]

/-- The occupation-number operator of the mode `p`. -/
def numberOp (p : ℕ) (f : ℕ → ℂ) : ℕ → ℂ := fun n => (n.factorization p : ℂ) * f n

/-- **`[A_p, N_p] = A_p`** (pointwise at `n ≠ 0`): lowering reduces the occupation by one. -/
theorem annihilate_numberOp_self (p : ℕ) (hp : p.Prime) (f : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) :
    annihilate p (numberOp p f) n - numberOp p (annihilate p f) n = annihilate p f n := by
  have hf : (p * n).factorization p = n.factorization p + 1 := by
    rw [Nat.factorization_mul hp.ne_zero hn, hp.factorization]; simp [add_comm]
  simp only [annihilate, numberOp, hf]
  push_cast; ring

/-- **`[A_p, N_q] = 0` for distinct primes**: different modes commute. -/
theorem annihilate_numberOp_other (p q : ℕ) (hp : p.Prime) (hpq : p ≠ q)
    (f : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) :
    annihilate p (numberOp q f) n = numberOp q (annihilate p f) n := by
  have hf : (p * n).factorization q = n.factorization q := by
    rw [Nat.factorization_mul hp.ne_zero hn, hp.factorization]
    simp [hpq]
  simp only [annihilate, numberOp, hf]

/-- The coherent vector as a monoid homomorphism `(ℕ, ·) → (ℂ, ·)`. -/
noncomputable def cohHom (z : ℂ) : ℕ →* ℂ where
  toFun := coh z
  map_one' := by simp [coh, logC]
  map_mul' := GppEulerFactorization.coh_mul z

/-- **The coherent vector is a product vector:** `e_z(n) = ∏_p (p^{-1/2-z})^{v_p(n)}`. -/
theorem coh_fock (z : ℂ) (n : ℕ) (hn : n ≠ 0) :
    coh z n = n.factorization.prod (fun p k => eigenvalue p z ^ k) := by
  have h : coh z n = cohHom z n := rfl
  rw [h]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [map_finsuppProd]
  refine Finsupp.prod_congr fun p _ => ?_
  rw [map_pow]
  rfl

end GppPrimeFock
