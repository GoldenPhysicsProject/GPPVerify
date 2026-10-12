import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Single
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Algebraic bosonic Fock space for the arithmetic bulk QFT — Track 1

This file builds the **algebraic** core of the bosonic Fock space used by the
arithmetic bulk QFT (prime-tower modes). It is Track 1 of Daniel's two-track
mandate: Track 2 (KMS-algebraic path) comes later.

## Design decisions (recorded per Daniel's rule)

* **Scalars are `ℂ`.** The Fock space is `Config ι →₀ ℂ`; creation/annihilation are
  `ℂ`-linear maps. `ℝ` would also work, but `ℂ` costs nothing extra here.
* **`Finsupp` for configurations.** `Config ι := ι →₀ ℕ` (finitely supported
  occupation functions). `Finsupp` gives `single`, `update`, `linearCombination`,
  and the induction principle, which together make the CCR proofs mechanical.
* **Unnormalized (Bargmann) basis.** `a†_i` adds one quantum with coefficient `1`;
  `a_i` removes one quantum with the standard linear coefficient `n`
  (we work over `ℂ` linearly, so the eigenvalue statements use `n`, not `√n`;
  no square roots appear anywhere).
  The `√n` normalization belongs to the Hilbert-space completion (out of scope).
* **Out of scope (explicit):** Hilbert completion, unbounded-operator domains,
  self-adjointness, and the analytic CCR on a dense domain. Everything here is
  purely algebraic: finite linear combinations and finitely supported functions.

## Contents

* `Config`, `Fock`, `vacuum`, `unitOcc`, `predOcc`
* `create`, `annihilate` and their action on basis vectors
* Canonical commutation relations:
  `comm_create_annihilate`, `comm_create_annihilate_ne`,
  `comm_annihilate_annihilate`, `comm_create_create`
* `numberOp`, `weightedNumber` and their eigenvalues
* Prime-tower identification: `toNat`, `fromNat`, `fromNat_toNat`,
  `toNat_fromNat`, and the `log n` eigenvalue
  (`weightedNumber_log_eigenvalue`).

Epistemic label: **LEAN-CHECKED** (kernel, zero `sorry`, standard axioms only).

## Relation to GPPVerify main (review note, 2026-10-12)

* The prime-tower maps `toNat`/`fromNat` overlap `GppPrimeFock.ofFock`/`toFock`
  (`RiemannHypothesis/PrimeFockFactorization.lean`); the statements are kept
  here in the unnormalized-Bargmann presentation used by the CCR proofs.
* `sum_mul_log_eq_log_toNat` overlaps `GppPrimeBulkQFTPaper.energy_eq_log`
  (PR #297); proved independently here from `Nat.factorization`.
* The CCR algebra (`comm_create_annihilate` and companions) is new:
  GPPVerify main has no creation/annihilation operator algebra.
-/

open Finsupp

namespace ArithmeticFock

variable {ι : Type*} [DecidableEq ι]

/-- Occupation-number configurations: finitely supported functions `ι → ℕ`. -/
abbrev Config (ι : Type*) [DecidableEq ι] := ι →₀ ℕ

/-- Algebraic Fock space: finite complex linear combinations of configurations. -/
abbrev Fock (ι : Type*) [DecidableEq ι] := Config ι →₀ ℂ

/-- The vacuum vector: the empty configuration with coefficient 1. -/
noncomputable def vacuum : Fock ι := Finsupp.single 0 1

/-- The configuration with a single quantum in mode `i`. -/
noncomputable def unitOcc (i : ι) : Config ι := Finsupp.single i 1

/-- Predecessor configuration: remove one quantum from mode `i`
(truncated subtraction; only used when `c i ≠ 0`). -/
noncomputable def predOcc (i : ι) (c : Config ι) : Config ι := c.update i (c i - 1)

/-- Creation operator: `a†_i |c⟩ = |c + e_i⟩`. -/
noncomputable def create (i : ι) : Fock ι →ₗ[ℂ] Fock ι :=
  Finsupp.linearCombination ℂ fun c : Config ι => Finsupp.single (c + unitOcc i) 1

/-- Annihilation operator: `a_i |c⟩ = (c i) • |predOcc i c⟩` (zero if `c i = 0`). -/
noncomputable def annihilate (i : ι) : Fock ι →ₗ[ℂ] Fock ι :=
  Finsupp.linearCombination ℂ fun c : Config ι =>
    if c i = 0 then 0 else (c i : ℂ) • Finsupp.single (predOcc i c) 1

@[simp] theorem create_single (i : ι) (c : Config ι) (z : ℂ) :
    create i (Finsupp.single c z) = z • Finsupp.single (c + unitOcc i) 1 :=
  Finsupp.linearCombination_single _ _ _

@[simp] theorem annihilate_single (i : ι) (c : Config ι) (z : ℂ) :
    annihilate i (Finsupp.single c z)
      = z • (if c i = 0 then 0 else (c i : ℂ) • Finsupp.single (predOcc i c) 1) :=
  Finsupp.linearCombination_single _ _ _

@[simp] theorem create_single_one (i : ι) (c : Config ι) :
    create i (Finsupp.single c 1) = Finsupp.single (c + unitOcc i) 1 := by
  rw [create_single, one_smul]

@[simp] theorem annihilate_single_one (i : ι) (c : Config ι) :
    annihilate i (Finsupp.single c 1)
      = (if c i = 0 then 0 else (c i : ℂ) • Finsupp.single (predOcc i c) 1) := by
  rw [annihilate_single, one_smul]

/-- Two linear maps agreeing on all `single c 1` are equal. -/
theorem ext_on_config {T S : Fock ι →ₗ[ℂ] Fock ι}
    (h : ∀ c : Config ι, T (Finsupp.single c 1) = S (Finsupp.single c 1)) :
    T = S := by
  have hsb : ∀ (a : Config ι) (b : ℂ),
      Finsupp.single a b = b • Finsupp.single a (1:ℂ) := by
    intro a b
    apply Finsupp.ext; intro k
    by_cases hk : k = a
    · subst hk
      simp [Finsupp.single_apply, Finsupp.smul_apply]
    · simp [Finsupp.single_apply, hk, Finsupp.smul_apply]
  apply LinearMap.ext; intro x
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
      rw [hsb a b, map_add, map_add, map_smul, map_smul, h a, ih]

/-- Pointwise description of `predOcc`. -/
theorem predOcc_apply (i : ι) (c : Config ι) (k : ι) :
    predOcc i c k = if k = i then c i - 1 else c k := by
  simp [predOcc, Finsupp.update_apply]

/-- Pointwise description of `unitOcc`. -/
theorem unitOcc_apply (i k : ι) : unitOcc i k = if k = i then 1 else 0 := by
  simp only [unitOcc, Finsupp.single_apply, eq_comm (a := i) (b := k)]

/-- Removing a quantum right after adding it recovers the configuration. -/
theorem predOcc_add_unitOcc (i : ι) (c : Config ι) : predOcc i (c + unitOcc i) = c := by
  apply Finsupp.ext; intro k
  rw [predOcc_apply]
  by_cases h : k = i
  · rw [h, if_pos rfl]
    have e : (c + unitOcc i) i = c i + 1 := by
      rw [Finsupp.add_apply, unitOcc_apply, if_pos rfl]
    omega
  · rw [if_neg h, Finsupp.add_apply, unitOcc_apply, if_neg h, add_zero]

/-- `predOcc i` commutes with adding a quantum in a *different* mode. -/
theorem predOcc_add_unitOcc_ne {i j : ι} (hij : i ≠ j) (c : Config ι) :
    predOcc i (c + unitOcc j) = predOcc i c + unitOcc j := by
  apply Finsupp.ext; intro k
  have h1 : (c + unitOcc j) i = c i := by
    rw [Finsupp.add_apply, unitOcc_apply, if_neg hij, add_zero]
  have h2 : unitOcc j i = 0 := by
    rw [unitOcc_apply, if_neg hij]
  rw [predOcc_apply]
  by_cases h : k = i
  · subst h
    rw [if_pos rfl, h1, Finsupp.add_apply, predOcc_apply, if_pos rfl, h2, add_zero]
  · rw [if_neg h, Finsupp.add_apply, Finsupp.add_apply, predOcc_apply, if_neg h]

/-- Adding a quantum after removing it recovers the configuration (needs `c i ≠ 0`). -/
theorem unitOcc_add_predOcc {i : ι} {c : Config ι} (hci : c i ≠ 0) :
    predOcc i c + unitOcc i = c := by
  apply Finsupp.ext; intro k
  by_cases h : k = i
  · subst h
    rw [Finsupp.add_apply, predOcc_apply, if_pos rfl, unitOcc_apply, if_pos rfl]
    omega
  · rw [Finsupp.add_apply, predOcc_apply, if_neg h, unitOcc_apply, if_neg h, add_zero]

/-- `predOcc` in different modes commutes. -/
theorem predOcc_comm {i j : ι} (hij : i ≠ j) (c : Config ι) :
    predOcc i (predOcc j c) = predOcc j (predOcc i c) := by
  have h1 : (predOcc j c) i = c i := by rw [predOcc_apply, if_neg hij]
  have h2 : (predOcc i c) j = c j := by rw [predOcc_apply, if_neg (Ne.symm hij)]
  apply Finsupp.ext; intro k
  by_cases hki : k = i
  · subst hki
    rw [predOcc_apply, if_pos rfl, h1, predOcc_apply, if_neg hij,
      predOcc_apply, if_pos rfl]
  · by_cases hkj : k = j
    · subst hkj
      rw [predOcc_apply, if_neg hki, predOcc_apply, if_pos rfl,
        predOcc_apply, if_pos rfl, h2]
    · rw [predOcc_apply, if_neg hki, predOcc_apply, if_neg hkj,
        predOcc_apply, if_neg hkj, predOcc_apply, if_neg hki]

/-- CCR, same mode: `[a_i, a†_i] = 1`. -/
theorem comm_create_annihilate (i : ι) :
    annihilate i ∘ₗ create i - create i ∘ₗ annihilate i = LinearMap.id := by
  apply ext_on_config
  intro c
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  have h1 : (c + unitOcc i) i ≠ 0 := by
    have e : (c + unitOcc i) i = c i + 1 := by
      rw [Finsupp.add_apply, unitOcc_apply, if_pos rfl]
    omega
  have e2 : ((c + unitOcc i) i : ℂ) = (c i : ℂ) + 1 := by
    have e : (c + unitOcc i) i = c i + 1 := by
      rw [Finsupp.add_apply, unitOcc_apply, if_pos rfl]
    rw [e]; push_cast; ring
  have A1 : annihilate i (create i (Finsupp.single c 1))
      = ((c i : ℂ) + 1) • Finsupp.single c 1 := by
    rw [create_single_one, annihilate_single_one, if_neg h1, e2, predOcc_add_unitOcc]
  have A2 : create i (annihilate i (Finsupp.single c 1))
      = (c i : ℂ) • Finsupp.single c 1 := by
    rw [annihilate_single_one]
    by_cases hci : c i = 0
    · rw [if_pos hci, map_zero]
      have e : (c i : ℂ) = 0 := by exact_mod_cast hci
      rw [e, zero_smul]
    · rw [if_neg hci, map_smul, create_single_one, unitOcc_add_predOcc hci]
  rw [A1, A2, add_smul, one_smul, add_sub_cancel_left]

/-- CCR, different modes: `[a_i, a†_j] = 0` for `i ≠ j`. -/
theorem comm_create_annihilate_ne {i j : ι} (hij : i ≠ j) :
    annihilate i ∘ₗ create j - create j ∘ₗ annihilate i = 0 := by
  apply ext_on_config
  intro c
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  have e1 : (c + unitOcc j) i = c i := by
    rw [Finsupp.add_apply, unitOcc_apply, if_neg hij, add_zero]
  have A1 : annihilate i (create j (Finsupp.single c 1))
      = (if c i = 0 then 0 else (c i : ℂ) • Finsupp.single (predOcc i c + unitOcc j) 1) := by
    rw [create_single_one, annihilate_single_one, e1, predOcc_add_unitOcc_ne hij]
  have A2 : create j (annihilate i (Finsupp.single c 1))
      = (if c i = 0 then 0 else (c i : ℂ) • Finsupp.single (predOcc i c + unitOcc j) 1) := by
    rw [annihilate_single_one]
    by_cases hci : c i = 0
    · rw [if_pos hci, map_zero, if_pos hci]
    · rw [if_neg hci, map_smul, create_single_one, if_neg hci]
  rw [A1, A2, sub_self]

/-- Double annihilation in different modes, symmetric form. -/
theorem annihilate_annihilate_single {i j : ι} (hij : i ≠ j) (c : Config ι) :
    annihilate i (annihilate j (Finsupp.single c 1))
      = if c i = 0 ∨ c j = 0 then 0
        else ((c i : ℂ) * (c j : ℂ)) • Finsupp.single (predOcc i (predOcc j c)) 1 := by
  have hpi : (predOcc j c) i = c i := by
    rw [predOcc_apply, if_neg hij]
  rw [annihilate_single_one]
  by_cases hcj : c j = 0
  · rw [if_pos hcj, map_zero, if_pos (Or.inr hcj)]
  · rw [if_neg hcj, map_smul, annihilate_single_one, hpi]
    by_cases hci : c i = 0
    · rw [if_pos hci, smul_zero, if_pos (Or.inl hci)]
    · have hne : ¬(c i = 0 ∨ c j = 0) := by simp [hci, hcj]
      rw [if_neg hci, if_neg hne, ← mul_smul, mul_comm (c j : ℂ) (c i : ℂ)]

/-- CCR: `[a_i, a_j] = 0`. -/
theorem comm_annihilate_annihilate (i j : ι) :
    annihilate i ∘ₗ annihilate j - annihilate j ∘ₗ annihilate i = 0 := by
  apply ext_on_config
  intro c
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  by_cases hij : i = j
  · subst hij; rw [sub_self]
  · rw [annihilate_annihilate_single hij,
        annihilate_annihilate_single (Ne.symm hij),
        predOcc_comm hij, mul_comm (c i : ℂ) (c j : ℂ)]
    simp only [or_comm, sub_self]

/-- Double creation. -/
theorem create_create_single (i j : ι) (c : Config ι) :
    create i (create j (Finsupp.single c 1))
      = Finsupp.single (c + unitOcc i + unitOcc j) 1 := by
  rw [create_single_one, create_single_one]
  congr 1
  abel

/-- CCR: `[a†_i, a†_j] = 0`. -/
theorem comm_create_create (i j : ι) :
    create i ∘ₗ create j - create j ∘ₗ create i = 0 := by
  apply ext_on_config
  intro c
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  rw [create_create_single, create_create_single]
  have e : (c + unitOcc j + unitOcc i : Config ι) = c + unitOcc i + unitOcc j := by abel
  rw [e, sub_self]

/-- Total number operator `N = Σ_i a†_i a_i` (diagonal on configurations). -/
noncomputable def numberOp : Fock ι →ₗ[ℂ] Fock ι :=
  Finsupp.linearCombination ℂ fun c : Config ι =>
    (c.sum fun _ r => (r : ℂ)) • Finsupp.single c 1

@[simp] theorem numberOp_single (c : Config ι) (z : ℂ) :
    numberOp (Finsupp.single c z)
      = z • ((c.sum fun _ r => (r : ℂ)) • Finsupp.single c 1) :=
  Finsupp.linearCombination_single _ _ _

/-- Eigenvalue of `N` on a basis configuration. -/
theorem numberOp_eigenvalue (c : Config ι) :
    numberOp (Finsupp.single c 1)
      = (c.sum fun _ r => (r : ℂ)) • Finsupp.single c 1 := by
  rw [numberOp_single, one_smul]

/-- Weighted number operator `Σ_i w_i a†_i a_i` (diagonal, real weights). -/
noncomputable def weightedNumber (w : ι → ℝ) : Fock ι →ₗ[ℂ] Fock ι :=
  Finsupp.linearCombination ℂ fun c : Config ι =>
    (((c.sum fun i r => (r : ℝ) * w i) : ℝ):ℂ) • Finsupp.single c 1

@[simp] theorem weightedNumber_single (w : ι → ℝ) (c : Config ι) (z : ℂ) :
    weightedNumber w (Finsupp.single c z)
      = z • ((((c.sum fun i r => (r : ℝ) * w i) : ℝ):ℂ) • Finsupp.single c 1) :=
  Finsupp.linearCombination_single _ _ _

/-- Eigenvalue of the weighted number operator on a basis configuration. -/
theorem weightedNumber_eigenvalue (w : ι → ℝ) (c : Config ι) :
    weightedNumber w (Finsupp.single c 1)
      = ((((c.sum fun i r => (r : ℝ) * w i) : ℝ):ℂ)) • Finsupp.single c 1 := by
  rw [weightedNumber_single, one_smul]

/-! ## Prime-tower identification

Configurations over prime modes are in bijection with positive naturals via
`n = ∏ p ^ (c p)` (unique factorization). The weighted number operator with
weights `log p` then acts as multiplication by `log n`.
-/

/-- Embedding of `Nat.Primes` into naturals (used for the prime tower). -/
def primeEmb : Nat.Primes ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩

/-- `toNat`: configuration ↦ positive natural via prime factorization. -/
noncomputable def toNat (c : Config Nat.Primes) : ℕ :=
  c.prod fun p r => (p : ℕ) ^ r

/-- `fromNat`: positive natural ↦ occupation configuration (prime exponents). -/
noncomputable def fromNat (n : ℕ) : Config Nat.Primes :=
  if n = 0 then 0 else Finsupp.subtypeDomain (fun p => p.Prime) (Nat.factorization n)

theorem toNat_ne_zero (c : Config Nat.Primes) : toNat c ≠ 0 := by
  unfold toNat
  show (∏ p ∈ c.support, (p : ℕ) ^ c p) ≠ 0
  rw [Finset.prod_ne_zero_iff]
  intro p _
  exact pow_ne_zero _ p.property.ne_zero

/-- Round trip: configuration → natural → configuration. -/
theorem fromNat_toNat (c : Config Nat.Primes) : fromNat (toNat c) = c := by
  have hne : toNat c ≠ 0 := toNat_ne_zero c
  -- Key: factorization of `toNat c` is `c` embedded into `ℕ →₀ ℕ`.
  have key : (toNat c).factorization = Finsupp.embDomain primeEmb c := by
    have hsupp : ∀ m ∈ (Finsupp.embDomain primeEmb c).support, m.Prime := by
      intro m hm
      rw [Finsupp.support_embDomain] at hm
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hm
      exact q.property
    have hprod : (Finsupp.embDomain primeEmb c).prod (· ^ ·) = toNat c := by
      rw [show (Finsupp.embDomain primeEmb c).prod (· ^ ·)
          = ∏ m ∈ (Finsupp.embDomain primeEmb c).support,
              m ^ ((Finsupp.embDomain primeEmb c) m) from rfl,
        show toNat c = ∏ p ∈ c.support, (p:ℕ) ^ c p from rfl,
        Finsupp.support_embDomain,
        Finset.prod_map]
      apply Finset.prod_congr rfl
      intro q _
      show (primeEmb q) ^ ((Finsupp.embDomain primeEmb c) (primeEmb q)) = (q : ℕ) ^ c q
      rw [Finsupp.embDomain_apply_self]
      rfl
    have h2 := Nat.prod_pow_factorization_eq_self hsupp
    rw [hprod] at h2
    exact h2
  unfold fromNat
  rw [if_neg hne, key]
  apply Finsupp.ext; intro q
  rw [Finsupp.subtypeDomain_apply]
  show (Finsupp.embDomain primeEmb c) (primeEmb q) = c q
  rw [Finsupp.embDomain_apply_self]

/-- Helper: prod over the prime subtype equals prod over `ℕ`. -/
theorem prod_subtypeDomain_prime {f : ℕ →₀ ℕ} (hsupp : ∀ m ∈ f.support, m.Prime) :
    (Finsupp.subtypeDomain (fun m => m.Prime) f).prod (fun q r => (q : ℕ) ^ r)
      = f.prod (· ^ ·) := by
  rw [show (Finsupp.subtypeDomain (fun m => m.Prime) f).prod (fun q r => (q : ℕ) ^ r)
      = ∏ q ∈ (Finsupp.subtypeDomain (fun m => m.Prime) f).support,
        (q : ℕ) ^ ((Finsupp.subtypeDomain (fun m => m.Prime) f) q) from rfl,
    show f.prod (· ^ ·) = ∏ m ∈ f.support, m ^ f m from rfl,
    Finsupp.support_subtypeDomain]
  apply Finset.prod_bij (fun q _ => (q.val : ℕ))
  · intro q hq
    exact Finset.mem_subtype.mp hq
  · intro q _ r _ hqr
    exact Subtype.val_injective hqr
  · intro m hm
    exact ⟨⟨m, hsupp m hm⟩, Finset.mem_subtype.mpr hm, rfl⟩
  · intro q _
    rw [Finsupp.subtypeDomain_apply]

/-- Round trip: natural → configuration → natural (for `n ≠ 0`). -/
theorem toNat_fromNat {n : ℕ} (hn : n ≠ 0) : toNat (fromNat n) = n := by
  unfold fromNat
  rw [if_neg hn]
  have hsupp : ∀ m ∈ (Nat.factorization n).support, m.Prime := by
    intro m hm
    rw [Nat.support_factorization] at hm
    exact Nat.prime_of_mem_primeFactors hm
  have h1 := prod_subtypeDomain_prime hsupp
  have hfac : (Nat.factorization n).prod (· ^ ·) = n :=
    Nat.prod_factorization_pow_eq_self hn
  unfold toNat
  rw [h1, hfac]

/-- Real identity: `∑_p (c p) * log p = log (∏ p^(c p))`. -/
theorem sum_mul_log_eq_log_toNat (c : Config Nat.Primes) :
    c.sum (fun i r => (r : ℝ) * Real.log ((i : ℕ):ℝ)) = Real.log (toNat c) := by
  have hpos : ∀ i ∈ c.support, (0:ℝ) < (((i : ℕ):ℝ)) ^ c i := by
    intro i _
    apply pow_pos
    have h2 : (2:ℕ) ≤ (i : ℕ) := i.property.two_le
    have h2r : (2:ℝ) ≤ (((i : ℕ)):ℝ) := by exact_mod_cast h2
    linarith
  rw [show c.sum (fun i r => (r:ℝ) * Real.log ((i:ℕ):ℝ))
      = ∑ i ∈ c.support, (c i : ℝ) * Real.log (((i : ℕ)):ℝ) from rfl,
    show toNat c = ∏ i ∈ c.support, ((i:ℕ)) ^ c i from rfl,
    Nat.cast_prod]
  simp only [Nat.cast_pow]
  rw [Real.log_prod (fun i hi => ne_of_gt (hpos i hi))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_pow]

/-- The `log p`-weighted number operator acts as multiplication by `log n`. -/
theorem weightedNumber_log_eigenvalue (c : Config Nat.Primes) :
    weightedNumber (fun p : Nat.Primes => Real.log ((p : ℕ):ℝ)) (Finsupp.single c (1:ℂ))
      = (((Real.log (toNat c)):ℝ):ℂ) • Finsupp.single c (1:ℂ) := by
  rw [weightedNumber_eigenvalue]
  congr 1
  rw [sum_mul_log_eq_log_toNat]

end ArithmeticFock
