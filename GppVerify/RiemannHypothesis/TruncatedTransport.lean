import GppVerify.RiemannHypothesis.HaarPositivityWeil
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# S-truncated transport: rung-level positivity on the class-group chart, no adeles

Thread T. The memo's section 6.1 transport question is blocked at the idele-class-group
level for the honest reason recorded since PR #45: idele class groups are not in
Mathlib. This file executes the finite-level workaround: the support ladder (Thread L)
proves rung N only ever sees the primes `p <= N`, so the transport target at rung N is
not the full class group but its S-truncated chart `R x Z^S` in log coordinates, with
the evaluation map `(u, k) |-> u + sum_p k_p log p`. Plain finite products — all in
Mathlib today.

* `PositiveTypeOn` — positive-type on an arbitrary additive commutative group
  (definitionally the repo's `PositiveType` when the group is `R`:
  `positiveTypeOn_real_iff` is `Iff.rfl`);
* `positiveTypeOn_comp_addMonoidHom` — Thread Q's transport seed at group level:
  positive-type pulls back along EVERY additive homomorphism;
* `truncatedLogHom` — the weighted-log chart `(u, k) |-> u + sum_i k_i * w_i` as an
  `AddMonoidHom` on `R x (i -> Z)`;
* **`truncated_transport`** — the assembly theorem: every positive-type datum on the
  `R`-factor transports to a positive-type datum on the full S-truncated chart, by ONE
  pullback. With `w_p = log p` this is rung-|S| transport;
* `logPrime_lattice_injective` — faithfulness of the prime chart, PROVED: `{log p}` is
  Z-linearly independent — unique factorization in log coordinates, via
  `Nat.factorization` comparison after splitting each coefficient into nonnegative
  parts. This is what makes the transported Gram data a faithful copy (no two
  prime-power rungs collide).

**Honest boundary**: transport is *free* — it holds for arbitrary weights `w` and needs
no primality; faithfulness (proved above) needs primality of `S`'s elements only.
The arithmetic enters through what is transported (the archimedean positivity floor,
Thread L rung 0, still carried as a named hypothesis pending the Connes-Consani
formalization). Nothing here is uniform in the rung parameter; by
`rh_iff_weil_pairedForm_nonneg` the uniform statement is equivalent to RH and stays
open and named.
-/

namespace GppTransport

open Finset
open scoped ComplexOrder

/-- Positive-type on an arbitrary additive commutative group: every finite Gram matrix
    `[P(x_i - x_j)]` is PSD. On `R` this is definitionally
    `GppHaarPositivityWeil.PositiveType`. -/
def PositiveTypeOn {G : Type*} [AddCommGroup G] (P : G → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
          (starRingEnd ℂ (c i)) * c j * (P (x i - x j) : ℂ)

/-- On `R` the group-level notion coincides definitionally with the repo's
    `PositiveType`. -/
theorem positiveTypeOn_real_iff (P : ℝ → ℝ) :
    PositiveTypeOn P ↔ GppHaarPositivityWeil.PositiveType P := Iff.rfl

/-- **Transport along any additive homomorphism** — Thread Q's seed
    (`positiveType_comp_addMonoidHom`) at group level: positive-type pulls back along
    every `φ : H →+ G`. Same one-line proof: homomorphisms preserve the difference
    structure that Gram matrices see. -/
theorem positiveTypeOn_comp_addMonoidHom {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G → ℝ} (hP : PositiveTypeOn P) (φ : H →+ G) :
    PositiveTypeOn (fun x => P (φ x)) := by
  intro n x c
  have h := hP n (fun i => φ (x i)) c
  simp only [← map_sub] at h
  exact h

/-- The truncated-lattice evaluation homomorphism `(u, k) |-> u + ∑ i, k_i * w_i`.
    With `w_p = log p` over a finite set of primes this is the log-coordinate chart of
    the S-truncated idele-class factor `R+ x prod_{p in S} p^Z` — finite products only,
    no adeles. -/
def truncatedLogHom {ι : Type*} [Fintype ι] (w : ι → ℝ) : (ℝ × (ι → ℤ)) →+ ℝ where
  toFun x := x.1 + ∑ i, (x.2 i : ℝ) * w i
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add, add_mul,
      Finset.sum_add_distrib]
    ring

/-- **The S-truncated transport theorem**: any positive-type `P` on `R` transports to a
    positive-type function on the truncated lattice `R x Z^ι` by evaluation along the
    weighted-log chart — one pullback, no idele class groups. Taking `ι = S` a finite
    set of primes and `w_p = log p`, this is rung-|S| transport: the positivity datum
    on the `R`-factor extends to the whole S-truncated class-group chart, and with the
    Schur step (`positiveType_mul_convSquare`, Thread S2) factor data multiply. -/
theorem truncated_transport {ι : Type*} [Fintype ι] (w : ι → ℝ) {P : ℝ → ℝ}
    (hP : GppHaarPositivityWeil.PositiveType P) :
    PositiveTypeOn (fun x : ℝ × (ι → ℤ) => P (x.1 + ∑ i, (x.2 i : ℝ) * w i)) :=
  positiveTypeOn_comp_addMonoidHom ((positiveTypeOn_real_iff P).mpr hP)
    (truncatedLogHom w)

/-- **Faithfulness of the prime chart**: the map `k |-> ∑_{p in S} k_p * log p` on `Z^S`
    kills only `k = 0` — the Z-linear independence of `{log p : p prime}`, i.e. unique
    factorization read in log coordinates. This upgrades `truncated_transport` from "a
    positive-type function on the chart" to "a faithful copy of the S-truncated Gram
    data": distinct prime-power rungs never collide, so the transported matrices are
    genuine submatrices of the `R`-side data.

    Proof: split each `k p` into its nonnegative/nonpositive parts `A p, B p : ℕ` (via
    `Int.toNat`, closed by `omega`); the hypothesis becomes, after grouping,
    `Real.log (∏ p^(A p)) = Real.log (∏ p^(B p))`; `Real.log` is injective on positives
    so the two products of prime powers agree as naturals; comparing `Nat.factorization`
    (`Nat.factorization_prod` + `Nat.Prime.factorization_pow`, evaluated pointwise via
    `Finsupp.applyAddHom`/`Finsupp.single_apply`/`Finset.sum_ite_eq'`) forces `A q = B q`
    at every `q ∈ S`; combined with `A q = 0 ∨ B q = 0` this forces both to vanish. -/
theorem logPrime_lattice_injective {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (k : S → ℤ) (hk : ∑ p : S, (k p : ℝ) * Real.log ((p : ℕ) : ℝ) = 0) :
    k = 0 := by
  classical
  -- extend `k` to a total function on `ℕ`, zero outside `S`
  set k' : ℕ → ℤ := fun p => if h : p ∈ S then k ⟨p, h⟩ else 0 with hk'def
  have hk'_eq : ∀ p : S, k' (p : ℕ) = k p := by
    intro p
    simp only [hk'def, dif_pos p.property]
  have hk_sum : ∑ p ∈ S, (k' p : ℝ) * Real.log (p : ℝ) = 0 := by
    rw [← Finset.sum_coe_sort S (fun p : ℕ => (k' p : ℝ) * Real.log (p : ℝ))]
    have heq : ∑ p : S, (k' (p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)
        = ∑ p : S, (k p : ℝ) * Real.log ((p : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun p _ => by rw [hk'_eq p])
    rw [heq]
    exact hk
  -- split each `k' p` into nonnegative parts `A p, B p` with `A p - B p = k' p`
  set A : ℕ → ℕ := fun p => (k' p).toNat with hAdef
  set B : ℕ → ℕ := fun p => (-(k' p)).toNat with hBdef
  have hAB : ∀ p : ℕ, (A p : ℤ) - (B p : ℤ) = k' p := by
    intro p
    simp only [hAdef, hBdef]
    omega
  have hABzero : ∀ p : ℕ, A p = 0 ∨ B p = 0 := by
    intro p
    simp only [hAdef, hBdef]
    omega
  -- rewrite the base sum as a difference of two prime-power log sums
  have hsplit : ∑ p ∈ S, (k' p : ℝ) * Real.log (p : ℝ) =
      ∑ p ∈ S, (A p : ℝ) * Real.log (p : ℝ) - ∑ p ∈ S, (B p : ℝ) * Real.log (p : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    have h : (A p : ℝ) - (B p : ℝ) = (k' p : ℝ) := by exact_mod_cast hAB p
    rw [← h]; ring
  rw [hsplit] at hk_sum
  -- each side is `log` of a natural-number product of prime powers
  have hprod : ∀ C : ℕ → ℕ, ∑ p ∈ S, (C p : ℝ) * Real.log (p : ℝ) =
      Real.log ((∏ p ∈ S, p ^ (C p) : ℕ) : ℝ) := by
    intro C
    have hcast : ((∏ p ∈ S, p ^ (C p) : ℕ) : ℝ) = ∏ p ∈ S, ((p : ℝ) ^ (C p)) := by
      push_cast; ring
    have hne : ∀ p ∈ S, ((p : ℝ) ^ (C p)) ≠ 0 := by
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).pos.ne'
      exact pow_ne_zero _ hp0
    rw [hcast, Real.log_prod hne]
    exact Finset.sum_congr rfl (fun p _ => by rw [Real.log_pow])
  rw [hprod A, hprod B, sub_eq_zero] at hk_sum
  -- both products are positive naturals; `log` is injective there, so the naturals agree
  set N : ℕ := ∏ p ∈ S, p ^ (A p) with hNdef
  set M : ℕ := ∏ p ∈ S, p ^ (B p) with hMdef
  have hNpos : 0 < N := by
    rw [hNdef]; exact Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos (A p))
  have hMpos : 0 < M := by
    rw [hMdef]; exact Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos (B p))
  have hNM : N = M := by
    have hNpos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hMpos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
    have heq := Real.log_injOn_pos (Set.mem_Ioi.mpr hNpos') (Set.mem_Ioi.mpr hMpos') hk_sum
    exact_mod_cast heq
  -- compare factorizations at each prime in `S`
  have hfact : ∀ q ∈ S, A q = B q := by
    intro q hq
    have hNfact : N.factorization q = A q := by
      have hprodneA : ∀ p ∈ S, p ^ A p ≠ 0 := fun p hp => pow_ne_zero _ (hS p hp).pos.ne'
      have hstep1 : N.factorization = ∑ p ∈ S, (p ^ A p).factorization := by
        rw [hNdef]; exact Nat.factorization_prod hprodneA
      have hstep2 : (∑ p ∈ S, (p ^ A p).factorization) q
          = ∑ p ∈ S, (p ^ A p).factorization q :=
        map_sum (Finsupp.applyAddHom q) (fun p => (p ^ A p).factorization) S
      have hstep3 : ∀ p ∈ S, (p ^ A p).factorization q = if p = q then A p else 0 := by
        intro p hp
        rw [Nat.Prime.factorization_pow (hS p hp), Finsupp.single_apply]
      calc N.factorization q = (∑ p ∈ S, (p ^ A p).factorization) q := by rw [hstep1]
        _ = ∑ p ∈ S, (p ^ A p).factorization q := hstep2
        _ = ∑ p ∈ S, (if p = q then A p else 0) := Finset.sum_congr rfl hstep3
        _ = if q ∈ S then A q else 0 := Finset.sum_ite_eq' S q A
        _ = A q := if_pos hq
    have hMfact : M.factorization q = B q := by
      have hprodneB : ∀ p ∈ S, p ^ B p ≠ 0 := fun p hp => pow_ne_zero _ (hS p hp).pos.ne'
      have hstep1 : M.factorization = ∑ p ∈ S, (p ^ B p).factorization := by
        rw [hMdef]; exact Nat.factorization_prod hprodneB
      have hstep2 : (∑ p ∈ S, (p ^ B p).factorization) q
          = ∑ p ∈ S, (p ^ B p).factorization q :=
        map_sum (Finsupp.applyAddHom q) (fun p => (p ^ B p).factorization) S
      have hstep3 : ∀ p ∈ S, (p ^ B p).factorization q = if p = q then B p else 0 := by
        intro p hp
        rw [Nat.Prime.factorization_pow (hS p hp), Finsupp.single_apply]
      calc M.factorization q = (∑ p ∈ S, (p ^ B p).factorization) q := by rw [hstep1]
        _ = ∑ p ∈ S, (p ^ B p).factorization q := hstep2
        _ = ∑ p ∈ S, (if p = q then B p else 0) := Finset.sum_congr rfl hstep3
        _ = if q ∈ S then B q else 0 := Finset.sum_ite_eq' S q B
        _ = B q := if_pos hq
    rw [← hNfact, ← hMfact, hNM]
  -- so `A`, `B` (hence `k'`) vanish on `S`, and `k = 0` follows
  funext p
  have hq : (p : ℕ) ∈ S := p.property
  have heq : A (p : ℕ) = B (p : ℕ) := hfact (p : ℕ) hq
  have hzero : A (p : ℕ) = 0 ∧ B (p : ℕ) = 0 := by
    rcases hABzero (p : ℕ) with h | h
    · exact ⟨h, by rw [← heq]; exact h⟩
    · exact ⟨by rw [heq]; exact h, h⟩
  have hk'0 : k' (p : ℕ) = 0 := by
    have hab := hAB (p : ℕ)
    have h1 := hzero.1
    have h2 := hzero.2
    omega
  rw [hk'_eq p] at hk'0
  simpa using hk'0

end GppTransport

-- Summary checks
#check @GppTransport.PositiveTypeOn
#check @GppTransport.positiveTypeOn_comp_addMonoidHom
#check @GppTransport.truncated_transport
#check @GppTransport.logPrime_lattice_injective
