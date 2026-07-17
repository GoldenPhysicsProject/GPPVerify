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
* `logPrime_lattice_injective` — faithfulness of the prime chart (stated, one
  documented `sorry`): `{log p}` is Z-linearly independent — unique factorization in
  log coordinates. This is what makes the transported Gram data a faithful copy (no two
  prime-power rungs collide). PROVABLE with current Mathlib — see the proof plan in the
  docstring; deferred to its own thread so this file's other proofs stay kernel-checked.

**Honest boundary**: transport is *free* — it holds for arbitrary weights `w` and needs
no primality. The arithmetic enters only through faithfulness (the sorry above) and
through what is transported (the archimedean positivity floor, Thread L rung 0, still
carried as a named hypothesis pending the Connes-Consani formalization). Nothing here
is uniform in the rung parameter; by `rh_iff_weil_pairedForm_nonneg` the uniform
statement is equivalent to RH and stays open and named.
-/

namespace GppTransport

open Finset

/-- Positive-type on an arbitrary additive commutative group: every finite Gram matrix
    `[P(x_i - x_j)]` is PSD. On `R` this is definitionally
    `GppHaarPositivityWeil.PositiveType`. -/
def PositiveTypeOn {G : Type*} [AddCommGroup G] (P : G → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
          (starRingEnd ℂ (c i)) * c j * (P (x i - x j) : ℂ)).re

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

/-- **Faithfulness of the prime chart** (stated; ONE documented `sorry`): the map
    `k |-> ∑_{p in S} k_p * log p` on `Z^S` kills only `k = 0` — the Z-linear
    independence of `{log p : p prime}`, i.e. unique factorization read in log
    coordinates. This upgrades `truncated_transport` from "a positive-type function on
    the chart" to "a faithful copy of the S-truncated Gram data": distinct prime-power
    rungs never collide, so the transported matrices are genuine submatrices of the
    `R`-side data.

    PROVABLE WITH CURRENT MATHLIB — this is not an open problem and not a Mathlib gap.
    Proof plan: split `k` into positive and negative parts `a b : S → ℕ` with disjoint
    supports; the hypothesis becomes `Real.log (∏ p^(a_p)) = Real.log (∏ p^(b_p))`;
    `Real.log` is injective on `[1, ∞)` so `∏ p^(a_p) = ∏ p^(b_p)` in `ℕ`; comparing
    `Nat.factorization` (via `Nat.Prime.factorization_pow` and `Nat.factorization_mul`
    on the positive products) forces `a = b`, and disjoint supports force both to
    vanish, so `k = 0`. Deferred to its own thread (see FORMALIZATION_PLAN) to keep
    this PR's other proofs kernel-checked. -/
theorem logPrime_lattice_injective {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (k : S → ℤ) (hk : ∑ p : S, (k p : ℝ) * Real.log ((p : ℕ) : ℝ) = 0) :
    k = 0 := by
  sorry

end GppTransport

-- Summary checks
#check @GppTransport.PositiveTypeOn
#check @GppTransport.positiveTypeOn_comp_addMonoidHom
#check @GppTransport.truncated_transport
#check @GppTransport.logPrime_lattice_injective
