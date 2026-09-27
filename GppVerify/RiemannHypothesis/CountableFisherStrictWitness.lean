import GppVerify.RiemannHypothesis.CountableFisherMomentLimit
import GppVerify.RiemannHypothesis.FiniteFisherQuantitativeWitness
import Mathlib.Tactic

/-!
# Countable Fisher strict witness bridge

This module packages the final topological step needed for strict countable
Fisher positivity. Once a fixed positive lower witness is known for all
sufficiently large finite prefixes, convergence of the mass-aware Fisher
numerator transfers that witness unchanged to the countable limit.

This deliberately separates the finite algebraic witness construction from
the analytic moment-limit passage.
-/

namespace GppCountableFisherStrictWitness

open Filter
open GppCountableFisherMomentLimit
open GppFiniteFisherMomentBridge

/-- Any eventual lower bound for the finite-prefix mass-aware Fisher numerator
survives the countable moment limit. -/
theorem fisherNumerator_infinite_ge_of_eventually_partial_ge
    (w x : ℕ → ℝ) (c : ℝ)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hge : ∀ᶠ N : ℕ in atTop,
      c ≤ fisherNumerator
        (partialMoment w x 0 N) (partialMoment w x 1 N)
        (partialMoment w x 2 N) (partialMoment w x 3 N)
        (partialMoment w x 4 N)) :
    c ≤ fisherNumerator
      (infiniteMoment w x 0) (infiniteMoment w x 1)
      (infiniteMoment w x 2) (infiniteMoment w x 3)
      (infiniteMoment w x 4) := by
  exact ge_of_tendsto
    (fisherNumerator_partial_tendsto_infinite w x h0 h1 h2 h3 h4) hge

/-- A strictly positive eventual finite-prefix witness yields strict positivity
of the countable mass-aware Fisher numerator. -/
theorem fisherNumerator_infinite_pos_of_eventually_partial_ge
    (w x : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hge : ∀ᶠ N : ℕ in atTop,
      c ≤ fisherNumerator
        (partialMoment w x 0 N) (partialMoment w x 1 N)
        (partialMoment w x 2 N) (partialMoment w x 3 N)
        (partialMoment w x 4 N)) :
    0 < fisherNumerator
      (infiniteMoment w x 0) (infiniteMoment w x 1)
      (infiniteMoment w x 2) (infiniteMoment w x 3)
      (infiniteMoment w x 4) := by
  exact lt_of_lt_of_le hc
    (fisherNumerator_infinite_ge_of_eventually_partial_ge
      w x c h0 h1 h2 h3 h4 hge)

/-- The quantitative finite witness specializes directly to a `Finset.range N`
truncation whenever the three selected natural-number states occur in that
prefix. This is the exact finite bookkeeping lemma needed for a fixed witness
in a countable model. -/
theorem fixed_three_state_witness_le_partial_fisherNumerator
    (w x : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    {N i j k : ℕ} (hi : i < N) (hj : j < N) (hk : k < N) :
    (w i *
        (w i * w j * w k *
          (((x i - x j) * (x i - x k) * (x j - x k)) ^ 2))) / 6 ≤
      fisherNumerator
        (partialMoment w x 0 N) (partialMoment w x 1 N)
        (partialMoment w x 2 N) (partialMoment w x 3 N)
        (partialMoment w x 4 N) := by
  let ii : Fin N := ⟨i, hi⟩
  let jj : Fin N := ⟨j, hj⟩
  let kk : Fin N := ⟨k, hk⟩
  have h :=
    GppFiniteFisherQuantitativeWitness.weighted_vandermonde_witness_div_six_le_fisherNumerator
      (fun a : Fin N => w a) (fun a : Fin N => x a)
      (fun a => hw a) ii jj kk
  simpa only [GppCountableFisherMomentLimit.rawMoment_fin_eq_partialMoment] using h

/-- A fixed three-state quantitative witness lower-bounds every sufficiently
large prefix. The witness constant does not decay with the truncation size. -/
theorem eventually_fixed_three_state_witness_le_partial_fisherNumerator
    (w x : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (i j k : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (w i *
          (w i * w j * w k *
            (((x i - x j) * (x i - x k) * (x j - x k)) ^ 2))) / 6 ≤
        fisherNumerator
          (partialMoment w x 0 N) (partialMoment w x 1 N)
          (partialMoment w x 2 N) (partialMoment w x 3 N)
          (partialMoment w x 4 N) := by
  filter_upwards [eventually_ge_atTop (Nat.succ (max i (max j k)))] with N hN
  apply fixed_three_state_witness_le_partial_fisherNumerator w x hw
  · exact lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_max_left i (max j k))) hN
  · exact lt_of_lt_of_le
      (Nat.lt_succ_of_le
        (le_trans (Nat.le_max_left j k) (Nat.le_max_right i (max j k)))) hN
  · exact lt_of_lt_of_le
      (Nat.lt_succ_of_le
        (le_trans (Nat.le_max_right j k) (Nat.le_max_right i (max j k)))) hN

/-- **Fixed-witness countable strictness.** One positive three-state witness at
pairwise distinct observable values, together with summability of raw moments
through order four, forces strict positivity of the countable mass-aware Fisher
numerator. No prefix normalization and no separate eventual-bound hypothesis
are needed. -/
theorem fisherNumerator_infinite_pos_of_fixed_positive_distinct_witness
    (w x : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (i j k : ℕ)
    (hwi : 0 < w i) (hwj : 0 < w j) (hwk : 0 < w k)
    (hij : x i ≠ x j) (hik : x i ≠ x k) (hjk : x j ≠ x k)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4)) :
    0 < fisherNumerator
      (infiniteMoment w x 0) (infiniteMoment w x 1)
      (infiniteMoment w x 2) (infiniteMoment w x 3)
      (infiniteMoment w x 4) := by
  let c : ℝ :=
    (w i *
        (w i * w j * w k *
          (((x i - x j) * (x i - x k) * (x j - x k)) ^ 2))) / 6
  have hdij : x i - x j ≠ 0 := sub_ne_zero.mpr hij
  have hdik : x i - x k ≠ 0 := sub_ne_zero.mpr hik
  have hdjk : x j - x k ≠ 0 := sub_ne_zero.mpr hjk
  have hv : (x i - x j) * (x i - x k) * (x j - x k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdij hdik) hdjk
  have hsq :
      0 < (((x i - x j) * (x i - x k) * (x j - x k)) ^ 2) :=
    sq_pos_of_ne_zero hv
  have hc : 0 < c := by
    dsimp [c]
    positivity
  exact fisherNumerator_infinite_pos_of_eventually_partial_ge
    w x c hc h0 h1 h2 h3 h4
    (eventually_fixed_three_state_witness_le_partial_fisherNumerator w x hw i j k)

/-- At unit total mass, the same positive finite-prefix witness gives strict
positivity of the usual countable Fisher covariance determinant. -/
theorem fisherDet_infinite_pos_of_mass_one_and_eventually_partial_ge
    (w x : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hmass : infiniteMoment w x 0 = 1)
    (hge : ∀ᶠ N : ℕ in atTop,
      c ≤ fisherNumerator
        (partialMoment w x 0 N) (partialMoment w x 1 N)
        (partialMoment w x 2 N) (partialMoment w x 3 N)
        (partialMoment w x 4 N)) :
    0 < fisherDet
      (infiniteMoment w x 1) (infiniteMoment w x 2)
      (infiniteMoment w x 3) (infiniteMoment w x 4) := by
  have hpos := fisherNumerator_infinite_pos_of_eventually_partial_ge
    w x c hc h0 h1 h2 h3 h4 hge
  rw [hmass, GppFiniteFisherMomentBridge.fisherNumerator_one_eq_fisherDet] at hpos
  exact hpos

end GppCountableFisherStrictWitness

#print axioms GppCountableFisherStrictWitness.fisherNumerator_infinite_ge_of_eventually_partial_ge
#print axioms GppCountableFisherStrictWitness.fisherNumerator_infinite_pos_of_eventually_partial_ge
#print axioms GppCountableFisherStrictWitness.fixed_three_state_witness_le_partial_fisherNumerator
#print axioms GppCountableFisherStrictWitness.eventually_fixed_three_state_witness_le_partial_fisherNumerator
#print axioms GppCountableFisherStrictWitness.fisherNumerator_infinite_pos_of_fixed_positive_distinct_witness
#print axioms GppCountableFisherStrictWitness.fisherDet_infinite_pos_of_mass_one_and_eventually_partial_ge
