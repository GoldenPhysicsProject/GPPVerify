import GppVerify.RiemannHypothesis.FiniteFisherMomentBridge
import GppVerify.RiemannHypothesis.FiniteFisherVandermondeIdentity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Countable Fisher moment limit

This module isolates the analytic passage from finite range moments to the
countable Fisher determinant. If weighted raw moments through order four are
summable, their finite truncations converge to the corresponding `tsum`s.

The mass-aware `fisherNumerator` layer is essential: finite truncations of a
normalized countable measure generally have total mass below one. Positivity
must therefore be transferred before specializing the limiting zeroth moment
to one.
-/

namespace GppCountableFisherMomentLimit

open Filter
open scoped BigOperators Topology
open GppFiniteFisherMomentBridge
open GppFiniteMomentFactorization
open GppFiniteFisherVandermondeIdentity

/-- Finite range raw moment. -/
def partialMoment (w x : ℕ → ℝ) (r N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, w n * x n ^ r

/-- Countable raw moment. -/
noncomputable def infiniteMoment (w x : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑' n : ℕ, w n * x n ^ r

/-- The raw moment of the restriction to `Fin N` is exactly the usual
`Finset.range N` partial moment. This is the bookkeeping bridge between the
finite Vandermonde theorem and countable truncations. -/
theorem rawMoment_fin_eq_partialMoment
    (w x : ℕ → ℝ) (r N : ℕ) :
    rawMoment (fun i : Fin N => w i) (fun i : Fin N => x i) r =
      partialMoment w x r N := by
  unfold rawMoment partialMoment
  rw [← Fin.sum_univ_eq_sum_range]

/-- A summable weighted raw moment is the limit of its finite range truncations. -/
theorem partialMoment_tendsto_infiniteMoment
    (w x : ℕ → ℝ) (r : ℕ)
    (hs : Summable (fun n : ℕ => w n * x n ^ r)) :
    Tendsto (fun N : ℕ => partialMoment w x r N) atTop
      (𝓝 (infiniteMoment w x r)) := by
  simpa [partialMoment, infiniteMoment] using hs.hasSum.tendsto_sum_nat

/-- If moments through order four are summable, the Fisher covariance determinant
of the finite truncations converges to the determinant formed from the countable
raw moments. This normalized polynomial limit is retained for downstream users
that already have normalized finite approximants. -/
theorem fisherDet_partial_tendsto_infinite
    (w x : ℕ → ℝ)
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4)) :
    Tendsto
      (fun N : ℕ => fisherDet
        (partialMoment w x 1 N) (partialMoment w x 2 N)
        (partialMoment w x 3 N) (partialMoment w x 4 N))
      atTop
      (𝓝 (fisherDet
        (infiniteMoment w x 1) (infiniteMoment w x 2)
        (infiniteMoment w x 3) (infiniteMoment w x 4))) := by
  have h1lim := partialMoment_tendsto_infiniteMoment w x 1 h1
  have h2lim := partialMoment_tendsto_infiniteMoment w x 2 h2
  have h3lim := partialMoment_tendsto_infiniteMoment w x 3 h3
  have h4lim := partialMoment_tendsto_infiniteMoment w x 4 h4
  unfold fisherDet
  exact
    ((h2lim.sub (h1lim.pow 2)).mul (h4lim.sub (h2lim.pow 2))).sub
      ((h3lim.sub (h1lim.mul h2lim)).pow 2)

/-- **Mass-aware countable Fisher limit.** If raw moments through order four
are summable, the division-free covariance numerator of the raw finite
truncations converges to the numerator formed from the countable moments.

Unlike `fisherDet_partial_tendsto_infinite`, this theorem tracks `m₀` and is
therefore valid for unnormalized finite truncations of a normalized infinite
measure. -/
theorem fisherNumerator_partial_tendsto_infinite
    (w x : ℕ → ℝ)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4)) :
    Tendsto
      (fun N : ℕ => fisherNumerator
        (partialMoment w x 0 N) (partialMoment w x 1 N)
        (partialMoment w x 2 N) (partialMoment w x 3 N)
        (partialMoment w x 4 N))
      atTop
      (𝓝 (fisherNumerator
        (infiniteMoment w x 0) (infiniteMoment w x 1)
        (infiniteMoment w x 2) (infiniteMoment w x 3)
        (infiniteMoment w x 4))) := by
  have h0lim := partialMoment_tendsto_infiniteMoment w x 0 h0
  have h1lim := partialMoment_tendsto_infiniteMoment w x 1 h1
  have h2lim := partialMoment_tendsto_infiniteMoment w x 2 h2
  have h3lim := partialMoment_tendsto_infiniteMoment w x 3 h3
  have h4lim := partialMoment_tendsto_infiniteMoment w x 4 h4
  unfold fisherNumerator
  exact
    (((h0lim.mul h2lim).sub (h1lim.pow 2)).mul
      ((h0lim.mul h4lim).sub (h2lim.pow 2))).sub
      (((h0lim.mul h3lim).sub (h1lim.mul h2lim)).pow 2)

/-- Every raw finite truncation has nonnegative mass-aware Fisher numerator
when the countable weights are pointwise nonnegative. No normalization of the
truncation is required. -/
theorem fisherNumerator_partial_nonneg
    (w x : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (N : ℕ) :
    0 ≤ fisherNumerator
      (partialMoment w x 0 N) (partialMoment w x 1 N)
      (partialMoment w x 2 N) (partialMoment w x 3 N)
      (partialMoment w x 4 N) := by
  have h := fisherNumerator_nonneg
    (fun i : Fin N => w i) (fun i : Fin N => x i)
    (fun i => hw i)
  simpa only [rawMoment_fin_eq_partialMoment] using h

/-- Nonnegativity of every finite mass-aware Fisher numerator survives the
countable moment limit. This is the topological half of the finite-to-countable
Vandermonde positivity bridge. -/
theorem fisherNumerator_infinite_nonneg_of_partial_nonneg
    (w x : ℕ → ℝ)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hfin : ∀ N : ℕ, 0 ≤ fisherNumerator
      (partialMoment w x 0 N) (partialMoment w x 1 N)
      (partialMoment w x 2 N) (partialMoment w x 3 N)
      (partialMoment w x 4 N)) :
    0 ≤ fisherNumerator
      (infiniteMoment w x 0) (infiniteMoment w x 1)
      (infiniteMoment w x 2) (infiniteMoment w x 3)
      (infiniteMoment w x 4) := by
  exact ge_of_tendsto
    (fisherNumerator_partial_tendsto_infinite w x h0 h1 h2 h3 h4)
    (Filter.Eventually.of_forall hfin)

/-- Pointwise nonnegative weights automatically supply the finite positivity
hypothesis, so the countable mass-aware Fisher numerator is nonnegative. -/
theorem fisherNumerator_infinite_nonneg
    (w x : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4)) :
    0 ≤ fisherNumerator
      (infiniteMoment w x 0) (infiniteMoment w x 1)
      (infiniteMoment w x 2) (infiniteMoment w x 3)
      (infiniteMoment w x 4) := by
  exact fisherNumerator_infinite_nonneg_of_partial_nonneg
    w x h0 h1 h2 h3 h4 (fisherNumerator_partial_nonneg w x hw)

/-- At unit total mass, the mass-aware limiting numerator is exactly the usual
countable Fisher determinant. -/
theorem fisherDet_infinite_nonneg_of_mass_one_and_partial_numerator_nonneg
    (w x : ℕ → ℝ)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hmass : infiniteMoment w x 0 = 1)
    (hfin : ∀ N : ℕ, 0 ≤ fisherNumerator
      (partialMoment w x 0 N) (partialMoment w x 1 N)
      (partialMoment w x 2 N) (partialMoment w x 3 N)
      (partialMoment w x 4 N)) :
    0 ≤ fisherDet
      (infiniteMoment w x 1) (infiniteMoment w x 2)
      (infiniteMoment w x 3) (infiniteMoment w x 4) := by
  have h := fisherNumerator_infinite_nonneg_of_partial_nonneg
    w x h0 h1 h2 h3 h4 hfin
  rw [hmass, fisherNumerator_one_eq_fisherDet] at h
  exact h

/-- **Countable Fisher positivity.** For a nonnegative countable weight with
summable raw moments through order four and unit total mass, the Fisher
covariance determinant of the sufficient statistics `X` and `X^2` is
nonnegative. This closes the finite Vandermonde-to-countable positivity bridge
without assuming normalized finite truncations. -/
theorem fisherDet_infinite_nonneg
    (w x : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hmass : infiniteMoment w x 0 = 1) :
    0 ≤ fisherDet
      (infiniteMoment w x 1) (infiniteMoment w x 2)
      (infiniteMoment w x 3) (infiniteMoment w x 4) := by
  exact fisherDet_infinite_nonneg_of_mass_one_and_partial_numerator_nonneg
    w x h0 h1 h2 h3 h4 hmass (fisherNumerator_partial_nonneg w x hw)

end GppCountableFisherMomentLimit

#print axioms GppCountableFisherMomentLimit.rawMoment_fin_eq_partialMoment
#print axioms GppCountableFisherMomentLimit.partialMoment_tendsto_infiniteMoment
#print axioms GppCountableFisherMomentLimit.fisherDet_partial_tendsto_infinite
#print axioms GppCountableFisherMomentLimit.fisherNumerator_partial_tendsto_infinite
#print axioms GppCountableFisherMomentLimit.fisherNumerator_partial_nonneg
#print axioms GppCountableFisherMomentLimit.fisherNumerator_infinite_nonneg_of_partial_nonneg
#print axioms GppCountableFisherMomentLimit.fisherNumerator_infinite_nonneg
#print axioms GppCountableFisherMomentLimit.fisherDet_infinite_nonneg_of_mass_one_and_partial_numerator_nonneg
#print axioms GppCountableFisherMomentLimit.fisherDet_infinite_nonneg
