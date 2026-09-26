import GppVerify.RiemannHypothesis.CountableFisherMomentLimit
import GppVerify.RiemannHypothesis.FiniteFisherVandermondeIdentity
import GppVerify.RiemannHypothesis.FiniteVandermondeEnergy
import Mathlib.Tactic

/-!
# Countable Fisher determinant nonnegativity

This module closes the positivity passage from arbitrary finite weighted support
to a countable normalized measure.  Finite truncations are deliberately kept
unnormalized: their division-free covariance numerator is nonnegative by the
finite Fisher--Vandermonde identity.  Summability then passes that homogeneous
numerator to the countable limit, where total mass one recovers the ordinary
Fisher covariance determinant for the sufficient statistics `X` and `X^2`.
-/

namespace GppCountableFisherNonnegativity

open Filter
open scoped BigOperators Topology
open GppFiniteMomentFactorization
open GppFiniteFisherMomentBridge
open GppFiniteVandermondeEnergy
open GppFiniteFisherVandermondeIdentity
open GppCountableFisherMomentLimit

/-- Finite range moments agree with raw moments on the corresponding `Fin N`
support. -/
theorem partialMoment_eq_rawMoment_fin
    (w x : ℕ → ℝ) (r N : ℕ) :
    partialMoment w x r N =
      rawMoment (fun i : Fin N => w i) (fun i : Fin N => x i) r := by
  simp [partialMoment, rawMoment]

/-- Every finite truncation has nonnegative homogeneous Fisher numerator when
the weights are nonnegative.  No normalization of the truncation is used. -/
theorem partial_fisherNumerator_nonneg
    (w x : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (N : ℕ) :
    0 ≤ fisherNumerator
      (partialMoment w x 0 N) (partialMoment w x 1 N)
      (partialMoment w x 2 N) (partialMoment w x 3 N)
      (partialMoment w x 4 N) := by
  let p : Fin N → ℝ := fun i => w i
  let y : Fin N → ℝ := fun i => x i
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    exact hw i
  have henergy : 0 ≤ orderedVandermondeEnergy p y :=
    orderedVandermondeEnergy_nonneg p y hp
  have hid : orderedVandermondeEnergy p y =
      momentDiscriminant
        (rawMoment p y 0) (rawMoment p y 1) (rawMoment p y 2)
        (rawMoment p y 3) (rawMoment p y 4) :=
    orderedVandermondeEnergy_eq_momentDiscriminant p y
  have hdisc : 0 ≤ momentDiscriminant
      (rawMoment p y 0) (rawMoment p y 1) (rawMoment p y 2)
      (rawMoment p y 3) (rawMoment p y 4) := by
    rw [← hid]
    exact henergy
  have hm0 : 0 ≤ rawMoment p y 0 := by
    unfold rawMoment
    apply Finset.sum_nonneg
    intro i hi
    simp [hp i]
  have hbridge := six_fisherNumerator_eq_mass_mul_momentDiscriminant
    (rawMoment p y 0) (rawMoment p y 1) (rawMoment p y 2)
    (rawMoment p y 3) (rawMoment p y 4)
  have hnum : 0 ≤ fisherNumerator
      (rawMoment p y 0) (rawMoment p y 1) (rawMoment p y 2)
      (rawMoment p y 3) (rawMoment p y 4) := by
    nlinarith [mul_nonneg hm0 hdisc]
  simpa [p, y, ← partialMoment_eq_rawMoment_fin] using hnum

/-- Under summability through order four, the homogeneous Fisher numerator of
finite truncations converges to its countable raw-moment counterpart. -/
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
    ((h0lim.mul h2lim).sub (h1lim.pow 2)).mul
      ((h0lim.mul h4lim).sub (h2lim.pow 2)) |>.sub
        (((h0lim.mul h3lim).sub (h1lim.mul h2lim)).pow 2)

/-- **Countable two-parameter Fisher positivity.**  For a nonnegative normalized
countable weight with summable moments through order four, the covariance
matrix of `X` and `X^2` has nonnegative determinant. -/
theorem fisherDet_infinite_nonneg
    (w x : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hnorm : infiniteMoment w x 0 = 1) :
    0 ≤ fisherDet
      (infiniteMoment w x 1) (infiniteMoment w x 2)
      (infiniteMoment w x 3) (infiniteMoment w x 4) := by
  have hlim := fisherNumerator_partial_tendsto_infinite w x h0 h1 h2 h3 h4
  have hnonneg : ∀ N : ℕ, 0 ≤ fisherNumerator
      (partialMoment w x 0 N) (partialMoment w x 1 N)
      (partialMoment w x 2 N) (partialMoment w x 3 N)
      (partialMoment w x 4 N) :=
    partial_fisherNumerator_nonneg w x hw
  have hinf : 0 ≤ fisherNumerator
      (infiniteMoment w x 0) (infiniteMoment w x 1)
      (infiniteMoment w x 2) (infiniteMoment w x 3)
      (infiniteMoment w x 4) :=
    le_of_tendsto hlim (Eventually.of_forall hnonneg)
  rw [hnorm, fisherNumerator_one_eq_fisherDet] at hinf
  exact hinf

end GppCountableFisherNonnegativity

#print axioms GppCountableFisherNonnegativity.partialMoment_eq_rawMoment_fin
#print axioms GppCountableFisherNonnegativity.partial_fisherNumerator_nonneg
#print axioms GppCountableFisherNonnegativity.fisherNumerator_partial_tendsto_infinite
#print axioms GppCountableFisherNonnegativity.fisherDet_infinite_nonneg
