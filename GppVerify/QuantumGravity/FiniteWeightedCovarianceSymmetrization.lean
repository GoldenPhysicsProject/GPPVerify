import Mathlib

/-!
# Finite weighted covariance symmetrization

This file isolates the finite algebraic identity behind the iid-copy covariance
symmetrization used in the continuous Gamma-chamber program.

For weights `wᵢ`, observables `gᵢ`, radial variables `yᵢ`, and total weight
`W = ∑ᵢ wᵢ`, the ordered pair sum satisfies

`∑ᵢⱼ wᵢ wⱼ (gᵢ-gⱼ)(yᵢ-yⱼ)
   = 2 (W ∑ᵢ wᵢ gᵢ yᵢ - (∑ᵢ wᵢ gᵢ)(∑ᵢ wᵢ yᵢ))`.

With nonnegative weights and pairwise monotonicity alignment, the right-hand
covariance numerator is therefore nonnegative.  This is a finite theorem only:
no measure-theoretic product/Fubini statement is claimed here.
-/

namespace GppFiniteWeightedCovarianceSymmetrization

open scoped BigOperators

variable {n : ℕ}

/-- Total mass of a finite real weight family. -/
def totalWeight (w : Fin n → ℝ) : ℝ := ∑ i, w i

/-- Unnormalized weighted covariance numerator. -/
def covarianceNumerator (w g y : Fin n → ℝ) : ℝ :=
  totalWeight w * (∑ i, w i * g i * y i) -
    (∑ i, w i * g i) * (∑ i, w i * y i)

/-- Ordered pairwise alignment energy. -/
def pairwiseAlignmentEnergy (w g y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (w i * w j) * ((g i - g j) * (y i - y j))

/-- Covariance after normalizing the finite weight family by its total mass. -/
noncomputable def normalizedCovariance (w g y : Fin n → ℝ) : ℝ :=
  covarianceNumerator w g y / (totalWeight w)^2

/-- Exact finite weighted covariance symmetrization. -/
theorem pairwiseAlignmentEnergy_eq_two_covarianceNumerator
    (w g y : Fin n → ℝ) :
    pairwiseAlignmentEnergy w g y = 2 * covarianceNumerator w g y := by
  unfold pairwiseAlignmentEnergy covarianceNumerator totalWeight
  have h1 : ∑ i, ∑ j, w i * w j * (g j * y j) = ∑ i, ∑ j, w i * w j * (g i * y i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ i, ∑ j, w i * w j * (g i * y j) = ∑ i, ∑ j, w i * w j * (g j * y i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [h1, h2]
  simp only [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Nonnegative weights and pairwise monotone alignment make the ordered
pairwise energy nonnegative. -/
theorem pairwiseAlignmentEnergy_nonneg
    (w g y : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (halign : ∀ i j, 0 ≤ (g i - g j) * (y i - y j)) :
    0 ≤ pairwiseAlignmentEnergy w g y := by
  unfold pairwiseAlignmentEnergy
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (hw i) (hw j)) (halign i j)

/-- Finite weighted Chebyshev covariance inequality in unnormalized form. -/
theorem covarianceNumerator_nonneg_of_pairwise_alignment
    (w g y : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (halign : ∀ i j, 0 ≤ (g i - g j) * (y i - y j)) :
    0 ≤ covarianceNumerator w g y := by
  have henergy : 0 ≤ pairwiseAlignmentEnergy w g y :=
    pairwiseAlignmentEnergy_nonneg w g y hw halign
  rw [pairwiseAlignmentEnergy_eq_two_covarianceNumerator] at henergy
  nlinarith

/-- Finite weighted Chebyshev covariance inequality after normalization.
The positive-total-mass hypothesis is the finite analogue of working with a
probability measure and records the nondegenerate normalization needed for the
continuous Gamma-chamber lift. -/
theorem normalizedCovariance_nonneg_of_pairwise_alignment
    (w g y : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hW : 0 < totalWeight w)
    (halign : ∀ i j, 0 ≤ (g i - g j) * (y i - y j)) :
    0 ≤ normalizedCovariance w g y := by
  unfold normalizedCovariance
  have hnum : 0 ≤ covarianceNumerator w g y :=
    covarianceNumerator_nonneg_of_pairwise_alignment w g y hw halign
  have hden : 0 ≤ (totalWeight w)^2 := sq_nonneg (totalWeight w)
  exact div_nonneg hnum hden

/-- Strict pairwise alignment energy forces strict normalized covariance whenever
the total mass is positive.  This isolates the strictness step independently of
how positivity of the pairwise energy is established. -/
theorem normalizedCovariance_pos_of_pairwiseAlignmentEnergy_pos
    (w g y : Fin n → ℝ)
    (hW : 0 < totalWeight w)
    (henergy : 0 < pairwiseAlignmentEnergy w g y) :
    0 < normalizedCovariance w g y := by
  have hEq := pairwiseAlignmentEnergy_eq_two_covarianceNumerator w g y
  have hnum : 0 < covarianceNumerator w g y := by
    nlinarith
  have hden : 0 < (totalWeight w)^2 := by
    simpa [pow_two] using mul_pos hW hW
  unfold normalizedCovariance
  exact div_pos hnum hden

end GppFiniteWeightedCovarianceSymmetrization
