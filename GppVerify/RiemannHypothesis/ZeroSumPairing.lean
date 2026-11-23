import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Pairings defined by a symmetric zero sum

A *zero sum* is a family of points `z k ∈ ℂ` (the zeros of an even function, with multiplicity)
and weights `w k ∈ ℂ`, symmetric in the sense that there is an equivalence `σ` of the index type
with `z (σ k) = - z k` and `w (σ k) = w k`. The pairing of two packets `P, P' : ℂ → ℂ` is

  `pair Z P P' = ∑' k, w k * P (z k) * P' (- z k)`.

All identities below are termwise (or a reindexing by `σ`) and hold with no summability
hypothesis, with the `tsum` convention of Mathlib.

* `pair_symm`: the pairing is symmetric.
* `pair_even_odd`: an even packet and an odd packet pair to `0` (parity).
* `pair_zero_of_vanishing`, `pair_zero_right`: a packet vanishing at every point of the
  zero sum pairs to zero with every packet.
* `pair_split_F`: for an even `S` and odd `V` with `S² - θ² V² = A D` pointwise and `A D` vanishing
  at every point of the zero sum, `pair S S = - θ² * pair V V`.
* `pair_split_H`: for `H` vanishing at every point of the zero sum, even `S` and `W` with
  `S - H = θ² W`, `pair S S = θ⁴ * pair W W`.
* `pair_A_self`: for `A (-z) = D z` and `A D` vanishing at every point, `pair A A = 0`.
-/

open Complex

namespace GppZeroSum

/-- A symmetric zero sum: points, weights, and the reflection equivalence. -/
structure ZeroSum (ι : Type*) where
  z : ι → ℂ
  w : ι → ℂ
  σ : ι ≃ ι
  hz : ∀ k, z (σ k) = -z k
  hw : ∀ k, w (σ k) = w k

variable {ι : Type*}

/-- The pairing of two packets over the zero sum. -/
noncomputable def pair (Z : ZeroSum ι) (P P' : ℂ → ℂ) : ℂ :=
  ∑' k, Z.w k * P (Z.z k) * P' (-Z.z k)

/-- The pairing is symmetric. -/
theorem pair_symm (Z : ZeroSum ι) (P P' : ℂ → ℂ) : pair Z P P' = pair Z P' P := by
  unfold pair
  rw [← Equiv.tsum_eq Z.σ]
  refine tsum_congr fun k => ?_
  rw [Z.hz, Z.hw, neg_neg]
  ring

/-- Parity: an even packet and an odd packet pair to zero. -/
theorem pair_even_odd (Z : ZeroSum ι) {P P' : ℂ → ℂ} (hP : ∀ x, P (-x) = P x)
    (hP' : ∀ x, P' (-x) = -P' x) : pair Z P P' = 0 := by
  have h : pair Z P P' = -pair Z P P' := by
    unfold pair
    conv_lhs => rw [← Equiv.tsum_eq Z.σ]
    rw [← tsum_neg]
    refine tsum_congr fun k => ?_
    rw [Z.hz, Z.hw, hP, neg_neg, hP' (Z.z k)]
    ring
  have h2 : (2 : ℂ) * pair Z P P' = 0 := by linear_combination h
  simpa using h2

/-- A packet vanishing on the zero sum pairs to zero on the left. -/
theorem pair_zero_of_vanishing (Z : ZeroSum ι) {H : ℂ → ℂ} (hH : ∀ k, H (Z.z k) = 0)
    (P' : ℂ → ℂ) : pair Z H P' = 0 := by
  unfold pair
  have : ∀ k, Z.w k * H (Z.z k) * P' (-Z.z k) = 0 := fun k => by rw [hH k]; ring
  simp [this]

/-- A packet vanishing on the zero sum pairs to zero on the right. -/
theorem pair_zero_right (Z : ZeroSum ι) {H : ℂ → ℂ} (hH : ∀ k, H (Z.z k) = 0)
    (P : ℂ → ℂ) : pair Z P H = 0 := by
  rw [pair_symm]; exact pair_zero_of_vanishing Z hH P

/-- Split identity `Q_F(S) = - θ² Q_F(V)`. -/
theorem pair_split_F (Z : ZeroSum ι) {A D S V : ℂ → ℂ} (θ : ℂ) (hS : ∀ x, S (-x) = S x)
    (hV : ∀ x, V (-x) = -V x) (hid : ∀ x, S x ^ 2 - θ ^ 2 * V x ^ 2 = A x * D x)
    (hzero : ∀ k, A (Z.z k) * D (Z.z k) = 0) : pair Z S S = -θ ^ 2 * pair Z V V := by
  unfold pair
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h := hid (Z.z k)
  rw [hzero k] at h
  rw [hS, hV]
  linear_combination (Z.w k) * h

/-- Split identity `Q_H(S) = θ⁴ Q_H(W)`. -/
theorem pair_split_H (Z : ZeroSum ι) {H S W : ℂ → ℂ} (θ : ℂ) (hS : ∀ x, S (-x) = S x)
    (hW : ∀ x, W (-x) = W x) (hid : ∀ x, S x - H x = θ ^ 2 * W x)
    (hH : ∀ k, H (Z.z k) = 0) : pair Z S S = θ ^ 4 * pair Z W W := by
  unfold pair
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h := hid (Z.z k)
  rw [hH k, sub_zero] at h
  rw [hS, hW]
  have : S (Z.z k) ^ 2 = θ ^ 4 * W (Z.z k) ^ 2 := by rw [h]; ring
  linear_combination (Z.w k) * this

/-- `Q_F(A, A) = 0` when `A (-z) = D z` and `A D` vanishes at every point. -/
theorem pair_A_self (Z : ZeroSum ι) {A D : ℂ → ℂ} (hAD : ∀ x, A (-x) = D x)
    (hzero : ∀ k, A (Z.z k) * D (Z.z k) = 0) : pair Z A A = 0 := by
  unfold pair
  have : ∀ k, Z.w k * A (Z.z k) * A (-Z.z k) = 0 := fun k => by
    rw [hAD]
    have := hzero k
    calc Z.w k * A (Z.z k) * D (Z.z k) = Z.w k * (A (Z.z k) * D (Z.z k)) := by ring
      _ = 0 := by rw [this]; ring
  simp [this]

#print axioms pair_symm
#print axioms pair_even_odd
#print axioms pair_zero_of_vanishing
#print axioms pair_split_F
#print axioms pair_split_H
#print axioms pair_A_self

end GppZeroSum
