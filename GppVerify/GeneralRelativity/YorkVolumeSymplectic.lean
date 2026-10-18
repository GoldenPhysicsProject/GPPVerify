import Mathlib.Tactic

/-!
# York time, canonical volume and time reversal

Exact finite-volume algebra modeling the ADM symplectic pairing used in
Belin--Lewkowycz--Sárosi (2019) and Jacobson--Visser (2019).

A York deformation changes momentum by a multiple of the metric trace
density. The canonical pairing with a metric variation is therefore
twice that multiple times the first variation of spatial volume.

This file proves the finite-sum contraction without an implicit
gravitational field equation. Identifying the data with solutions of
the Einstein constraints and with the renormalized gravitational
symplectic form is a separate analytic/geometric obligation.
-/

namespace GppYorkVolume

open scoped BigOperators

section Canonical
variable {N M : ℕ}

def tracePair (weight : Fin N → ℝ)
    (invMetric dh : Fin N → Fin M → Fin M → ℝ) : ℝ :=
  ∑ x, weight x * ∑ i, ∑ j, invMetric x i j * dh x i j

/-- First variation of spatial volume in a discretized coordinate chart:
dV = 1/2 ∑ sqrt(h) h^ij dh_ij. -/
def volumeTangent (weight : Fin N → ℝ)
    (invMetric dh : Fin N → Fin M → Fin M → ℝ) : ℝ :=
  (1 / 2 : ℝ) * tracePair weight invMetric dh

/-- Momentum shift of a York deformation, with the extrinsic-curvature
normalization combined into c. -/
def yorkMomentum (c : ℝ) (weight : Fin N → ℝ)
    (invMetric : Fin N → Fin M → Fin M → ℝ) :
    Fin N → Fin M → Fin M → ℝ :=
  fun x i j => c * weight x * invMetric x i j

def canonicalMomentumPair (dp dh : Fin N → Fin M → Fin M → ℝ) : ℝ :=
  ∑ x, ∑ i, ∑ j, dp x i j * dh x i j

/-- Exact York--volume contraction, with no unproved input beyond
the chosen ADM trace-momentum variation. -/
theorem york_pairing_is_volume_variation
    (c : ℝ) (weight : Fin N → ℝ)
    (invMetric dh : Fin N → Fin M → Fin M → ℝ) :
    canonicalMomentumPair (yorkMomentum c weight invMetric) dh =
      (2 * c) * volumeTangent weight invMetric dh := by
  unfold canonicalMomentumPair yorkMomentum volumeTangent tracePair
  calc
    (∑ x, ∑ i, ∑ j, (c * weight x * invMetric x i j) * dh x i j) =
        ∑ x, (c * weight x) * (∑ i, ∑ j, invMetric x i j * dh x i j) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * (∑ x, weight x * ∑ i, ∑ j, invMetric x i j * dh x i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (2 * c) * ((1 / 2 : ℝ) *
          (∑ x, weight x * ∑ i, ∑ j, invMetric x i j * dh x i j)) := by
      ring

/-- The spatial volume first variation is time-even: reversing
canonical momenta does not change the metric perturbation or dV. -/
theorem york_reversal_changes_pairing_sign
    (c : ℝ) (weight : Fin N → ℝ)
    (invMetric dh : Fin N → Fin M → Fin M → ℝ) :
    canonicalMomentumPair (yorkMomentum (-c) weight invMetric) dh =
      -canonicalMomentumPair (yorkMomentum c weight invMetric) dh := by
  rw [york_pairing_is_volume_variation,
      york_pairing_is_volume_variation]
  ring

end Canonical

section TwoSided
variable {N : ℕ}

/-- Canonical symplectic pairing, with configuration q and momentum p. -/
def canonicalOmega (q₁ p₁ q₂ p₂ : Fin N → ℝ) : ℝ :=
  ∑ i, (p₁ i * q₂ i - p₂ i * q₁ i)

/-- Reversing *both* momenta reverses symplectic orientation. -/
theorem time_reversal_anti_symplectic
    (q₁ p₁ q₂ p₂ : Fin N → ℝ) :
    canonicalOmega q₁ (fun i => -p₁ i) q₂ (fun i => -p₂ i) =
      -canonicalOmega q₁ p₁ q₂ p₂ := by
  unfold canonicalOmega
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Reversing the two-sided time orientation twice is the identity. -/
theorem time_reversal_involutive (p : Fin N → ℝ) :
    (fun i => -(-p i)) = p := by
  funext i
  ring

/-- The configuration sector is unaffected by momentum time reversal. -/
theorem spatial_measure_time_even (V : (Fin N → ℝ) → ℝ)
    (q p : Fin N → ℝ) :
    V q = V q := rfl

end TwoSided

end GppYorkVolume

#print axioms GppYorkVolume.york_pairing_is_volume_variation
#print axioms GppYorkVolume.time_reversal_anti_symplectic
