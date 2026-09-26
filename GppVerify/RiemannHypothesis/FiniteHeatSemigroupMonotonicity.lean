import GppVerify.RiemannHypothesis.FiniteHeatSemigroupGram
import Mathlib.Tactic

/-!
# Positivity and monotonicity of finite positive heat spectra

For a finite atomic heat trace

  K(t) = Σ_a w_a exp(-λ_a t),

nonnegative weights imply `K(t) ≥ 0`, and nonnegative rates imply that `K` is
antitone in Euclidean time.  These are finite spectral consequences only; no claim
is made that the explicit arithmetic prime--Archimedean heat function already has
such a positive spectral representation.
-/

namespace GppFiniteHeatSemigroupMonotonicity

open Real
open scoped BigOperators
open GppFiniteHeatSemigroupGram

/-- A finite atomic heat trace with nonnegative weights is pointwise nonnegative. -/
theorem atomicHeat_nonneg
    {α : Type*} [DecidableEq α]
    (atoms : Finset α) (weight rate : α → ℝ)
    (hweight : ∀ a ∈ atoms, 0 ≤ weight a) (t : ℝ) :
    0 ≤ atomicHeat atoms weight rate t := by
  unfold atomicHeat
  exact Finset.sum_nonneg fun a ha =>
    mul_nonneg (hweight a ha) (Real.exp_pos _).le

/-- With nonnegative spectral rates, every individual heat mode decreases with time. -/
theorem atomicHeat_term_antitone
    {w lam t u : ℝ}
    (hw : 0 ≤ w) (hlam : 0 ≤ lam) (htu : t ≤ u) :
    w * Real.exp (-lam * u) ≤ w * Real.exp (-lam * t) := by
  apply mul_le_mul_of_nonneg_left _ hw
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul] using
    neg_le_neg (mul_le_mul_of_nonneg_left htu hlam)

/-- A finite positive heat trace with nonnegative rates is antitone in Euclidean time. -/
theorem atomicHeat_antitone
    {α : Type*} [DecidableEq α]
    (atoms : Finset α) (weight rate : α → ℝ)
    (hweight : ∀ a ∈ atoms, 0 ≤ weight a)
    (hrate : ∀ a ∈ atoms, 0 ≤ rate a)
    {t u : ℝ} (htu : t ≤ u) :
    atomicHeat atoms weight rate u ≤ atomicHeat atoms weight rate t := by
  unfold atomicHeat
  apply Finset.sum_le_sum
  intro a ha
  exact atomicHeat_term_antitone (hweight a ha) (hrate a ha) htu

/-- In particular, positive-time values are bounded above by the zero-time mass. -/
theorem atomicHeat_le_zero_time
    {α : Type*} [DecidableEq α]
    (atoms : Finset α) (weight rate : α → ℝ)
    (hweight : ∀ a ∈ atoms, 0 ≤ weight a)
    (hrate : ∀ a ∈ atoms, 0 ≤ rate a)
    {t : ℝ} (ht : 0 ≤ t) :
    atomicHeat atoms weight rate t ≤ atomicHeat atoms weight rate 0 :=
  atomicHeat_antitone atoms weight rate hweight hrate ht

end GppFiniteHeatSemigroupMonotonicity

#print axioms GppFiniteHeatSemigroupMonotonicity.atomicHeat_nonneg
#print axioms GppFiniteHeatSemigroupMonotonicity.atomicHeat_antitone
#print axioms GppFiniteHeatSemigroupMonotonicity.atomicHeat_le_zero_time
