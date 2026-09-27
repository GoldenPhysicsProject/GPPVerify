import GppVerify.CelestialHolography.ArithmeticOSReflection
import Mathlib

/-!
# Arithmetic OS Gram positivity: finite spectral atoms

The OS kernel attached to a positive heat-semigroup spectral atom has the form

  K_α(s,t) = exp(-α s) exp(-α t).

For any finite real coefficients `cᵢ`, its quadratic form is exactly a square.
This is the finite algebraic skeleton behind the representation

  K(s,t) = ∫ exp(-α s) exp(-α t) dμ(α),  μ ≥ 0.

The file proves only this positive Gram mechanism.  It does not construct the
prime--Archimedean measure `μ` and therefore does not prove arithmetic
reflection positivity or RH.
-/

namespace GppArithmeticOS

open scoped BigOperators

/-- A rank-one real Gram kernel has quadratic form equal to a square. -/
theorem rankOneGram_sum_eq_square
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c v : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (c i * v i) * (c j * v j)) =
      (∑ i ∈ s, c i * v i) ^ 2 := by
  rw [pow_two]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

/-- Consequently every finite rank-one Gram quadratic form is nonnegative. -/
theorem rankOneGram_nonneg
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c v : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, (c i * v i) * (c j * v j) := by
  rw [rankOneGram_sum_eq_square]
  exact sq_nonneg _

/-- A single positive heat spectral atom `α` gives a reflection-positive
finite matrix `exp(-α(tᵢ+tⱼ))`, written in factored semigroup form. -/
theorem heatAtom_osGram_nonneg
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c t : ι → ℝ) (α : ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      (c i * Real.exp (-α * t i)) *
      (c j * Real.exp (-α * t j)) := by
  exact rankOneGram_nonneg s c (fun i => Real.exp (-α * t i))

/-- Positive rescaling of one spectral atom preserves OS Gram positivity. -/
theorem weighted_heatAtom_osGram_nonneg
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c t : ι → ℝ) (α w : ℝ) (hw : 0 ≤ w) :
    0 ≤ w *
      (∑ i ∈ s, ∑ j ∈ s,
        (c i * Real.exp (-α * t i)) *
        (c j * Real.exp (-α * t j))) := by
  exact mul_nonneg hw (heatAtom_osGram_nonneg s c t α)

end GppArithmeticOS

#print axioms GppArithmeticOS.rankOneGram_sum_eq_square
#print axioms GppArithmeticOS.rankOneGram_nonneg
#print axioms GppArithmeticOS.heatAtom_osGram_nonneg
#print axioms GppArithmeticOS.weighted_heatAtom_osGram_nonneg
