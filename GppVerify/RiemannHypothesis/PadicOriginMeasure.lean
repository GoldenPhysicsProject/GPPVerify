import GppVerify.RiemannHypothesis.PadicZetaIntegral

/-!
# The origin has Haar measure zero in `ℤ_p`

Real infrastructure continuing the p-adic zeta integral thread (Tate's-thesis lecture
notes, Example 4.10): `μ({0}) = 0`, needed to justify dropping the origin when
decomposing `ℤ_p` into the shells `pⁿ ℤ_p \ pⁿ⁺¹ ℤ_p`. Not sourced from a specific
Golden Physics Project paper.

Proved without any limit/`Tendsto` machinery: `{0} ⊆ pⁿ ℤ_p` for every `n`, so
`μ({0}) ≤ μ(pⁿ ℤ_p) = (p⁻¹)ⁿ` for every `n`; since `p⁻¹ < 1`, Mathlib's
`ENNReal.eq_zero_of_le_mul_pow` (a quantity bounded by every term of a geometric
sequence with ratio `< 1` is zero) closes it directly.
-/

namespace GppPadicOrigin

open MeasureTheory
open scoped ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- **The origin has Haar measure zero.** -/
theorem haarMeasure_singleton_zero :
    GppPadicHaar.haarMeasure p ({0} : Set (PadicInt p)) = 0 := by
  have hle : ∀ n : ℕ,
      GppPadicHaar.haarMeasure p ({0} : Set (PadicInt p)) ≤
        (1 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    rw [one_mul, ← ENNReal.inv_pow, ← GppPadicZetaIntegral.haarMeasure_span_pow p n]
    apply measure_mono
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact Submodule.zero_mem _
  have hr : (p : ℝ≥0∞)⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]
    exact_mod_cast (Fact.out : p.Prime).one_lt
  exact ENNReal.eq_zero_of_le_mul_pow hr hle

end GppPadicOrigin
