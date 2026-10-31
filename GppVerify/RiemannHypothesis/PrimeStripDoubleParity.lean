import Mathlib.Tactic

/-!
# Exact two-reflection source decomposition for a prime endpoint strip

This is a finite scalar algebraic carrier. It proves a signed source
identity for any finite strip data, including real sign-varying profiles.
The continuous L² boundary geometry and actual completed Weil form are
not formalized here. No RH claim or positive-source hypothesis.
-/

namespace GppPrimeStripDoubleParity

variable {N : ℕ}

/-- Local reflection-even part of the first endpoint strip. -/
noncomputable def localEven (g : Fin N → ℝ) (R : Fin N → Fin N) (i : Fin N) : ℝ :=
  (g i + g (R i)) / 2

/-- Local reflection-odd part of the first endpoint strip. -/
noncomputable def localOdd (g : Fin N → ℝ) (R : Fin N → Fin N) (i : Fin N) : ℝ :=
  (g i - g (R i)) / 2

/-- Pointwise two-reflection square identity. This requires no presumed
positivity of the prime term; the two squares enter with OPPOSITE signs. -/
theorem strip_product_eq_even_sq_sub_odd_sq (a b : ℝ) :
    a * b = ((a + b) / 2)^2 - ((a - b) / 2)^2 := by
  ring

/-- Exact signed finite endpoint cross-correlation decomposition.
No assumption that R is involutive is needed for this algebraic identity;
in application R is geometric reflection within the first endpoint strip. -/
theorem strip_cross_decomposition (g : Fin N → ℝ)
    (R : Fin N → Fin N) :
    (∑ i : Fin N, g i * g (R i)) =
      (∑ i : Fin N, (localEven g R i)^2)
        - (∑ i : Fin N, (localOdd g R i)^2) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact strip_product_eq_even_sq_sub_odd_sq (g i) (g (R i))

/-- The geometric first-prime source in any fixed global reflection parity,
with sigma = ±1: the two LOCAL reflection parity channels have opposite sign.
The proof is exact for all finite coefficient arrays, not a numerical test. -/
theorem global_local_source_identity (w sigma : ℝ)
    (g : Fin N → ℝ) (R : Fin N → Fin N) :
    2 * w * sigma * (∑ i : Fin N, g i * g (R i)) =
      2 * w * sigma *
        ((∑ i : Fin N, (localEven g R i)^2)
         - (∑ i : Fin N, (localOdd g R i)^2)) := by
  rw [strip_cross_decomposition]

/-- For a local-reflection-even profile, the source cross term is a sum
of squares, but the completed Weil source enters with the opposite sign. -/
theorem localEven_cross (g : Fin N → ℝ) (R : Fin N → Fin N)
    (h : ∀ i, g (R i) = g i) :
    (∑ i : Fin N, g i * g (R i)) = ∑ i : Fin N, (g i)^2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]
  ring

/-- For a local-reflection-odd profile the same source is minus a sum of
squares; global mirror parity must therefore be tracked separately. -/
theorem localOdd_cross (g : Fin N → ℝ) (R : Fin N → Fin N)
    (h : ∀ i, g (R i) = -g i) :
    (∑ i : Fin N, g i * g (R i)) = -(∑ i : Fin N, (g i)^2) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]
  ring

end GppPrimeStripDoubleParity

#print axioms GppPrimeStripDoubleParity.strip_cross_decomposition
#print axioms GppPrimeStripDoubleParity.global_local_source_identity
#print axioms GppPrimeStripDoubleParity.localOdd_cross
