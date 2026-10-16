import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Weil-window invisible shifts: pointwise support and autocorrelation

For an ordinary test function supported in the *open* interval (-L,L),
translations by u with |u| >= 2L have no overlapping support. Consequently
the shifted autocorrelation is zero, including the boundary |u| = 2L.

This is the spatial half of the invisible-harmonic lemma used in
Grok S27 (2026-10-15); Fourier inversion/Plancherel connecting
the autocorrelation with the cosine multiplier is not claimed here.
No RH or GRH conclusion.
-/

namespace GppWeilInvisibleFrequency

/-- Two points in the open support window cannot differ by at least its diameter. -/
theorem open_window_disjoint_shift
    (L u x : ℝ) (hu : 2 * L ≤ |u|) :
    ¬ ((-L < x ∧ x < L) ∧ (-L < x + u ∧ x + u < L)) := by
  rintro ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
  have hup : u < 2 * L := by linarith
  have hdown : -(2 * L) < u := by linarith
  have hbound : |u| < 2 * L := abs_lt.mpr ⟨hdown, hup⟩
  exact (not_lt_of_ge hu) hbound

/-- The integrand in the shifted autocorrelation vanishes pointwise. -/
theorem shifted_conjugate_product_zero
    (f : ℝ → ℂ) (L u x : ℝ)
    (hf : ∀ y : ℝ, ¬ (-L < y ∧ y < L) → f y = 0)
    (hu : 2 * L ≤ |u|) :
    f x * star (f (x + u)) = 0 := by
  by_cases hx : -L < x ∧ x < L
  · have hy : ¬ (-L < x + u ∧ x + u < L) := by
      intro hy
      exact open_window_disjoint_shift L u x hu ⟨hx, hy⟩
    have h0 : f (x + u) = 0 := hf _ hy
    rw [h0]
    simp
  · have h0 : f x = 0 := hf _ hx
    rw [h0]
    simp

/-- The shifted autocorrelation integral vanishes (no integrability assumption
needed, since the integrand is identically zero). -/
theorem shifted_autocorrelation_zero
    (f : ℝ → ℂ) (L u : ℝ)
    (hf : ∀ y : ℝ, ¬ (-L < y ∧ y < L) → f y = 0)
    (hu : 2 * L ≤ |u|) :
    (∫ x : ℝ, f x * star (f (x + u))) = 0 := by
  have hpoint (x : ℝ) : f x * star (f (x + u)) = 0 := by
    exact shifted_conjugate_product_zero f L u x hf hu
  calc
    (∫ x : ℝ, f x * star (f (x + u))) = (∫ _x : ℝ, (0 : ℂ)) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = 0 := by simp

end GppWeilInvisibleFrequency
