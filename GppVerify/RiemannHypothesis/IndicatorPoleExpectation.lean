import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Indicator-vector expectations of the Weil pole kernel and the prime shift sum

Exact calculus behind the "Schur scale" note of Astra (`work/2026-10-17_astra_prime_essential_spectrum_schur_scale.md`,
section 3). On `[-L, L]` with the normalised indicator `f_L = (2L)^{-1/2} 1_{[-L,L]}`:

* the Weil pole kernel `P_L(x,y) = 2 cosh((x-y)/2)` has `⟨f_L, P_L f_L⟩ = 8 (cosh L - 1) / L`
  (`pole_indicator_expectation`);
* the overlap of `[-L,L]` with its translate by `a ∈ [0, 2L]` has length `2L - a`, so the shift
  expectation is `1 - a/(2L)` (`indicator_shift_overlap`);
* hence for finite weights `w_n` at shifts `log n < 2L`, the symmetric prime-shift expectation is
  `2 Σ w_n (1 - log n/(2L))` (`prime_shift_expectation`).

Astra's 60-digit numerical values at `L = 6` (`267.6208481632745` and `262.9586956420191`) were
re-checked independently before this file was written.

**Scope.** Elementary integrals and a finite sum. It says nothing about the spectrum of the prime
operator, about the Archimedean term, or about any zero of ζ. The operator-level essential-spectrum
argument of the note is not formalized here. No RH claim.
-/

namespace GppIndicatorPole

open MeasureTheory intervalIntegral

/-- `⟨f_L, P_L f_L⟩ = 8 (cosh L - 1) / L` for the Weil pole kernel `2 cosh((x-y)/2)`. -/
theorem pole_indicator_expectation (L : ℝ) (hL : 0 < L) :
    (1 / (2 * L)) * ∫ x in (-L)..L, ∫ y in (-L)..L, 2 * Real.cosh ((x - y) / 2) =
      8 * (Real.cosh L - 1) / L := by
  have hinner : ∀ x : ℝ, ∫ y in (-L)..L, 2 * Real.cosh ((x - y) / 2) =
      8 * Real.sinh (L / 2) * Real.cosh (x / 2) := by
    intro x
    have hd : ∀ y ∈ Set.uIcc (-L) L,
        HasDerivAt (fun y : ℝ => -4 * Real.sinh ((x - y) / 2)) (2 * Real.cosh ((x - y) / 2)) y := by
      intro y _
      have h1 : HasDerivAt (fun y : ℝ => (x - y) / 2) (-(1 / 2)) y := by
        exact (((hasDerivAt_id y).const_sub x).div_const 2).congr_deriv (by norm_num)
      exact (h1.sinh.const_mul (-4)).congr_deriv (by ring)
    rw [integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have e1 : Real.sinh ((x - L) / 2) = Real.sinh (x / 2) * Real.cosh (L / 2)
        - Real.cosh (x / 2) * Real.sinh (L / 2) := by
      rw [show (x - L) / 2 = x / 2 - L / 2 by ring, Real.sinh_sub]
    have e2 : Real.sinh ((x - -L) / 2) = Real.sinh (x / 2) * Real.cosh (L / 2)
        + Real.cosh (x / 2) * Real.sinh (L / 2) := by
      rw [show (x - -L) / 2 = x / 2 + L / 2 by ring, Real.sinh_add]
    simp only [e1, e2]
    ring
  simp_rw [hinner]
  have hd2 : ∀ x ∈ Set.uIcc (-L) L,
      HasDerivAt (fun x : ℝ => 8 * Real.sinh (L / 2) * (2 * Real.sinh (x / 2)))
        (8 * Real.sinh (L / 2) * Real.cosh (x / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    exact ((h1.sinh.const_mul 2).const_mul (8 * Real.sinh (L / 2))).congr_deriv (by ring)
  rw [integral_eq_sub_of_hasDerivAt hd2 (by apply Continuous.intervalIntegrable; fun_prop)]
  have hs : Real.sinh (-L / 2) = -Real.sinh (L / 2) := by
    rw [neg_div, Real.sinh_neg]
  have hc : Real.cosh L - 1 = 2 * Real.sinh (L / 2) ^ 2 := by
    have h2 : Real.cosh L = Real.cosh (L / 2) ^ 2 + Real.sinh (L / 2) ^ 2 := by
      rw [← Real.cosh_two_mul]; ring_nf
    nlinarith [Real.cosh_sq (L / 2)]
  rw [hs]
  field_simp
  nlinarith [hc]

/-- The overlap of `[-L, L]` with its translate by `a ∈ [0, 2L]` has length `2L - a`. -/
theorem indicator_shift_overlap (L a : ℝ) (ha : 0 ≤ a) (haL : a ≤ 2 * L) :
    (volume (Set.Icc (-L) L ∩ Set.Icc (-L + a) (L + a))).toReal = 2 * L - a := by
  have : Set.Icc (-L) L ∩ Set.Icc (-L + a) (L + a) = Set.Icc (-L + a) L := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Icc]; constructor
    · rintro ⟨⟨_, h2⟩, ⟨h3, _⟩⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨by linarith, h2⟩, ⟨h3, by linarith⟩⟩
  rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Symmetric prime-shift expectation: with the overlap fraction `1 - ℓ/(2L)` at each shift
`±ℓ_n`, the sum `Σ w_n ((2L-ℓ_n)/(2L) + (2L-ℓ_n)/(2L))` equals `2 Σ w_n (1 - ℓ_n/(2L))`. -/
theorem prime_shift_expectation {ι : Type*} (s : Finset ι) (w ℓ : ι → ℝ) (L : ℝ) (hL : 0 < L) :
    ∑ n ∈ s, w n * ((2 * L - ℓ n) / (2 * L) + (2 * L - ℓ n) / (2 * L)) =
      2 * ∑ n ∈ s, w n * (1 - ℓ n / (2 * L)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  field_simp
  ring

end GppIndicatorPole

#print axioms GppIndicatorPole.pole_indicator_expectation
#print axioms GppIndicatorPole.indicator_shift_overlap
#print axioms GppIndicatorPole.prime_shift_expectation
