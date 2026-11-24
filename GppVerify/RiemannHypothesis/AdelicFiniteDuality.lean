/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicPoissonStatement
import GppVerify.RiemannHypothesis.AdelicCovolume


/-!
# `∏ ℤ_v` is self-dual for the finite part of the standard character

Discharges `FinFourierIntegralSelfDual` (`AdelicPoissonStatement.lean`): the finite Fourier
transform of the indicator of `∏ ℤ_v`, against `Rat.FiniteAdeleRing.haar` (normalized so that
`∏ ℤ_v` has volume `1`), is that indicator.

* `finChar_eq_one_iff`: the kernel of the finite part `ψ_f` is exactly `∏ ℤ_v`.
* `exists_natCast_mul_not_mem`: an adele outside `∏ ℤ_v` is moved outside it by a natural number
  (a power of a prime), so `a ↦ ψ_f(-ab)` is a nontrivial character of `∏ ℤ_v` when `b ∉ ∏ ℤ_v`.
* `finFourierIntegralSelfDual`: for `b ∈ ∏ ℤ_v` the integrand is `1` on a set of volume `1`; for
  `b ∉ ∏ ℤ_v` a translation by a point where the character is not `1` forces the integral to be `0`.

This is the single local input that `poissonSummation_pureTensor_integral` consumed.
-/

open MeasureTheory IsDedekindDomain GppIdeleQ

namespace GlobalTate.Poisson

/-- The kernel of the finite part of the standard character is exactly `∏ ℤ_v`. -/
theorem finChar_eq_one_iff (a : Af) : finChar a = 1 ↔ a ∈ intBox := by
  refine ⟨fun h => ?_, finChar_integral⟩
  have hrep : IsRep ((0 : ℝ), a) (rep ((0 : ℝ), a)) := isRep_rep _
  unfold finChar at h
  rw [adeleChar_eq_of_isRep hrep, e_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hq : rep ((0 : ℝ), a) = -(n : ℚ) := by
    have : ((rep ((0 : ℝ), a) : ℚ) : ℝ) = -(n : ℝ) := by
      simp only at hn
      linarith
    exact_mod_cast this
  intro v
  have h1 := hrep v
  have h2 := intCast_mem_integers v (-n)
  have e : a v = (a v - algebraMap ℚ (v.adicCompletion ℚ) (rep ((0 : ℝ), a))) +
      algebraMap ℚ (v.adicCompletion ℚ) (((-n : ℤ) : ℚ)) := by
    rw [hq]; push_cast; ring
  rw [e]
  exact add_mem h1 h2

theorem intBox_mul_mem {a b : Af} (ha : a ∈ intBox) (hb : b ∈ intBox) : a * b ∈ intBox :=
  fun v => mul_mem (ha v) (hb v)

theorem intBox_neg_mem {a : Af} (ha : a ∈ intBox) : -a ∈ intBox := fun v => neg_mem (ha v)

theorem intBox_add_mem {a b : Af} (ha : a ∈ intBox) (hb : b ∈ intBox) : a + b ∈ intBox :=
  fun v => add_mem (ha v) (hb v)

theorem natCast_mem_intBox (m : ℕ) : (m : Af) ∈ intBox := by
  intro v
  have : (m : Af) = algebraMap ℚ Af ((m : ℤ) : ℚ) := by simp
  rw [this, algebraMap_Af_apply]
  exact intCast_mem_integers v m

/-- An adele outside `∏ ℤ_v` is moved outside it by multiplication by a natural number. -/
theorem exists_natCast_mul_not_mem {b : Af} (hb : b ∉ intBox) :
    ∃ m : ℕ, (m : Af) * b ∉ intBox := by
  have : ∃ v, b v ∉ v.adicCompletionIntegers ℚ := by
    by_contra h
    push Not at h
    exact hb h
  obtain ⟨v, hv⟩ := this
  classical
  set p : ℕ := pr v with hp
  have hex := Rat.FiniteAdeleRing.exists_pow_mul_mem_adicCompletionIntegers v (b v)
  set k := Nat.find hex with hk
  have hkspec : ((p : ℕ) : v.adicCompletion ℚ) ^ k * b v ∈ v.adicCompletionIntegers ℚ :=
    Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hkspec
    simp at hkspec
    exact hv hkspec
  refine ⟨p ^ (k - 1), fun hmem => ?_⟩
  have h1 := hmem v
  have e : ((p ^ (k - 1) : ℕ) : Af) v = ((p : ℕ) : v.adicCompletion ℚ) ^ (k - 1) := by
    have : ((p ^ (k - 1) : ℕ) : Af) = algebraMap ℚ Af (((p : ℚ)) ^ (k - 1)) := by simp
    rw [this, algebraMap_Af_apply]
    simp
  have h2 : ((p : ℕ) : v.adicCompletion ℚ) ^ (k - 1) * b v ∈ v.adicCompletionIntegers ℚ := by
    rw [← e]
    exact h1
  exact Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos) h2

/-- **`∏ ℤ_v` is self-dual**: `FinFourierIntegralSelfDual`. -/
theorem finFourierIntegralSelfDual : FinFourierIntegralSelfDual := by
  funext b
  unfold finFourier intIndicator
  have key : ∀ a : Af, (finChar (-(a * b)) : ℂ) * intBox.indicator (fun _ => (1 : ℂ)) a =
      intBox.indicator (fun a => (finChar (-(a * b)) : ℂ)) a := by
    intro a
    by_cases ha : a ∈ intBox <;> simp [Set.indicator, ha]
  simp_rw [key]
  have hmeas : MeasurableSet intBox := isOpen_intBox.measurableSet
  by_cases hb : b ∈ intBox
  · rw [Set.indicator_of_mem hb, integral_indicator hmeas]
    have hc : ∀ a ∈ intBox, (finChar (-(a * b)) : ℂ) = 1 := fun a ha => by
      rw [finChar_integral (intBox_neg_mem (intBox_mul_mem ha hb))]; simp
    rw [setIntegral_congr_fun hmeas hc, setIntegral_const]
    have : Rat.FiniteAdeleRing.haar intBox = 1 := Rat.FiniteAdeleRing.haar_integralAdeles
    simp [Measure.real, this]
  · rw [Set.indicator_of_notMem hb]
    obtain ⟨m, hm⟩ := exists_natCast_mul_not_mem hb
    set a0 : Af := (m : Af) with ha0
    set c : ℂ := (finChar (-(a0 * b)) : ℂ) with hc
    have hc1 : c ≠ 1 := by
      intro h
      have : finChar (-(a0 * b)) = 1 := Subtype.ext h
      rw [finChar_eq_one_iff] at this
      apply hm
      have := intBox_neg_mem this
      simpa using this
    set F : Af → ℂ := fun a => intBox.indicator (fun a => (finChar (-(a * b)) : ℂ)) a with hF
    have hshift : ∀ a, F (a + a0) = c * F a := by
      intro a
      by_cases ha : a ∈ intBox
      · have hs : a + a0 ∈ intBox := intBox_add_mem ha (natCast_mem_intBox m)
        simp only [hF, Set.indicator_of_mem ha, Set.indicator_of_mem hs]
        have : -((a + a0) * b) = -(a * b) + -(a0 * b) := by ring
        rw [this, finChar_add]
        simp [hc, mul_comm]
      · have hs : a + a0 ∉ intBox := fun h => ha (by
          have h' := intBox_add_mem h (intBox_neg_mem (natCast_mem_intBox m))
          have e : a + a0 + -(m : Af) = a := by rw [ha0]; exact add_neg_cancel_right _ _
          rwa [e] at h')
        simp [hF, Set.indicator_of_notMem ha, Set.indicator_of_notMem hs]
    have h1 : ∫ a, F (a + a0) ∂Rat.FiniteAdeleRing.haar = ∫ a, F a ∂Rat.FiniteAdeleRing.haar :=
      integral_add_right_eq_self F a0
    simp_rw [hshift, integral_const_mul] at h1
    have : (c - 1) * ∫ a, F a ∂Rat.FiniteAdeleRing.haar = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hc1
    · exact h

end GlobalTate.Poisson
