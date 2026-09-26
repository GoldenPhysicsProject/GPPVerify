import GppVerify.RiemannHypothesis.KLOrientationKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Midpoint reflection identity for directed-KL asymmetry

The antisymmetric triangular Fisher kernel on `[β,γ]` can be split at the midpoint
and reflected to the left half.  This gives exactly the positive kernel used by the
strict-orientation theorem.
-/

namespace GppKLReflectionIdentity

open Set MeasureTheory intervalIntegral
open GppKLOrientationKernel

/-- Exact midpoint reflection of the antisymmetric Fisher kernel. -/
theorem antisymmetric_integral_eq_reflected
    (g : ℝ → ℝ) (β γ : ℝ) (hg : Continuous g) :
    (∫ x in β..γ, (β + γ - 2 * x) * g x) =
      ∫ y in (0 : ℝ)..((γ - β) / 2),
        reflectedKernel g ((β + γ) / 2) y := by
  let m : ℝ := (β + γ) / 2
  let L : ℝ := (γ - β) / 2
  let f : ℝ → ℝ := fun x => (β + γ - 2 * x) * g x
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hβm : IntervalIntegrable f volume β m := hfcont.intervalIntegrable
  have hmγ : IntervalIntegrable f volume m γ := hfcont.intervalIntegrable
  have hsplit :
      (∫ x in β..γ, f x) = (∫ x in β..m, f x) + ∫ x in m..γ, f x := by
    exact (intervalIntegral.integral_add_adjacent_intervals hβm hmγ).symm
  have hleft :
      (∫ x in β..m, f x) = ∫ y in (0 : ℝ)..L, f (m - y) := by
    have h := intervalIntegral.integral_comp_sub_left (f := f) (a := (0 : ℝ)) (b := L) m
    rw [show m - L = β by dsimp [m, L]; ring,
        show m - 0 = m by ring] at h
    exact h.symm
  have hright :
      (∫ x in m..γ, f x) = ∫ y in (0 : ℝ)..L, f (y + m) := by
    have h := intervalIntegral.integral_comp_add_right (f := f) (a := (0 : ℝ)) (b := L) m
    rw [show 0 + m = m by ring,
        show L + m = γ by dsimp [m, L]; ring] at h
    exact h.symm
  rw [show (∫ x in β..γ, (β + γ - 2 * x) * g x) = ∫ x in β..γ, f x by rfl]
  rw [hsplit, hleft, hright, ← intervalIntegral.integral_add]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp [f, m, reflectedKernel]
  ring

end GppKLReflectionIdentity

#print axioms GppKLReflectionIdentity.antisymmetric_integral_eq_reflected
