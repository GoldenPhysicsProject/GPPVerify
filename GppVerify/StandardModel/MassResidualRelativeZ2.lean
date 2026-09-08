import Mathlib.Tactic
import GppVerify.StandardModel.MassBreaksRelativeScale

/-!
# A nonzero mass leaves only a Z2 remnant of the anti-diagonal relative scale

The independent chiral scaling group contains the anti-diagonal one-parameter subgroup

    A_rel = {(a,a^{-1})}.

A nonzero contact/Dirac mass coupling preserves only the diagonal subgroup `(r,r)`.  Their
intersection therefore obeys

    a = a^{-1},

hence

    a^2 = 1,

and over the complex numbers

    a = +1  or  a = -1.

So a nonzero mass collapses the continuous relative `C*` orientation to a discrete `Z2`
remnant.  This gives a mathematically natural route by which a binary orientation label can
survive after continuous left/right scale symmetry is broken.

The theorem is purely algebraic.  Interpreting this residual Z2 as a physical matter/time
orientation or fermion parity requires the spin-gauge dictionary and is not asserted here.
-/

namespace GppMassResidualRelativeZ2

open GppMassBreaksRelativeScale
open GppRelativePhaseDiracEnergy

/-- Fixed point of inversion implies square one. -/
theorem fixed_by_inverse_sq_one (a : ℂ) (ha0 : a ≠ 0) (hfix : a = a⁻¹) :
    a^2 = 1 := by
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  rw [← hfix] at hinv
  simpa [pow_two] using hinv

/-- Over `C`, the only square roots of one are `±1`. -/
theorem complex_sq_one_iff_pm_one (a : ℂ) :
    a^2 = 1 ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    have hfac : (a - 1) * (a + 1) = 0 := by
      calc
        (a - 1) * (a + 1) = a^2 - 1 := by ring
        _ = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp hfac with h1 | hm1
    · left
      exact sub_eq_zero.mp h1
    · right
      exact eq_neg_of_add_eq_zero_left hm1
  · rintro (rfl | rfl) <;> norm_num

/-- Hence a nonzero anti-diagonal relative scale compatible with the mass exchange is
necessarily one of the two signs. -/
theorem massive_antidiagonal_residual_is_Z2
    (a : ℂ) (ha0 : a ≠ 0)
    (hMass : chiralScale a a⁻¹ * betaRest =
      betaRest * chiralScale a a⁻¹) :
    a = 1 ∨ a = -1 := by
  have hfix : a = a⁻¹ :=
    antidiagonal_mass_symmetry_implies_fixed_point a hMass
  have hsq : a^2 = 1 := fixed_by_inverse_sq_one a ha0 hfix
  exact (complex_sq_one_iff_pm_one a).1 hsq

/-- Both residual signs indeed commute with the mass exchange. -/
theorem residual_plus_minus_survive :
    (chiralScale (1:ℂ) 1 * betaRest = betaRest * chiralScale 1 1) ∧
    (chiralScale (-1:ℂ) (-1) * betaRest = betaRest * chiralScale (-1) (-1)) := by
  exact ⟨diagonal_scale_commutes_beta 1, diagonal_scale_commutes_beta (-1)⟩

end GppMassResidualRelativeZ2
