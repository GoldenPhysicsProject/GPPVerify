import Mathlib.Tactic
import GppVerify.CelestialHolography.SturmReciprocalPotential

/-!
# The two fixed points of reciprocal Sturm duality are complex and para-complex geometry

The rank-two Penrose/NSF Sturm generator is

    G_U(x,p) = (p,-U x),

and satisfies

    G_U^2 = -U id.

The reciprocal component exchange sends the projective dynamics at `U` to that at `U^{-1}`.
Hence the fixed potentials of reciprocal duality satisfy

    U = U^{-1}  <=>  U^2=1,

so over `C` they are exactly

    U=+1, U=-1.

These two fixed points have sharply different geometry:

* `U=+1`: `G_1(x,p)=(p,-x)` and `G_1^2=-1`, the elliptic/complex quarter-turn;
* `U=-1`: `G_{-1}(x,p)=(p,x)` and `G_{-1}^2=+1`, the split/para-complex reciprocal exchange;
* `U=0`: `G_0^2=0`, the parabolic/nilpotent transition between them.

Moreover the first two operations are *exactly* the `epsilonTurn` and `reciprocalSwap`
already present in the ambitwistor Sturm carrier.  Thus the project's complex/spin Z4 and
split/exchange Z2 are the two self-reciprocal normalized points of one Sturm family, not
independent matrices introduced by hand.

The normalization `|U|=1` is a choice of dimensionless projective scale; this theorem does
not claim generic curved spacetime has `U=±1`.
-/

namespace GppSturmDualityFixedPointGeometry

open GppAmbidextrousPenroseRayQuotients
open GppAmbitwistorSturmBidegrees
open GppSturmReciprocalPotential

/-- General square law, repackaged. -/
theorem Sturm_square_is_minus_potential (U : ℂ) (u : SturmState) :
    sturmGenerator U (sturmGenerator U u) = scaleSturmState (-U) u := by
  rcases u with ⟨x,p⟩
  simp [sturmGenerator, scaleSturmState]
  constructor <;> ring

/-- At the positive reciprocal fixed point the Sturm generator is the epsilon quarter-turn. -/
theorem Sturm_at_plus_one_eq_epsilonTurn (u : SturmState) :
    sturmGenerator 1 u = epsilonTurn u := by
  rcases u with ⟨x,p⟩
  simp [sturmGenerator, epsilonTurn]

/-- Hence the `U=+1` generator is a complex structure. -/
theorem Sturm_plus_one_sq_neg_id (u : SturmState) :
    sturmGenerator 1 (sturmGenerator 1 u) = scaleSturmState (-1) u := by
  simpa using Sturm_square_is_minus_potential (1:ℂ) u

/-- At the negative reciprocal fixed point the Sturm generator is the reciprocal swap. -/
theorem Sturm_at_minus_one_eq_reciprocalSwap (u : SturmState) :
    sturmGenerator (-1) u = reciprocalSwap u := by
  rcases u with ⟨x,p⟩
  simp [sturmGenerator, reciprocalSwap]

/-- Hence the `U=-1` generator is a para-complex involution. -/
theorem Sturm_minus_one_sq_id (u : SturmState) :
    sturmGenerator (-1) (sturmGenerator (-1) u) = u := by
  rw [Sturm_at_minus_one_eq_reciprocalSwap,
      Sturm_at_minus_one_eq_reciprocalSwap,
      reciprocalSwap_involution]

/-- The zero-potential generator is nilpotent of order two. -/
theorem Sturm_zero_sq_zero (u : SturmState) :
    sturmGenerator 0 (sturmGenerator 0 u) = (0,0) := by
  rcases u with ⟨x,p⟩
  simp [sturmGenerator]

/-- A nonzero reciprocal fixed point squares to one. -/
theorem reciprocal_fixed_implies_square_one
    (U : ℂ) (hU : U ≠ 0) (hfix : U = U⁻¹) : U^2 = 1 := by
  have hinv : U * U⁻¹ = 1 := mul_inv_cancel₀ hU
  rw [← hfix] at hinv
  simpa [pow_two] using hinv

/-- The only reciprocal fixed potentials are `+1` and `-1`. -/
theorem reciprocal_fixed_points_pm_one
    (U : ℂ) (hU : U ≠ 0) (hfix : U = U⁻¹) :
    U = 1 ∨ U = -1 := by
  have hsq : U^2 = 1 := reciprocal_fixed_implies_square_one U hU hfix
  have hfac : (U - 1) * (U + 1) = 0 := by
    calc
      (U - 1) * (U + 1) = U^2 - 1 := by ring
      _ = 0 := by rw [hsq]; ring
  rcases mul_eq_zero.mp hfac with h1 | hm1
  · left; exact sub_eq_zero.mp h1
  · right; exact eq_neg_of_add_eq_zero_left hm1

/-- Both normalized fixed points really are fixed by reciprocal potential duality. -/
theorem plus_minus_one_are_reciprocal_fixed :
    ((1:ℂ)⁻¹ = 1) ∧ ((-1:ℂ)⁻¹ = -1) := by
  norm_num

/-- Capstone trichotomy at the three canonical normalized potentials. -/
theorem normalized_elliptic_parabolic_split_package (u : SturmState) :
    sturmGenerator 1 (sturmGenerator 1 u) = scaleSturmState (-1) u ∧
    sturmGenerator 0 (sturmGenerator 0 u) = (0,0) ∧
    sturmGenerator (-1) (sturmGenerator (-1) u) = u := by
  exact ⟨Sturm_plus_one_sq_neg_id u, Sturm_zero_sq_zero u,
    Sturm_minus_one_sq_id u⟩

end GppSturmDualityFixedPointGeometry
