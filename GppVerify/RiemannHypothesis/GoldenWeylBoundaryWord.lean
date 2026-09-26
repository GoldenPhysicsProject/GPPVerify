import GppVerify.RiemannHypothesis.GoldenMobiusAudit
import Mathlib.Tactic

/-!
# Suzuki Weyl boundary word and the golden return map

This file separates three scalar coordinates which must not be conflated in the
Riemann-hypothesis boundary program.

* `suzukiRatio = A/B` is the homogeneous deficiency/projective coordinate.
  Spectral reflection `z ↦ -z` swaps `A` and `B`, hence reciprocates this ratio.
* The normalized physical Suzuki Weyl function is naturally
  `m = -i (A-B)/(A+B)`.  Reflection changes its sign.
* The opposite `0/π` self-adjoint boundary condition is represented by the
  negative reciprocal `m ↦ -1/m`.
* A unit rank-one Krein feedback translates the reciprocal response by one.

The composite

  reflection -> opposite-boundary duality -> unit feedback

is therefore the golden Möbius map `m ↦ 1 + 1/m`.

This is an exact algebraic boundary-word theorem.  It does **not** assert that the
completed arithmetic boundary reservoir realizes unit feedback, and it does not
prove RH.

The file also records a useful no-go.  The tempting response `2B/A` cannot be
identified with Suzuki's normalized Herglotz/Weyl function: `A(i)=0`, so the
projective response degenerates at the normalization point, whereas the normalized
Weyl function equals `i` when the opposite boundary coordinate is nonzero.
-/

namespace GppGoldenMobius

open GppWeilParity

noncomputable section

/-- The finite Suzuki Weyl coordinate associated with the 0/pi extension pair:
    `m = -i W_pi/W_0 = -i (A-B)/(A+B)`. -/
def physicalWeyl (I : ℂ → ℂ) (z : ℂ) : ℂ :=
  -Complex.I * (suzukiA I z - suzukiB I z) /
    (suzukiA I z + suzukiB I z)

/-- Spectral reflection makes the physical Weyl coordinate odd. -/
theorem physicalWeyl_neg (I : ℂ → ℂ) (z : ℂ) :
    physicalWeyl I (-z) = -physicalWeyl I z := by
  unfold physicalWeyl
  rw [suzukiA_neg_eq_neg_suzukiB, suzukiB_neg_eq_neg_suzukiA]
  ring

/-- The canonical opposite-boundary Weyl coordinate is the negative reciprocal. -/
def weylBoundaryDual (m : ℂ) : ℂ := -1 / m

/--
The missing operation in the naive reflection-plus-feedback word is the canonical
opposite-boundary duality.  Reflection, then negative reciprocal duality, then unit
feedback is exactly the golden map.
-/
theorem weyl_reflect_dual_feedback_golden (m : ℂ) :
    weylFeedback (weylBoundaryDual (weylReflection m)) = goldenMapC m := by
  simp [weylFeedback, weylBoundaryDual, weylReflection, goldenMapC, add_comm]

/-- Standard scalar Krein rank-one feedback. -/
def kreinFeedback (r : ℂ) : ℂ := r / (1 + r)

/-- Reciprocal response linearizes unit Krein feedback to translation by +1. -/
theorem reciprocal_kreinFeedback
    {r : ℂ} (hr : r ≠ 0) (hr1 : 1 + r ≠ 0) :
    1 / kreinFeedback r = 1 / r + 1 := by
  unfold kreinFeedback
  field_simp [hr, hr1]
  ring

/-- The deficiency coordinate `A` has its forced normalization zero at `z=i`. -/
theorem suzukiA_at_I_eq_zero (I : ℂ → ℂ) :
    suzukiA I Complex.I = 0 := by
  simp [suzukiA]

/-- Consequently the raw projective ratio `A/B` vanishes at `z=i`. -/
theorem suzukiRatio_at_I_eq_zero (I : ℂ → ℂ) :
    suzukiRatio I Complex.I = 0 := by
  unfold suzukiRatio
  rw [suzukiA_at_I_eq_zero]
  simp

/--
Hence the algebraic response coordinate `2/(A/B)`, interpreted in Lean's total
field convention, degenerates to zero at the Suzuki normalization point.  In
particular it cannot itself be the normalized Weyl function, whose value there is
nonzero.
-/
theorem responseFromRatio_at_I_eq_zero (I : ℂ → ℂ) :
    responseFromRatio (suzukiRatio I Complex.I) = 0 := by
  rw [suzukiRatio_at_I_eq_zero]
  simp [responseFromRatio]

/-- If `B(i)` is nonzero, the physical Suzuki Weyl coordinate is normalized by
    `m(i)=i`. -/
theorem physicalWeyl_at_I
    (I : ℂ → ℂ) (hB : suzukiB I Complex.I ≠ 0) :
    physicalWeyl I Complex.I = Complex.I := by
  unfold physicalWeyl
  rw [suzukiA_at_I_eq_zero]
  field_simp [hB]
  ring

/-- The raw response `2B/A` and the normalized physical Weyl function are therefore
    provably different at the canonical normalization point whenever `B(i) ≠ 0`. -/
theorem responseFromRatio_ne_physicalWeyl_at_I
    (I : ℂ → ℂ) (hB : suzukiB I Complex.I ≠ 0) :
    responseFromRatio (suzukiRatio I Complex.I) ≠ physicalWeyl I Complex.I := by
  rw [responseFromRatio_at_I_eq_zero, physicalWeyl_at_I I hB]
  exact Ne.symm Complex.I_ne_zero

end

end GppGoldenMobius
