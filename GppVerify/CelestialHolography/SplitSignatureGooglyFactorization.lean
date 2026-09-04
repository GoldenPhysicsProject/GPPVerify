import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# Split-signature factorization of celestial shadow data

In split signature the two real spinor factors are independent and the celestial
boundary carries independent left/right conformal weights `(h, hbar)`.  The two
light transforms act on one factor at a time,

  L  : (h,hbar) |-> (1-h,hbar),
  Lb : (h,hbar) |-> (h,1-hbar).

Their composition is the ordinary two-dimensional shadow reflection

  (h,hbar) |-> (1-h,1-hbar).

Writing `Delta = h+hbar` and `J = h-hbar`, this gives exactly

  (Delta,J) |-> (2-Delta,-J).

This file formalizes only this weight algebra.  The analytic theorem identifying
these reflections with normalized light/half-Fourier transforms on actual states is
separate, as is the Penrose-transform theorem needed for a genuine linear googly
resolution.
-/

namespace GppSplitSignatureGooglyFactorization

structure LRLabel where
  h : ℂ
  hbar : ℂ
  deriving DecidableEq

noncomputable def Delta (x : LRLabel) : ℂ := x.h + x.hbar
noncomputable def spinJ (x : LRLabel) : ℂ := x.h - x.hbar

/-- Left light transform: reflect only the left SL(2,R) weight. -/
noncomputable def leftLight (x : LRLabel) : LRLabel :=
  ⟨1 - x.h, x.hbar⟩

/-- Right/dual light transform: reflect only the right SL(2,R) weight. -/
noncomputable def rightLight (x : LRLabel) : LRLabel :=
  ⟨x.h, 1 - x.hbar⟩

/-- Full split-signature shadow transform. -/
noncomputable def fullShadow (x : LRLabel) : LRLabel :=
  ⟨1 - x.h, 1 - x.hbar⟩

/-- Each chiral light reflection is an involution. -/
theorem leftLight_involutive (x : LRLabel) :
    leftLight (leftLight x) = x := by
  cases x
  simp [leftLight]
  ring

theorem rightLight_involutive (x : LRLabel) :
    rightLight (rightLight x) = x := by
  cases x
  simp [rightLight]
  ring

/-- The left and right light transforms commute because they act on independent factors. -/
theorem light_transforms_commute (x : LRLabel) :
    leftLight (rightLight x) = rightLight (leftLight x) := by
  cases x
  rfl

/-- Their composition is exactly the full shadow reflection. -/
theorem fullShadow_eq_left_right (x : LRLabel) :
    fullShadow x = leftLight (rightLight x) := by
  cases x
  rfl

/-- Consequently the full shadow is itself involutive. -/
theorem fullShadow_involutive (x : LRLabel) :
    fullShadow (fullShadow x) = x := by
  cases x
  simp [fullShadow]
  constructor <;> ring

/-- Full shadow sends conformal dimension `Delta` to `2-Delta`. -/
theorem fullShadow_Delta (x : LRLabel) :
    Delta (fullShadow x) = 2 - Delta x := by
  cases x
  simp [Delta, fullShadow]
  ring

/-- Full shadow reverses the left-right spin/helicity label. -/
theorem fullShadow_spinJ (x : LRLabel) :
    spinJ (fullShadow x) = - spinJ x := by
  cases x
  simp [spinJ, fullShadow]
  ring

/-- Package form of the celestial shadow label map. -/
theorem fullShadow_Delta_spin (x : LRLabel) :
    Delta (fullShadow x) = 2 - Delta x ∧
    spinJ (fullShadow x) = - spinJ x := by
  exact ⟨fullShadow_Delta x, fullShadow_spinJ x⟩

/-- A left light transform alone changes `Delta` and `J` in the same direction. -/
theorem leftLight_Delta (x : LRLabel) :
    Delta (leftLight x) = 1 - spinJ x := by
  cases x
  simp [Delta, spinJ, leftLight]
  ring

/-- A right light transform alone changes `Delta` and `J` in the opposite direction. -/
theorem rightLight_Delta (x : LRLabel) :
    Delta (rightLight x) = 1 + spinJ x := by
  cases x
  simp [Delta, spinJ, rightLight]
  ring

/-- The full reflection is not a mysterious extra operation: in split signature it
factorizes into two commuting chiral reflections. -/
theorem split_shadow_factorization (x : LRLabel) :
    fullShadow x = leftLight (rightLight x) ∧
    fullShadow x = rightLight (leftLight x) := by
  constructor
  · exact fullShadow_eq_left_right x
  · rw [light_transforms_commute]
    exact fullShadow_eq_left_right x

end GppSplitSignatureGooglyFactorization
