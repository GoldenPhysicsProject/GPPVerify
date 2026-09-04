import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# Split-signature light transforms with discrete parity labels

In the split-signature celestial torus, each real projective spinor factor carries
both a continuous conformal weight and a discrete `Z2` parity under sign reversal.
The normalized light transforms reflect the continuous weights but preserve the
discrete parity labels.

This module formalizes that representation-label algebra. It does not formalize the
integral kernels or their Gamma-function normalization.
-/

namespace GppSplitSignatureLightParity

structure SplitLabel where
  h : ℂ
  hbar : ℂ
  sh : Bool
  shbar : Bool
  deriving DecidableEq

noncomputable def Delta (x : SplitLabel) : ℂ := x.h + x.hbar
noncomputable def J (x : SplitLabel) : ℂ := x.h - x.hbar

noncomputable def leftLight (x : SplitLabel) : SplitLabel :=
  ⟨1 - x.h, x.hbar, x.sh, x.shbar⟩

noncomputable def rightLight (x : SplitLabel) : SplitLabel :=
  ⟨x.h, 1 - x.hbar, x.sh, x.shbar⟩

noncomputable def shadow (x : SplitLabel) : SplitLabel :=
  ⟨1 - x.h, 1 - x.hbar, x.sh, x.shbar⟩

/-- The left light transform preserves both discrete parity labels. -/
theorem leftLight_preserves_parity (x : SplitLabel) :
    (leftLight x).sh = x.sh ∧ (leftLight x).shbar = x.shbar := by
  exact ⟨rfl, rfl⟩

/-- The dual/right light transform preserves both discrete parity labels. -/
theorem rightLight_preserves_parity (x : SplitLabel) :
    (rightLight x).sh = x.sh ∧ (rightLight x).shbar = x.shbar := by
  exact ⟨rfl, rfl⟩

/-- Each normalized light reflection is involutive at the label level. -/
theorem leftLight_involutive (x : SplitLabel) : leftLight (leftLight x) = x := by
  cases x
  simp [leftLight]
  ring

theorem rightLight_involutive (x : SplitLabel) : rightLight (rightLight x) = x := by
  cases x
  simp [rightLight]
  ring

/-- The two chiral reflections commute. -/
theorem left_right_commute (x : SplitLabel) :
    leftLight (rightLight x) = rightLight (leftLight x) := by
  cases x
  rfl

/-- Full shadow is the product of the two commuting light transforms. -/
theorem shadow_factorization (x : SplitLabel) :
    shadow x = leftLight (rightLight x) := by
  cases x
  rfl

/-- The full shadow sends `(Delta,J)` to `(2-Delta,-J)`. -/
theorem shadow_Delta_J (x : SplitLabel) :
    Delta (shadow x) = 2 - Delta x ∧ J (shadow x) = -J x := by
  cases x
  simp [Delta, J, shadow]
  constructor <;> ring

/-- Full shadow preserves the discrete sign-representation data. -/
theorem shadow_preserves_parity (x : SplitLabel) :
    (shadow x).sh = x.sh ∧ (shadow x).shbar = x.shbar := by
  exact ⟨rfl, rfl⟩

/-- Hence helicity/spin-label reversal under shadow is not a swap of the even/odd
`Z2` little-group representations. The two pieces of representation data are distinct. -/
theorem shadow_spin_flip_parity_fixed (x : SplitLabel) :
    J (shadow x) = -J x ∧
    (shadow x).sh = x.sh ∧
    (shadow x).shbar = x.shbar := by
  exact ⟨(shadow_Delta_J x).2, rfl, rfl⟩

end GppSplitSignatureLightParity
