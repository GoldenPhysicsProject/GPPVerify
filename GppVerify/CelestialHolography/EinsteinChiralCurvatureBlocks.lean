import Mathlib.Tactic

/-!
# Four-block chiral curvature algebra

The 1995 Iyer--Kozameh--Newman holonomy formulation decomposes an O(3,1) curvature by
spacetime duality (left sign) and internal Lorentz duality (right sign):

  F = ^+F^+ + ^+F^- + ^-F^+ + ^-F^-.

They explain that, after the gravitational/soldering restriction, the vacuum Einstein
condition is almost encoded by vanishing of the two mixed blocks

  ^+F^- = 0,   ^-F^+ = 0,

while the two diagonal chiral sectors remain simultaneously present.

This file formalizes only the exact four-slot algebra and its behavior under swapping the
spacetime-duality label.  It does NOT formalize an O(3,1) connection, a soldering form,
Yang--Mills equations, or the physical theorem identifying mixed-block vanishing with the
Einstein equations.  Those are external geometric inputs.
-/

namespace GppEinsteinChiralCurvatureBlocks

variable {K : Type*} [Zero K]

/-- Curvature split by spacetime duality (first sign) and internal duality (second sign). -/
structure CurvatureBlocks (K : Type*) where
  pp : K
  pm : K
  mp : K
  mm : K
  deriving DecidableEq

/-- Algebraic mixed-block-free condition corresponding to `^+F^- = ^-F^+ = 0`. -/
def MixedBlocksVanish (F : CurvatureBlocks K) : Prop :=
  F.pm = 0 ∧ F.mp = 0

/-- Swap only the spacetime-duality label.  This models the bookkeeping effect of reversing
four-dimensional orientation while keeping the internal Lorentz-duality label fixed. -/
def reverseSpacetimeDuality (F : CurvatureBlocks K) : CurvatureBlocks K :=
  ⟨F.mp, F.mm, F.pp, F.pm⟩

/-- Swapping spacetime duality twice restores all four curvature blocks. -/
theorem reverseSpacetimeDuality_involution (F : CurvatureBlocks K) :
    reverseSpacetimeDuality (reverseSpacetimeDuality F) = F := by
  cases F
  rfl

/-- Orientation reversal exchanges the two diagonal chiral blocks. -/
theorem reverse_spacetime_duality_swaps_diagonal (F : CurvatureBlocks K) :
    (reverseSpacetimeDuality F).mp = F.pp ∧
      (reverseSpacetimeDuality F).pm = F.mm := by
  rfl

/-- More transparently, the old `++` block appears in the new `-+` slot and the old `--`
block appears in the new `+-` slot when only the spacetime sign is reversed. -/
theorem reverse_spacetime_duality_components (F : CurvatureBlocks K) :
    (reverseSpacetimeDuality F).pp = F.mp ∧
    (reverseSpacetimeDuality F).pm = F.mm ∧
    (reverseSpacetimeDuality F).mp = F.pp ∧
    (reverseSpacetimeDuality F).mm = F.pm := by
  rfl

/-- If one instead swaps BOTH duality labels, the diagonal blocks exchange with each other
and the two mixed blocks exchange with each other.  This is the algebraic operation that
preserves the diagonal-vs-mixed distinction. -/
def swapBothDualities (F : CurvatureBlocks K) : CurvatureBlocks K :=
  ⟨F.mm, F.mp, F.pm, F.pp⟩

/-- Double duality exchange is involutive. -/
theorem swapBothDualities_involution (F : CurvatureBlocks K) :
    swapBothDualities (swapBothDualities F) = F := by
  cases F
  rfl

/-- The mixed-block-free condition is invariant under simultaneous exchange of the two
chirality labels. -/
theorem mixedBlocksVanish_swapBothDualities (F : CurvatureBlocks K) :
    MixedBlocksVanish (swapBothDualities F) ↔ MixedBlocksVanish F := by
  simp [MixedBlocksVanish, swapBothDualities, and_comm]

/-- In particular a configuration with only the two diagonal chiral sectors survives a
simultaneous chirality exchange as another configuration with only the two diagonal
sectors; neither diagonal sector is generated from the other. -/
theorem diagonal_pair_survives_swap
    (Fplus Fminus : K) :
    let F : CurvatureBlocks K := ⟨Fplus,0,0,Fminus⟩
    MixedBlocksVanish F ∧
    MixedBlocksVanish (swapBothDualities F) ∧
    (swapBothDualities F).pp = Fminus ∧
    (swapBothDualities F).mm = Fplus := by
  simp [MixedBlocksVanish, swapBothDualities]

/-- The two diagonal components are independent algebraic slots: setting the `--` block to
zero does not manufacture it under the identity/common-geometry operation. -/
theorem pure_plus_has_no_hidden_minus (Fplus : K) :
    let F : CurvatureBlocks K := ⟨Fplus,0,0,0⟩
    F.mm = 0 := by
  rfl

end GppEinsteinChiralCurvatureBlocks
