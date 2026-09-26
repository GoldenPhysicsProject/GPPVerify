import Mathlib.Tactic

/-!
# Four-block chiral curvature algebra

There are two closely related four-block decompositions in four-dimensional gravity.

(1) The 1995 Iyer--Kozameh--Newman holonomy formulation decomposes an O(3,1) curvature by
spacetime duality (left sign) and internal Lorentz duality (right sign):

  F = ^+F^+ + ^+F^- + ^-F^+ + ^-F^-.

After the gravitational/soldering restriction, they explain that the vacuum Einstein
condition is almost encoded by vanishing of the two mixed blocks

  ^+F^- = 0,   ^-F^+ = 0,

while the two diagonal chiral sectors remain simultaneously present.

(2) The standard Riemann curvature operator acts on

  Lambda^2 = Lambda^2_+ ⊕ Lambda^2_-

and has block form

  R = [[W^+ + s/12, B], [B*, W^- + s/12]],

where `B` is trace-free Ricci.  Einstein is exactly the condition that the two off-diagonal
blocks vanish.  Reversing the four-orientation swaps both the domain and codomain Hodge
splittings, so the same curvature operator is represented by the block-conjugated matrix
which exchanges the two diagonal blocks and exchanges the two off-diagonal blocks.

This file formalizes only the exact four-slot bookkeeping common to those statements.  It
does NOT formalize an O(3,1) connection, a soldering form, a Riemann tensor, Yang--Mills
equations, or the geometric theorem identifying the off-diagonal block with trace-free
Ricci.  Those remain external inputs.
-/

namespace GppEinsteinChiralCurvatureBlocks

variable {K : Type*} [Zero K]

/-- Generic four-block carrier.  It can be read either as the spacetime/internal-duality
split of the holonomy paper or as the domain/codomain Hodge split of the Riemann curvature
operator, provided the tags are interpreted accordingly. -/
structure CurvatureBlocks (K : Type*) where
  pp : K
  pm : K
  mp : K
  mm : K
  deriving DecidableEq

/-- Algebraic off-diagonal/mixed-block-free condition. -/
def MixedBlocksVanish (F : CurvatureBlocks K) : Prop :=
  F.pm = 0 ∧ F.mp = 0

/-- Swap only the first duality label.  In the holonomy notation this changes the spacetime
label while leaving the internal Lorentz label fixed.  It is deliberately NOT called the
Riemann-operator orientation reversal, because the latter swaps both the domain and codomain
Hodge decompositions. -/
def swapFirstDuality (F : CurvatureBlocks K) : CurvatureBlocks K :=
  ⟨F.mp, F.mm, F.pp, F.pm⟩

/-- Backward-compatible alias for the first-label swap. -/
def reverseSpacetimeDuality (F : CurvatureBlocks K) : CurvatureBlocks K :=
  swapFirstDuality F

/-- Swapping the first duality label twice restores all four blocks. -/
theorem swapFirstDuality_involution (F : CurvatureBlocks K) :
    swapFirstDuality (swapFirstDuality F) = F := by
  cases F
  rfl

/-- Backward-compatible involution theorem. -/
theorem reverseSpacetimeDuality_involution (F : CurvatureBlocks K) :
    reverseSpacetimeDuality (reverseSpacetimeDuality F) = F := by
  exact swapFirstDuality_involution F

/-- Components of the first-label swap. -/
theorem swapFirstDuality_components (F : CurvatureBlocks K) :
    (swapFirstDuality F).pp = F.mp ∧
    (swapFirstDuality F).pm = F.mm ∧
    (swapFirstDuality F).mp = F.pp ∧
    (swapFirstDuality F).mm = F.pm := by
  rfl

/-- Backward-compatible component theorem. -/
theorem reverse_spacetime_duality_components (F : CurvatureBlocks K) :
    (reverseSpacetimeDuality F).pp = F.mp ∧
    (reverseSpacetimeDuality F).pm = F.mm ∧
    (reverseSpacetimeDuality F).mp = F.pp ∧
    (reverseSpacetimeDuality F).mm = F.pm := by
  exact swapFirstDuality_components F

/-- Swap both row/domain and column/codomain chirality labels.  For the Riemann curvature
operator this is exactly the block-conjugation induced by reversing the four-orientation:
`Lambda^2_+` and `Lambda^2_-` exchange on both source and target. -/
def swapBothDualities (F : CurvatureBlocks K) : CurvatureBlocks K :=
  ⟨F.mm, F.mp, F.pm, F.pp⟩

/-- Riemann-operator orientation-reversal bookkeeping. -/
def reverseRiemannHodgeOrientation (F : CurvatureBlocks K) : CurvatureBlocks K :=
  swapBothDualities F

/-- Simultaneous duality exchange is involutive. -/
theorem swapBothDualities_involution (F : CurvatureBlocks K) :
    swapBothDualities (swapBothDualities F) = F := by
  cases F
  rfl

/-- Reversing the Hodge orientation twice restores the original curvature blocks. -/
theorem reverseRiemannHodgeOrientation_involution (F : CurvatureBlocks K) :
    reverseRiemannHodgeOrientation (reverseRiemannHodgeOrientation F) = F := by
  exact swapBothDualities_involution F

/-- Hodge-orientation reversal exchanges the two diagonal curvature sectors. -/
theorem reverseRiemannHodgeOrientation_swaps_diagonal (F : CurvatureBlocks K) :
    (reverseRiemannHodgeOrientation F).pp = F.mm ∧
    (reverseRiemannHodgeOrientation F).mm = F.pp := by
  rfl

/-- It also exchanges the two off-diagonal/mixed sectors. -/
theorem reverseRiemannHodgeOrientation_swaps_mixed (F : CurvatureBlocks K) :
    (reverseRiemannHodgeOrientation F).pm = F.mp ∧
    (reverseRiemannHodgeOrientation F).mp = F.pm := by
  rfl

/-- Therefore the mixed-block-free/Einstein block pattern is invariant under reversal of
four-orientation.  Geometrically this corresponds to the fact that Einstein-ness is
orientation-independent. -/
theorem mixedBlocksVanish_reverseRiemannHodgeOrientation (F : CurvatureBlocks K) :
    MixedBlocksVanish (reverseRiemannHodgeOrientation F) ↔ MixedBlocksVanish F := by
  simp [MixedBlocksVanish, reverseRiemannHodgeOrientation, swapBothDualities, and_comm]

/-- Backward-compatible simultaneous-swap theorem. -/
theorem mixedBlocksVanish_swapBothDualities (F : CurvatureBlocks K) :
    MixedBlocksVanish (swapBothDualities F) ↔ MixedBlocksVanish F := by
  exact mixedBlocksVanish_reverseRiemannHodgeOrientation F

/-- In an Einstein/block-diagonal configuration, orientation reversal simply exchanges the
existing two diagonal chiral sectors.  Neither sector is generated from the other. -/
theorem diagonal_pair_survives_orientation_reversal
    (Fplus Fminus : K) :
    let F : CurvatureBlocks K := ⟨Fplus,0,0,Fminus⟩
    MixedBlocksVanish F ∧
    MixedBlocksVanish (reverseRiemannHodgeOrientation F) ∧
    (reverseRiemannHodgeOrientation F).pp = Fminus ∧
    (reverseRiemannHodgeOrientation F).mm = Fplus := by
  simp [MixedBlocksVanish, reverseRiemannHodgeOrientation, swapBothDualities]

/-- Backward-compatible name. -/
theorem diagonal_pair_survives_swap
    (Fplus Fminus : K) :
    let F : CurvatureBlocks K := ⟨Fplus,0,0,Fminus⟩
    MixedBlocksVanish F ∧
    MixedBlocksVanish (swapBothDualities F) ∧
    (swapBothDualities F).pp = Fminus ∧
    (swapBothDualities F).mm = Fplus := by
  simpa [reverseRiemannHodgeOrientation] using
    diagonal_pair_survives_orientation_reversal Fplus Fminus

/-- A pure `+` diagonal configuration contains no hidden `-` diagonal component. -/
theorem pure_plus_has_no_hidden_minus (Fplus : K) :
    let F : CurvatureBlocks K := ⟨Fplus,0,0,0⟩
    F.mm = 0 := by
  rfl

end GppEinsteinChiralCurvatureBlocks
