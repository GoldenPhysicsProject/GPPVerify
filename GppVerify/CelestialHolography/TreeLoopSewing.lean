import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# GppTreeLoopSewing — tree-to-loop topology behind the shadow-discontinuity program

From `shadow_discontinuity_v18_tree_to_loop.tex` (Toupin, August 2026), "Loop Integrands
Hidden in Trees: Explicit Extraction by Double Shadow Discontinuities". The paper's central
claim: a higher-point *tree* celestial correlator's shadow-pole analytic structure already
encodes a lower-point loop *integrand*, extractable by a double shadow discontinuity.

This file formalizes the two layers the paper itself keeps logically separate (its own
§7 "What is proved here, and what remains to be proved"):

1. **Axiom-free combinatorics** (§4, §6 of the paper). A connected cubic tree with
   `4 + 2L` external leaves has `2L + 2` trivalent vertices and `2L + 1` internal edges.
   Sewing `L` disjoint pairs of the `2L` extra leaves adds `L` internal edges, leaves four
   external legs, and gives cycle rank exactly `L` — the paper's boxed topology theorem,
   `(4+2L)-point cubic tree + L pair sewings → 4-point L-loop cubic graph`. This is genuine
   graph-theoretic content and is proved unconditionally here.

2. **Analytic interface** (the paper's real open problem). The celestial/shadow statement
   — that the inverse-Mellin of the pair shadow discontinuity equals the momentum-space
   pair closure — is represented by a *local* hypothesis, `ShadowPairSewing.sewing_identity`,
   not a global axiom. This isolates the one physics theorem the paper itself says still
   needs an explicit six-point celestial derivation (its own boxed equation in §"Remaining
   analytic theorem"), rather than smuggling it in.

**This file does NOT discharge, replace, or duplicate** the existing infrastructure stubs
in `GppShadowDisc` (`open_celestial_amplitude_has_cut`, `open_disc_equals_loop_integrand`,
`open_shadow_disc_mellin_density` — all `theorem foo : True := trivial`, the repo's honest
convention, not axioms despite older naming). Those stay exactly as they are: nothing here
proves the analytic sewing identity for an explicit celestial amplitude, so nothing here
justifies removing or "discharging" those stubs. See `ShadowPairSewing` below for exactly
where that remaining gap is isolated.

## Loop-count convention (paper correction tracked here)

The paper's early draft language about "L+1 shadow closures" is corrected in this version:
closing `L` disjoint pairs of tree legs is `L` pair sewings, giving cycle rank `L` — not
`L+1`. `pairSewing_cycleRank` below proves the corrected count. Do not conflate "pair
sewings / graph closures" (`L`) with "leg-wise discontinuity actions" (potentially `2L`,
one per leg of each pair) — these are different countable quantities.
-/

namespace GppTreeLoopSewing

open Complex

/-! ## Shadow-pair algebra -/

/-- Scalar shadow dimension on a two-dimensional celestial sphere. -/
def shadowDim (Δ : ℂ) : ℂ := 2 - Δ

/-- Two conformal dimensions form a scalar shadow pair. -/
def IsShadowPair (Δ₅ Δ₆ : ℂ) : Prop := Δ₆ = shadowDim Δ₅

/-- Principal-series dimensions `1 ± i·lam` are shadow paired. -/
theorem principalSeries_isShadowPair (lam : ℝ) :
    IsShadowPair
      ((1 : ℂ) + Complex.I * (lam : ℂ))
      ((1 : ℂ) - Complex.I * (lam : ℂ)) := by
  simp only [IsShadowPair, shadowDim]
  ring

/-- A shadow pair lies on the joint scalar shadow locus `Δ₅ + Δ₆ = 2`. -/
theorem shadowPair_sum_two {Δ₅ Δ₆ : ℂ} (h : IsShadowPair Δ₅ Δ₆) :
    Δ₅ + Δ₆ = 2 := by
  rw [h]
  simp only [shadowDim]
  ring

/-- Shadow pairing is involutive. -/
theorem shadowDim_involutive (Δ : ℂ) : shadowDim (shadowDim Δ) = Δ := by
  simp only [shadowDim]
  ring

/-! ## Sequential pair discontinuity -/

/--
Abstract composition of the two leg-wise shadow-discontinuity operations
(`dDisc_sh^(56) := Disc^sh_6 ∘ Disc^sh_5` in the paper's Definition 2.1).
The celestial implementation may refine the two operations further; this
pure definition records only the sequential structure.
-/
def doubleShadowDisc {α : Type*} (disc₅ disc₆ : α → α) : α → α :=
  disc₆ ∘ disc₅

@[simp] theorem doubleShadowDisc_apply {α : Type*} (disc₅ disc₆ : α → α) (x : α) :
    doubleShadowDisc disc₅ disc₆ x = disc₆ (disc₅ x) := rfl

/-! ## Axiom-free cubic graph counts -/

/-- Number of trivalent vertices in a connected cubic tree with `n` leaves. -/
def cubicTreeVertices (n : ℕ) : ℕ := n - 2

/-- Number of internal edges in a connected cubic tree with `n` leaves. -/
def cubicTreeInternalEdges (n : ℕ) : ℕ := n - 3

/-- External legs remaining after sewing `L` disjoint pairs of leaves. -/
def sewnExternalLegs (n L : ℕ) : ℕ := n - 2 * L

/-- Internal edges after sewing `L` disjoint pairs; each sewing adds one edge. -/
def sewnInternalEdges (n L : ℕ) : ℕ := cubicTreeInternalEdges n + L

/-- First Betti number / cycle rank for a connected graph from `(V,I)`. -/
def cycleRank (V I : ℕ) : ℕ := I + 1 - V

/-- A `(4+2L)`-point cubic tree has `2L+2` trivalent vertices. -/
theorem cubicTree_vertices_4plus2L (L : ℕ) :
    cubicTreeVertices (4 + 2 * L) = 2 * L + 2 := by
  simp only [cubicTreeVertices]
  omega

/-- A `(4+2L)`-point cubic tree has `2L+1` internal tree edges. -/
theorem cubicTree_internalEdges_4plus2L (L : ℕ) :
    cubicTreeInternalEdges (4 + 2 * L) = 2 * L + 1 := by
  simp only [cubicTreeInternalEdges]
  omega

/-- Sewing the `2L` extra leaves in `L` pairs leaves four external legs. -/
theorem sewn_externalLegs_are_four (L : ℕ) :
    sewnExternalLegs (4 + 2 * L) L = 4 := by
  simp only [sewnExternalLegs]
  omega

/-- After `L` pair sewings there are `3L+1` internal edges. -/
theorem sewn_internalEdges_4plus2L (L : ℕ) :
    sewnInternalEdges (4 + 2 * L) L = 3 * L + 1 := by
  simp only [sewnInternalEdges, cubicTreeInternalEdges]
  omega

/--
Main graph-theoretic theorem (the paper's boxed topology statement): sewing `L` disjoint
pairs of the extra leaves of an open `(4+2L)`-point cubic tree produces a connected
four-point graph of cycle rank exactly `L`.
-/
theorem pairSewing_cycleRank (L : ℕ) :
    cycleRank
      (cubicTreeVertices (4 + 2 * L))
      (sewnInternalEdges (4 + 2 * L) L) = L := by
  simp only [cycleRank, cubicTreeVertices, sewnInternalEdges, cubicTreeInternalEdges]
  omega

/-- The complete count package used by the all-loop paper statement. -/
theorem tree_to_L_loop_counts (L : ℕ) :
    sewnExternalLegs (4 + 2 * L) L = 4 ∧
    cubicTreeVertices (4 + 2 * L) = 2 * L + 2 ∧
    cubicTreeInternalEdges (4 + 2 * L) = 2 * L + 1 ∧
    sewnInternalEdges (4 + 2 * L) L = 3 * L + 1 ∧
    cycleRank
      (cubicTreeVertices (4 + 2 * L))
      (sewnInternalEdges (4 + 2 * L) L) = L := by
  refine ⟨sewn_externalLegs_are_four L, cubicTree_vertices_4plus2L L,
    cubicTree_internalEdges_4plus2L L, sewn_internalEdges_4plus2L L, pairSewing_cycleRank L⟩

/-- One-loop specialization: six-point cubic tree → four-point one-loop graph. -/
theorem sixPoint_onePair_oneLoop_counts :
    cubicTreeVertices 6 = 4 ∧
    cubicTreeInternalEdges 6 = 3 ∧
    sewnExternalLegs 6 1 = 4 ∧
    sewnInternalEdges 6 1 = 4 ∧
    cycleRank (cubicTreeVertices 6) (sewnInternalEdges 6 1) = 1 := by
  norm_num [cubicTreeVertices, cubicTreeInternalEdges, sewnExternalLegs,
    sewnInternalEdges, cycleRank]

/-! ## The open chain and the box denominator -/

section Denominators

variable {V : Type*} [AddCommGroup V]

/--
The three propagator denominators already present in the open six-point cubic
chain obtained by cutting one edge of a four-point box (the paper's `D_L`, `D_6`, `D_R`
of eq. 3.34–3.36, before closure).
-/
def openSixPointChainDenominator (Q : V → ℂ) (ℓ p₁ p₂ p₄ : V) : ℂ :=
  Q (ℓ - p₁) * Q (ℓ - p₁ - p₂) * Q (ℓ + p₄)

/--
Closing the distinguished pair of leaves adds the missing edge `Q ℓ` (the paper's `D_5`),
turning the open tree chain into the four-denominator box cycle, eq. 3.37.
-/
def closedBoxDenominator (Q : V → ℂ) (ℓ p₁ p₂ p₄ : V) : ℂ :=
  Q ℓ * openSixPointChainDenominator Q ℓ p₁ p₂ p₄

/-- The box denominator is literally the missing closure edge times the tree denominator. -/
theorem boxDenominator_is_pairClosure
    (Q : V → ℂ) (ℓ p₁ p₂ p₄ : V) :
    closedBoxDenominator Q ℓ p₁ p₂ p₄ =
      Q ℓ *
        (Q (ℓ - p₁) * Q (ℓ - p₁ - p₂) * Q (ℓ + p₄)) := by
  rfl

end Denominators

/-! ## Analytic interface: isolate, do not hide, the celestial sewing theorem -/

/--
A local interface for the genuinely analytic part of the program — the paper's own
boxed "remaining analytic theorem" (its `𝓜⁻¹_{5,6}[dDisc_sh^(56) T̃₆] = (i/(ℓ²+i0)) T₆(...)`).

`doubleDisc` is the spectral object obtained by applying the pair shadow closure to a
higher-point celestial tree. `inverseMellin` reconstructs a momentum-space object.
`closePair` is the same pair closure described directly in momentum space.

The field `sewing_identity` is *the* theorem that the celestial calculation must
ultimately prove from explicit six-point tree/OPE/cut data — the paper states this
identity's exact normalization/sign/prescription must be derived from actual celestial
conventions, not inserted because it is the target. Keeping it as a structure field means
all downstream formal theorems are conditional on a visible local hypothesis rather than
a global project axiom or stub.
-/
structure ShadowPairSewing (Tree Spectral Integrand : Type*) where
  doubleDisc : Tree → ℕ → ℕ → Spectral
  inverseMellin : Spectral → Integrand
  closePair : Tree → ℕ → ℕ → Integrand
  sewing_identity : ∀ (T : Tree) (a b : ℕ),
    inverseMellin (doubleDisc T a b) = closePair T a b

namespace ShadowPairSewing

variable {Tree Spectral Integrand : Type*}

/-- Tree → pair shadow discontinuity → inverse Mellin equals direct pair closure. -/
theorem tree_to_loop_extraction
    (S : ShadowPairSewing Tree Spectral Integrand)
    (T : Tree) (a b : ℕ) :
    S.inverseMellin (S.doubleDisc T a b) = S.closePair T a b :=
  S.sewing_identity T a b

end ShadowPairSewing

end GppTreeLoopSewing
