import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basic
import Mathlib.Data.Complex.Basic

/-!
# Orientation core of the googly problem

This file isolates the part of the proposed googly mechanism that is already
pure mathematics and separates it from the genuinely open twistor/Penrose step.

In oriented Lorentzian four-dimensional geometry the Hodge operator on two-forms
changes sign when the spacetime orientation is reversed.  After complexification,
self-dual and anti-self-dual sectors are the ±i eigenspaces.  Therefore orientation
reversal exchanges those eigenspaces exactly.

We formalize that algebra abstractly over a complex vector space, then package the
remaining twistor statement as a commuting-square criterion: any twistor map whose
Penrose transform intertwines with the bulk orientation reversal automatically gives
an ASD↔SD googly map.  Existence of that twistor map is NOT assumed or claimed here.
-/

namespace GppOrientationGoogly

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Abstract Hodge operator on the complexified two-form space. -/
def IsSelfDual (star : V → V) (F : V) : Prop := star F = Complex.I • F

/-- Anti-self-dual sector, the `-i` eigenspace. -/
def IsAntiSelfDual (star : V → V) (F : V) : Prop := star F = (-Complex.I) • F

/-- Reversing the underlying spacetime orientation sends `star` to `-star`. -/
def reversedHodge (star : V → V) : V → V := fun F => -(star F)

/-- Exact orientation theorem: a self-dual field becomes anti-self-dual when the
orientation is reversed. -/
theorem selfDual_to_antiSelfDual_under_orientation_reversal
    (star : V → V) (F : V) (hF : IsSelfDual star F) :
    IsAntiSelfDual (reversedHodge star) F := by
  unfold IsSelfDual at hF
  unfold IsAntiSelfDual reversedHodge
  rw [hF]
  simp

/-- Exact converse: an anti-self-dual field becomes self-dual under orientation reversal. -/
theorem antiSelfDual_to_selfDual_under_orientation_reversal
    (star : V → V) (F : V) (hF : IsAntiSelfDual star F) :
    IsSelfDual (reversedHodge star) F := by
  unfold IsAntiSelfDual at hF
  unfold IsSelfDual reversedHodge
  rw [hF]
  simp

/-- Reversing orientation twice restores the original Hodge operator. -/
theorem reversedHodge_involution (star : V → V) :
    reversedHodge (reversedHodge star) = star := by
  funext F
  simp [reversedHodge]

/-! ## The exact remaining googly criterion

Let `Tw` be a twistor-data space, `Bulk` the bulk complexified curvature space,
`Pminus` the Penrose transform into one helicity sector, and `Pplus` the transform
into the opposite sector.  A candidate googly map `G` solves the linearized exchange
problem if the square commutes with the bulk orientation reversal `R`:

    Tw  --G-->  Tw
     |          |
   Pminus      Pplus
     |          |
     v          v
    Bulk --R--> Bulk

The theorem below is deliberately taut but useful: once the commuting square and
sector exchange of `R` are established from geometry, the googly conclusion is no
longer an independent assumption.
-/

variable {Tw Bulk : Type*}

structure GooglyIntertwiner where
  G : Tw → Tw
  R : Bulk → Bulk
  Pminus : Tw → Bulk
  Pplus : Tw → Bulk
  commute : ∀ z, Pplus (G z) = R (Pminus z)

/-- A commuting Penrose/orientation square transports every property of the
orientation-reversed bulk image to the googly image. -/
theorem googly_of_intertwiner
    (Sminus Splus : Bulk → Prop)
    (g : GooglyIntertwiner (Tw := Tw) (Bulk := Bulk))
    (hexchange : ∀ F, Sminus F → Splus (g.R F))
    (z : Tw) (hz : Sminus (g.Pminus z)) :
    Splus (g.Pplus (g.G z)) := by
  rw [g.commute]
  exact hexchange _ hz

/-- If the bulk reversal is involutive and the two Penrose transforms are injective,
then a two-sided commuting googly map is itself involutive.  This is one concrete
closure criterion for a genuine two-sector reconstruction. -/
theorem googly_involutive_of_two_sided_intertwiner
    (G : Tw → Tw) (R : Bulk → Bulk) (P : Tw → Bulk)
    (hcomm : ∀ z, P (G z) = R (P z))
    (hR : ∀ F, R (R F) = F)
    (hP : Function.Injective P) :
    ∀ z, G (G z) = z := by
  intro z
  apply hP
  rw [hcomm, hcomm, hR]

/-! ## Celestial label check

For a celestial primary label `(Delta,J)`, ordinary shadow sends
`(Delta,J) ↦ (2-Delta,-J)`.  This is an exact involution and flips helicity/spin
label.  It does not act on any internal charge label because none appears here.
-/

structure CelestialLabel where
  Delta : ℂ
  J : ℤ
  deriving DecidableEq

noncomputable def shadowLabel (x : CelestialLabel) : CelestialLabel :=
  ⟨2 - x.Delta, -x.J⟩

theorem shadowLabel_involution (x : CelestialLabel) :
    shadowLabel (shadowLabel x) = x := by
  cases x
  simp [shadowLabel]
  ring

theorem shadowLabel_flips_helicity (x : CelestialLabel) :
    (shadowLabel x).J = -x.J := by
  rfl

end GppOrientationGoogly
