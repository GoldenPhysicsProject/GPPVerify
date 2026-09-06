import Mathlib.Tactic
import GppVerify.CelestialHolography.TaggedAmbitwistorParity

/-!
# First-order weak incidence and Penrose's second-order strong-incidence obstruction

In TN41 (1996), Penrose distinguishes two chiral notions of weak incidence between
neighboring complex null rays.  In flat twistor/dual-twistor coordinates these are the
first-order conditions

  W . dZ = 0,        Z . dW = 0.

For a tangent deformation of the ambitwistor incidence quadric `Z.W=0`, however,

  dZ.W + Z.dW = 0,

so the two weak-incidence conditions are equivalent to first order.  Penrose emphasizes
that *strong* incidence only appears at second order, through the additional quadratic
condition

  dZ.dW = 0.

This module formalizes that observation exactly.  If `(Z,W)` is incident and `(dZ,dW)`
is tangent to the incidence quadric, then along the affine perturbation

  Z_t = Z + t dZ,    W_t = W + t dW,

one has the exact polynomial identity

  Z_t.W_t = t^2 (dZ.dW).

Thus the first-order contact hyperplane cannot distinguish the two chiral weak-incidence
branches; the obstruction to remaining incident is genuinely second order.  This is a
finite flat-incidence theorem.  The interpretation of the second-order geometry as curved
Jacobi/Weyl data is external and is not asserted here.
-/

namespace GppAmbitwistorSecondOrderIncidence

open GppTwistorAnnihilatorIncidence
open GppTaggedAmbitwistorParity

/-- Coordinatewise addition on the common four-coordinate carrier. -/
def addV4 (x y : V4) : V4 :=
  (x.1+y.1, x.2.1+y.2.1, x.2.2.1+y.2.2.1, x.2.2.2+y.2.2.2)

/-- Scalar multiplication on the coordinate carrier. -/
def scaleV4' (t : ℝ) (x : V4) : V4 :=
  (t*x.1, t*x.2.1, t*x.2.2.1, t*x.2.2.2)

/-- Affine perturbation of a twistor coordinate. -/
def perturbTwistor (t : ℝ) (z dz : Twistor) : Twistor :=
  ⟨addV4 z.val (scaleV4' t dz.val)⟩

/-- Affine perturbation of a dual-twistor coordinate. -/
def perturbDualTwistor (t : ℝ) (w dw : DualTwistor) : DualTwistor :=
  ⟨addV4 w.val (scaleV4' t dw.val)⟩

/-- Linearized tangent condition to the incidence quadric. -/
def TangentIncidence
    (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor) : Prop :=
  pair4 dz.val w.val + pair4 z.val dw.val = 0

/-- Penrose's first chiral weak-incidence condition. -/
def WeakLeft (w : DualTwistor) (dz : Twistor) : Prop :=
  pair4 dz.val w.val = 0

/-- Penrose's opposite chiral weak-incidence condition. -/
def WeakRight (z : Twistor) (dw : DualTwistor) : Prop :=
  pair4 z.val dw.val = 0

/-- The genuinely second-order strong-incidence condition. -/
def StrongSecondOrder (dz : Twistor) (dw : DualTwistor) : Prop :=
  pair4 dz.val dw.val = 0

/-- On a tangent deformation, the two chiral weak-incidence conditions are the same
first-order hyperplane condition. -/
theorem weakLeft_iff_weakRight_on_tangent
    (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor)
    (hT : TangentIncidence z w dz dw) :
    WeakLeft w dz ↔ WeakRight z dw := by
  unfold TangentIncidence WeakLeft WeakRight at hT ⊢
  constructor <;> intro h <;> linarith

/-- Exact quadratic expansion of the incidence pairing under simultaneous affine
perturbation. -/
theorem perturbed_pairing_expansion
    (t : ℝ) (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor) :
    pairing (perturbTwistor t z dz) (perturbDualTwistor t w dw) =
      pairing z w +
      t * (pair4 dz.val w.val + pair4 z.val dw.val) +
      t*t * pair4 dz.val dw.val := by
  rcases z with ⟨⟨z0,z1,z2,z3⟩⟩
  rcases w with ⟨⟨w0,w1,w2,w3⟩⟩
  rcases dz with ⟨⟨a0,a1,a2,a3⟩⟩
  rcases dw with ⟨⟨b0,b1,b2,b3⟩⟩
  simp [pairing, perturbTwistor, perturbDualTwistor, addV4, scaleV4', pair4]
  ring

/-- Main Penrose second-order identity: base incidence plus tangent incidence cancels the
constant and linear terms exactly. -/
theorem perturbed_pairing_is_second_order
    (t : ℝ) (a : Ambitwistor)
    (dz : Twistor) (dw : DualTwistor)
    (hT : TangentIncidence a.z a.w dz dw) :
    pairing (perturbTwistor t a.z dz) (perturbDualTwistor t a.w dw) =
      t*t * pair4 dz.val dw.val := by
  rw [perturbed_pairing_expansion]
  rw [a.incident]
  have hT' : pair4 dz.val a.w.val + pair4 a.z.val dw.val = 0 := hT
  rw [hT']
  ring

/-- For any nonzero displacement parameter, remaining exactly on the incidence quadric is
equivalent to the second-order strong-incidence condition. -/
theorem perturbed_incident_iff_strongSecondOrder
    (t : ℝ) (ht : t ≠ 0) (a : Ambitwistor)
    (dz : Twistor) (dw : DualTwistor)
    (hT : TangentIncidence a.z a.w dz dw) :
    pairing (perturbTwistor t a.z dz) (perturbDualTwistor t a.w dw) = 0 ↔
      StrongSecondOrder dz dw := by
  rw [perturbed_pairing_is_second_order t a dz dw hT]
  unfold StrongSecondOrder
  constructor
  · intro h
    have htt : t*t ≠ 0 := mul_ne_zero ht ht
    exact (mul_eq_zero.mp h).resolve_left htt
  · intro h
    rw [h]
    ring

/-- If the second-order condition fails, every nonzero affine displacement immediately
leaves the incidence quadric despite satisfying the linearized tangent equation. -/
theorem tangent_but_not_strong_leaves_quadric
    (t : ℝ) (ht : t ≠ 0) (a : Ambitwistor)
    (dz : Twistor) (dw : DualTwistor)
    (hT : TangentIncidence a.z a.w dz dw)
    (hNS : ¬ StrongSecondOrder dz dw) :
    pairing (perturbTwistor t a.z dz) (perturbDualTwistor t a.w dw) ≠ 0 := by
  intro hzero
  apply hNS
  exact (perturbed_incident_iff_strongSecondOrder t ht a dz dw hT).mp hzero

end GppAmbitwistorSecondOrderIncidence
