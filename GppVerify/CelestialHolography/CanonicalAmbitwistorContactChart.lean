import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbitwistorSecondOrderIncidence
import GppVerify.CelestialHolography.AmbitwistorContactNeutralCone

/-!
# Canonical flat ambitwistor contact chart

Penrose's TN41 strong-incidence condition is written in twistor/dual-twistor increments as

    dZ . dW = 0.

The homogeneous Lagrangian-contact model writes the same rank-four contact screen as a pair
of two-vectors `(X,Y)` with contact-null equation

    X . Y = 0.

Earlier modules deliberately left the coordinate chart between these descriptions external.
This file closes that gap at one canonical flat ambitwistor point.  Take

    Z0 = (1,0,0,0),    W0 = (0,0,0,1),    Z0.W0 = 0.

Fix the ordinary projective tangent gauges `dZ_0=0` and `dW_3=0`.  The two contact/weak-
incidence equations then set `dZ_3=0` and `dW_0=0`, leaving exactly

    dZ = (0,X0,X1,0),    dW = (0,Y0,Y1,0).

In these coordinates

    dZ.dW = X0 Y0 + X1 Y1,

which is precisely the half-pairing whose double is the neutral contact quadratic form.
Thus Penrose strong incidence is *exactly* the contact-null cone in this canonical chart.

This is a genuine local flat chart theorem, not yet the global projective/curved theorem.
Because flat ambitwistor space is homogeneous, the next step is to transport this chart by
the appropriate projective group action and then prove compatibility with curved sky/Jacobi
reconstruction.  No such global transport is asserted here.
-/

namespace GppCanonicalAmbitwistorContactChart

open GppTwistorAnnihilatorIncidence
open GppTaggedAmbitwistorParity
open GppAmbitwistorSecondOrderIncidence
open GppAmbitwistorContactNeutralCone

/-- Canonical incident twistor/dual-twistor pair. -/
def canonicalAmbitwistor : Ambitwistor where
  z := ⟨(1,0,0,0)⟩
  w := ⟨(0,0,0,1)⟩
  incident := by
    norm_num [pairing, pair4]

/-- Embed the left contact half as a gauge-fixed twistor tangent. -/
def chartDz (u : ContactVector) : Twistor :=
  ⟨(0,u.1.1,u.1.2,0)⟩

/-- Embed the right contact half as a gauge-fixed dual-twistor tangent. -/
def chartDw (u : ContactVector) : DualTwistor :=
  ⟨(0,u.2.1,u.2.2,0)⟩

/-- Coordinates read back from the two middle components of arbitrary increments. -/
def contactCoords (dz : Twistor) (dw : DualTwistor) : ContactVector :=
  ((dz.val.2.1,dz.val.2.2.1),(dw.val.2.1,dw.val.2.2.1))

/-- Ordinary projective tangent gauge at `Z0`: remove the component along `Z0`. -/
def LeftProjectiveGauge (dz : Twistor) : Prop := dz.val.1 = 0

/-- Dual projective tangent gauge at `W0`: remove the component along `W0`. -/
def RightProjectiveGauge (dw : DualTwistor) : Prop := dw.val.2.2.2 = 0

/-- Every chart increment satisfies both weak-incidence/contact equations. -/
theorem chart_weak_incidence (u : ContactVector) :
    WeakLeft canonicalAmbitwistor.w (chartDz u) ∧
    WeakRight canonicalAmbitwistor.z (chartDw u) := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  norm_num [WeakLeft, WeakRight, canonicalAmbitwistor, chartDz, chartDw, pair4]

/-- Hence every chart increment is tangent to the incidence quadric. -/
theorem chart_tangent_incidence (u : ContactVector) :
    TangentIncidence canonicalAmbitwistor.z canonicalAmbitwistor.w
      (chartDz u) (chartDw u) := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  norm_num [TangentIncidence, canonicalAmbitwistor, chartDz, chartDw, pair4]

/-- The second-order twistor pairing is exactly the contact half-pairing. -/
theorem chart_secondOrder_pair_eq_halfPair (u : ContactVector) :
    pair4 (chartDz u).val (chartDw u).val = halfPair u.1 u.2 := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  simp [chartDz, chartDw, pair4, halfPair]
  ring

/-- Main local bridge: Penrose strong incidence is exactly the neutral contact-null cone. -/
theorem strongSecondOrder_iff_neutralQ_zero (u : ContactVector) :
    StrongSecondOrder (chartDz u) (chartDw u) ↔ neutralQ u = 0 := by
  unfold StrongSecondOrder
  rw [chart_secondOrder_pair_eq_halfPair]
  symm
  exact neutralQ_zero_iff_halfPair_zero u

/-- Exact affine-incidence expansion in canonical contact coordinates. -/
theorem perturbed_pairing_in_contact_chart (t : ℝ) (u : ContactVector) :
    pairing
        (perturbTwistor t canonicalAmbitwistor.z (chartDz u))
        (perturbDualTwistor t canonicalAmbitwistor.w (chartDw u)) =
      t*t * halfPair u.1 u.2 := by
  rw [perturbed_pairing_is_second_order
        t canonicalAmbitwistor (chartDz u) (chartDw u)
        (chart_tangent_incidence u)]
  rw [chart_secondOrder_pair_eq_halfPair]

/-- The same expansion expressed directly through the neutral contact norm. -/
theorem perturbed_pairing_eq_half_neutralQ (t : ℝ) (u : ContactVector) :
    pairing
        (perturbTwistor t canonicalAmbitwistor.z (chartDz u))
        (perturbDualTwistor t canonicalAmbitwistor.w (chartDw u)) =
      (t*t/2) * neutralQ u := by
  rw [perturbed_pairing_in_contact_chart, neutralQ_eq_twice_halfPair]
  ring

/-- In the canonical gauge, weak incidence kills the fourth component of `dZ`. -/
theorem weakLeft_canonical_forces_last_zero
    (dz : Twistor)
    (h : WeakLeft canonicalAmbitwistor.w dz) :
    dz.val.2.2.2 = 0 := by
  unfold WeakLeft at h
  rcases dz with ⟨⟨z0,z1,z2,z3⟩⟩
  norm_num [canonicalAmbitwistor, pair4] at h ⊢
  exact h

/-- In the canonical gauge, opposite weak incidence kills the first component of `dW`. -/
theorem weakRight_canonical_forces_first_zero
    (dw : DualTwistor)
    (h : WeakRight canonicalAmbitwistor.z dw) :
    dw.val.1 = 0 := by
  unfold WeakRight at h
  rcases dw with ⟨⟨w0,w1,w2,w3⟩⟩
  norm_num [canonicalAmbitwistor, pair4] at h ⊢
  exact h

/-- Conversely, every gauge-fixed contact tangent at the canonical point is uniquely of the
`(X,Y)` chart form.  This proves that the displayed four coordinates span the entire
projectivized contact hyperplane in this gauge, rather than merely giving a subspace. -/
theorem gaugeFixed_contact_parameterized
    (dz : Twistor) (dw : DualTwistor)
    (hLg : LeftProjectiveGauge dz)
    (hRg : RightProjectiveGauge dw)
    (hL : WeakLeft canonicalAmbitwistor.w dz)
    (hR : WeakRight canonicalAmbitwistor.z dw) :
    dz = chartDz (contactCoords dz dw) ∧
    dw = chartDw (contactCoords dz dw) := by
  have hz3 := weakLeft_canonical_forces_last_zero dz hL
  have hw0 := weakRight_canonical_forces_first_zero dw hR
  rcases dz with ⟨⟨z0,z1,z2,z3⟩⟩
  rcases dw with ⟨⟨w0,w1,w2,w3⟩⟩
  simp [LeftProjectiveGauge, RightProjectiveGauge] at hLg hRg
  simp at hz3 hw0
  subst z0
  subst z3
  subst w0
  subst w3
  simp [contactCoords, chartDz, chartDw]

/-- Therefore, on the full gauge-fixed contact tangent space, strong incidence is precisely
neutral nullity of the extracted contact coordinates. -/
theorem gaugeFixed_strong_iff_contactNull
    (dz : Twistor) (dw : DualTwistor)
    (hLg : LeftProjectiveGauge dz)
    (hRg : RightProjectiveGauge dw)
    (hL : WeakLeft canonicalAmbitwistor.w dz)
    (hR : WeakRight canonicalAmbitwistor.z dw) :
    StrongSecondOrder dz dw ↔ neutralQ (contactCoords dz dw) = 0 := by
  rcases gaugeFixed_contact_parameterized dz dw hLg hRg hL hR with ⟨hdz,hdw⟩
  rw [hdz, hdw]
  exact strongSecondOrder_iff_neutralQ_zero (contactCoords dz dw)

end GppCanonicalAmbitwistorContactChart
