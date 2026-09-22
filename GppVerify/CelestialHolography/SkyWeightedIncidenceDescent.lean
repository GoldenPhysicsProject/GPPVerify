import Mathlib.Tactic
import GppVerify.CelestialHolography.SkyIncidenceDescent

/-!
# Weighted sky-incidence descent

In the null-surface formulation the scalar `Omega(x,zeta,zeta_bar)` is not literally
independent of the null direction.  The auxiliary conformal representative `h(x,zeta)`
also depends on that direction, and the first metricity equation fixes the angular
variation of `Omega` so that the physical metric is direction-independent.  There remains
the freedom `Omega -> omega(x) Omega` for an arbitrary spacetime conformal rescaling.

Thus the correct abstract descent model is a line bundle, not a globally fixed scalar
trivialization.

Let `frame(u)` be the nonzero scalar relating the local ray-dependent trivialization at an
incidence point `u : F` to a reference scale line.  A correspondence-space scalar `shat`
descends to one spacetime scale `sigma` exactly when

  shat(u) = frame(u) * sigma(point(u)).

Equivalently, the normalized quantity `shat/frame` is constant on every sky fibre.
This file proves that equivalence and the induced multiplicative transition cocycle.

The identification of the NSF first metricity equation with the differential equation for
such a `frame` is external and remains a research target.
-/

namespace GppSkyWeightedIncidenceDescent

variable {F M K : Type*} [Field K]

/-- Normalized value of a ray-dependent scalar in a chosen nonzero local scale frame. -/
def normalizedValue (frame shat : F → K) (u : F) : K := shat u / frame u

/-- Weighted sky-basicness: after dividing out the ray-dependent local frame, all rays
through one spacetime point give the same scale value. -/
def WeightedSkyBasic
    (point : F → M) (frame shat : F → K) : Prop :=
  ∀ u v : F, point u = point v → normalizedValue frame shat u = normalizedValue frame shat v

/-- A spacetime scale expressed in ray-dependent local frames is weighted sky-basic. -/
theorem framed_pullback_is_weightedSkyBasic
    (point : F → M) (frame : F → K) (hframe : ∀ u, frame u ≠ 0)
    (sigma : M → K) :
    WeightedSkyBasic point frame (fun u => frame u * sigma (point u)) := by
  intro u v huv
  simp [WeightedSkyBasic, normalizedValue, hframe]
  rw [huv]

/-- Weighted descent: under surjectivity and nonvanishing frames, every weighted-sky-basic
field is a spacetime field written in the local ray-dependent frames. -/
theorem weightedSkyBasic_descends
    (point : F → M) (hpoint : Function.Surjective point)
    (frame shat : F → K) (hframe : ∀ u, frame u ≠ 0)
    (hbasic : WeightedSkyBasic point frame shat) :
    ∃ sigma : M → K, ∀ u : F, shat u = frame u * sigma (point u) := by
  have hnorm : GppSkyIncidenceDescent.SkyBasic point (normalizedValue frame shat) := hbasic
  obtain ⟨sigma,hsigma⟩ :=
    GppSkyIncidenceDescent.skyBasic_descends point hpoint (normalizedValue frame shat) hnorm
  refine ⟨sigma, ?_⟩
  intro u
  have hu := hsigma u
  unfold normalizedValue at hu
  have hf := hframe u
  field_simp [hf] at hu
  exact hu

/-- Exact iff form of weighted descent. -/
theorem weightedSkyBasic_iff_framed_factorization
    (point : F → M) (hpoint : Function.Surjective point)
    (frame shat : F → K) (hframe : ∀ u, frame u ≠ 0) :
    WeightedSkyBasic point frame shat ↔
      ∃ sigma : M → K, ∀ u : F, shat u = frame u * sigma (point u) := by
  constructor
  · exact weightedSkyBasic_descends point hpoint frame shat hframe
  · rintro ⟨sigma,hsigma⟩
    intro u v huv
    unfold normalizedValue
    rw [hsigma u, hsigma v]
    simp [hframe]
    rw [huv]

/-- Transition factor between two ray-dependent frames over the same spacetime point. -/
def transition (frame : F → K) (u v : F) : K := frame v / frame u

/-- The transition factors satisfy the multiplicative cocycle law. -/
theorem transition_cocycle
    (frame : F → K) (hframe : ∀ u, frame u ≠ 0)
    (u v w : F) :
    transition frame u v * transition frame v w = transition frame u w := by
  unfold transition
  field_simp [hframe u, hframe v, hframe w]
  ring

/-- The transition from a frame to itself is one. -/
theorem transition_refl
    (frame : F → K) (hframe : ∀ u, frame u ≠ 0) (u : F) :
    transition frame u u = 1 := by
  simp [transition, hframe]

/-- Reversing a transition gives its multiplicative inverse. -/
theorem transition_reverse
    (frame : F → K) (hframe : ∀ u, frame u ≠ 0) (u v : F) :
    transition frame u v * transition frame v u = 1 := by
  rw [transition_cocycle frame hframe u v u]
  exact transition_refl frame hframe u

/-- If `shat` is a framed pullback of a spacetime scale, values in two local ray frames are
related by the corresponding transition factor. -/
theorem framed_values_related_by_transition
    (point : F → M) (frame : F → K) (hframe : ∀ u, frame u ≠ 0)
    (sigma : M → K) (u v : F) (huv : point u = point v) :
    frame v * sigma (point v) =
      transition frame u v * (frame u * sigma (point u)) := by
  unfold transition
  rw [huv]
  field_simp [hframe u]
  ring

end GppSkyWeightedIncidenceDescent
