import GppVerify.CelestialHolography.PositiveRealPrincipalSeries
import Mathlib.Tactic

/-!
# Celestial shadow as an exact helicity reversal

The two-dimensional shadow transform acts on conformal weights by

  (h, hbar) ↦ (1-h, 1-hbar).

Consequently it sends the conformal dimension `Delta = h+hbar` to `2-Delta`
and the celestial spin `J = h-hbar` to `-J`.  This is the precise algebraic
bridge needed for the twistor googly discussion: opposite helicity sectors are
exchanged by shadow at the level of celestial representation labels.

This file deliberately does *not* assert the Penrose--Ward/sheaf-cohomology
identification between those labels and nonlinear SD/ASD twistor bundles; that
geometric bridge is a separate theorem still to be constructed.
-/

namespace GppCelestialShadowHelicity

structure Weights where
  h : ℂ
  hbar : ℂ

namespace Weights

/-- Celestial conformal dimension. -/
def delta (w : Weights) : ℂ := w.h + w.hbar

/-- Celestial spin/helicity label. -/
def spin (w : Weights) : ℂ := w.h - w.hbar

/-- Two-dimensional shadow transform on conformal weights. -/
def shadow (w : Weights) : Weights :=
  ⟨1 - w.h, 1 - w.hbar⟩

/-- Shadow is an involution on the full pair of conformal weights. -/
theorem shadow_involutive (w : Weights) : shadow (shadow w) = w := by
  cases w
  simp [shadow]

/-- Shadow reflects conformal dimension about one: `Delta ↦ 2-Delta`. -/
theorem delta_shadow (w : Weights) :
    delta (shadow w) = 2 - delta w := by
  unfold delta shadow
  ring

/-- Shadow reverses celestial spin exactly: `J ↦ -J`. -/
theorem spin_shadow (w : Weights) :
    spin (shadow w) = -spin w := by
  unfold spin shadow
  ring

/-- A weight pair reconstructed from dimension and spin. -/
noncomputable def ofDeltaSpin (Delta J : ℂ) : Weights :=
  ⟨(Delta + J) / 2, (Delta - J) / 2⟩

@[simp] theorem delta_ofDeltaSpin (Delta J : ℂ) :
    delta (ofDeltaSpin Delta J) = Delta := by
  unfold delta ofDeltaSpin
  dsimp
  ring

@[simp] theorem spin_ofDeltaSpin (Delta J : ℂ) :
    spin (ofDeltaSpin Delta J) = J := by
  unfold spin ofDeltaSpin
  dsimp
  ring

/-- In `(Delta,J)` variables the shadow transform is exactly
`(Delta,J) ↦ (2-Delta,-J)`. -/
theorem shadow_ofDeltaSpin (Delta J : ℂ) :
    shadow (ofDeltaSpin Delta J) = ofDeltaSpin (2 - Delta) (-J) := by
  change Weights.mk (1 - (Delta + J) / 2) (1 - (Delta - J) / 2) =
    Weights.mk (((2 - Delta) + (-J)) / 2) (((2 - Delta) - (-J)) / 2)
  congr 1 <;> ring

/-- On the principal series `Delta = 1+i nu`, the dimension part of shadow is
ordinary complex conjugation. -/
theorem principal_series_shadow_delta (nu : ℝ) :
    let Delta : ℂ := 1 + Complex.I * nu
    delta (shadow (ofDeltaSpin Delta 0)) = starRingEnd ℂ Delta := by
  dsimp
  rw [delta_shadow, delta_ofDeltaSpin]
  apply Complex.ext <;>
    simp [RCLike.star_def, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Spin-two googly exchange: shadow sends a `+2` celestial helicity label to
`-2`, independently of the conformal dimension. -/
theorem graviton_plus_to_minus (Delta : ℂ) :
    spin (shadow (ofDeltaSpin Delta 2)) = -2 := by
  rw [spin_shadow, spin_ofDeltaSpin]

/-- Conversely shadow sends a `-2` celestial helicity label to `+2`. -/
theorem graviton_minus_to_plus (Delta : ℂ) :
    spin (shadow (ofDeltaSpin Delta (-2))) = 2 := by
  rw [spin_shadow, spin_ofDeltaSpin]
  ring

/-- Spin-one exchange for gauge bosons. -/
theorem gauge_plus_to_minus (Delta : ℂ) :
    spin (shadow (ofDeltaSpin Delta 1)) = -1 := by
  rw [spin_shadow, spin_ofDeltaSpin]

end Weights

end GppCelestialShadowHelicity

#print axioms GppCelestialShadowHelicity.Weights.shadow_involutive
#print axioms GppCelestialShadowHelicity.Weights.delta_shadow
#print axioms GppCelestialShadowHelicity.Weights.spin_shadow
#print axioms GppCelestialShadowHelicity.Weights.shadow_ofDeltaSpin
#print axioms GppCelestialShadowHelicity.Weights.graviton_plus_to_minus
