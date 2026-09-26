import Mathlib.Tactic
import GppVerify.CelestialHolography.CelestialLightWeylIntertwiners
import GppVerify.CelestialHolography.SplitFourierKernelFactorization

/-!
# Two half-Fourier/light diamonds compose to the full shadow diamond

Brown--Gowdy--Spence prove, analytically in split signature, two commuting diagrams:

  momentum --T--> twistor               momentum --Tbar--> dual twistor
     |              |                      |                  |
  chiral Mellin   chiral Mellin          chiral Mellin     chiral Mellin
     |              |                      |                  |
     v              v                      v                  v
  celestial --L--> light celestial      celestial --Lbar--> dual-light celestial.

They also describe the full Fourier transform as the composition of the two complementary
half-Fourier transforms.  `SplitFourierKernelFactorization` proves the underlying finite
algebra in the GPP twistor coordinates: the four-dimensional Fourier phase is the sum of
the two chiral rank-two phases, hence every exponential-type kernel factorizes into the
product of the two half kernels.  The analytic passage from kernel factorization to
iterated distributional integrals remains external.

Since the two normalized celestial light transforms commute and their product is full
shadow, the two commuting squares compose.

This file formalizes the categorical composition only.  It does not formalize any Fourier,
Mellin, or light integral; those enter as explicit commuting-square hypotheses.  The weight
identity `Lbar L = shadow` is already unconditional algebra in
`CelestialLightWeylIntertwiners`.
-/

namespace GppFourierLightShadowDiamond

open GppCelestialLightWeylIntertwiners

/-- Abstract two-step transform diagram with all analytic content isolated in the two
commuting-square fields. -/
structure TwoHalfTransformDiamond
    (Mom Tw Full Cel CelL CelS : Type*) where
  halfLeft : Mom → Tw
  halfRight : Tw → Full
  mellin0 : Mom → Cel
  mellin1 : Tw → CelL
  mellin2 : Full → CelS
  lightLeft : Cel → CelL
  lightRight : CelL → CelS
  left_commutes : ∀ m, mellin1 (halfLeft m) = lightLeft (mellin0 m)
  right_commutes : ∀ t, mellin2 (halfRight t) = lightRight (mellin1 t)

/-- The composed full transform automatically intertwines with the composed two light
transforms. -/
theorem full_transform_commutes_with_two_lights
    {Mom Tw Full Cel CelL CelS : Type*}
    (D : TwoHalfTransformDiamond Mom Tw Full Cel CelL CelS)
    (m : Mom) :
    D.mellin2 (D.halfRight (D.halfLeft m)) =
      D.lightRight (D.lightLeft (D.mellin0 m)) := by
  rw [D.right_commutes, D.left_commutes]

/-- At the split celestial weight level, the two chiral light reflections are exactly the
full shadow reflection. -/
theorem two_light_weight_reflections_are_shadow (w : WeightPair) :
    lightR (lightL w) = shadow w := by
  symm
  exact shadow_eq_lightR_lightL w

/-- The same statement with the two commuting chiral reflections in the opposite order. -/
theorem two_light_weight_reflections_are_shadow_opposite_order (w : WeightPair) :
    lightL (lightR w) = shadow w := by
  symm
  exact shadow_eq_lightL_lightR w

/-- Hence on `(Delta,J)` labels the two-step celestial operation is
`(Delta,J) -> (2-Delta,-J)`. -/
theorem two_light_deltaSpin_is_shadow (w : WeightPair) :
    deltaSpin (lightR (lightL w)) =
      (2 - (deltaSpin w).1, -(deltaSpin w).2) := by
  rw [two_light_weight_reflections_are_shadow]
  exact deltaSpin_shadow w

/-- On the unitary principal axes the same operation flips both spectral parameters. -/
theorem two_light_principal_parameters (a b : ℝ) :
    lightR (lightL (principalWeights a b)) = principalWeights (-a) (-b) := by
  rw [two_light_weight_reflections_are_shadow]
  exact shadow_principal a b

end GppFourierLightShadowDiamond
