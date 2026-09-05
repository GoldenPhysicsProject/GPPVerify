import Mathlib.Tactic

/-!
# Split celestial light-transform Weyl algebra

For split signature the celestial cut factorizes into two real projective spinor factors.
At the level of conformal weights the two normalized light intertwiners act separately:

  L    : (h,hbar) |-> (1-h,hbar),
  Lbar : (h,hbar) |-> (h,1-hbar).

Their product is the ordinary two-dimensional shadow reflection

  S : (h,hbar) |-> (1-h,1-hbar).

A separate factor-exchange involution

  P : (h,hbar) |-> (hbar,h)

models the representation-theoretic parity/orientation exchange between the two chiral
factors.  It conjugates L into Lbar but is not itself the shadow transform.

Brown--Gowdy--Spence identify the corresponding half-Fourier twistor transforms with L
and Lbar after the appropriate half-Mellin transform.  This module formalizes only the
exact weight/Weyl algebra; it does not formalize the analytic integral intertwiners.
-/

namespace GppCelestialLightWeylIntertwiners

/-- Pair of chiral celestial weights `(h,hbar)`. -/
abbrev WeightPair := ℂ × ℂ

/-- Left light reflection. -/
def lightL (w : WeightPair) : WeightPair := (1 - w.1, w.2)

/-- Right light reflection. -/
def lightR (w : WeightPair) : WeightPair := (w.1, 1 - w.2)

/-- Full celestial shadow. -/
def shadow (w : WeightPair) : WeightPair := (1 - w.1, 1 - w.2)

/-- Chiral factor exchange (parity/orientation label exchange). -/
def parity (w : WeightPair) : WeightPair := (w.2, w.1)

/-- Dimension and spin coordinates: Delta=h+hbar and J=h-hbar. -/
def deltaSpin (w : WeightPair) : WeightPair := (w.1 + w.2, w.1 - w.2)

/-- Each chiral light reflection is involutive. -/
theorem lightL_sq (w : WeightPair) : lightL (lightL w) = w := by
  rcases w with ⟨h,hb⟩
  simp [lightL]

/-- Each chiral light reflection is involutive. -/
theorem lightR_sq (w : WeightPair) : lightR (lightR w) = w := by
  rcases w with ⟨h,hb⟩
  simp [lightR]

/-- The two chiral light reflections commute. -/
theorem light_commute (w : WeightPair) :
    lightL (lightR w) = lightR (lightL w) := by
  rcases w with ⟨h,hb⟩
  rfl

/-- Full shadow is the product of the two half-shadow/light reflections. -/
theorem shadow_eq_lightL_lightR (w : WeightPair) :
    shadow w = lightL (lightR w) := by
  rcases w with ⟨h,hb⟩
  rfl

/-- And equivalently in the opposite order. -/
theorem shadow_eq_lightR_lightL (w : WeightPair) :
    shadow w = lightR (lightL w) := by
  rcases w with ⟨h,hb⟩
  rfl

/-- Full shadow is involutive. -/
theorem shadow_sq (w : WeightPair) : shadow (shadow w) = w := by
  rcases w with ⟨h,hb⟩
  simp [shadow]

/-- Chiral factor exchange is involutive. -/
theorem parity_sq (w : WeightPair) : parity (parity w) = w := by
  rcases w with ⟨h,hb⟩
  rfl

/-- Parity conjugates the left light reflection into the right one. -/
theorem parity_lightL_parity (w : WeightPair) :
    parity (lightL (parity w)) = lightR w := by
  rcases w with ⟨h,hb⟩
  rfl

/-- Parity conjugates the right light reflection into the left one. -/
theorem parity_lightR_parity (w : WeightPair) :
    parity (lightR (parity w)) = lightL w := by
  rcases w with ⟨h,hb⟩
  rfl

/-- Parity commutes with full shadow. -/
theorem parity_shadow_commute (w : WeightPair) :
    parity (shadow w) = shadow (parity w) := by
  rcases w with ⟨h,hb⟩
  rfl

/-- In `(Delta,J)` coordinates, the left light transform sends
`(Delta,J)` to `(1-J,1-Delta)`. -/
theorem deltaSpin_lightL (w : WeightPair) :
    deltaSpin (lightL w) = (1 - (deltaSpin w).2, 1 - (deltaSpin w).1) := by
  rcases w with ⟨h,hb⟩
  apply Prod.ext <;> simp [deltaSpin, lightL] <;> ring

/-- In `(Delta,J)` coordinates, the right light transform sends
`(Delta,J)` to `(1+J,Delta-1)`. -/
theorem deltaSpin_lightR (w : WeightPair) :
    deltaSpin (lightR w) = (1 + (deltaSpin w).2, (deltaSpin w).1 - 1) := by
  rcases w with ⟨h,hb⟩
  apply Prod.ext <;> simp [deltaSpin, lightR] <;> ring

/-- Full shadow sends `(Delta,J)` to `(2-Delta,-J)`. -/
theorem deltaSpin_shadow (w : WeightPair) :
    deltaSpin (shadow w) = (2 - (deltaSpin w).1, -(deltaSpin w).2) := by
  rcases w with ⟨h,hb⟩
  apply Prod.ext <;> simp [deltaSpin, shadow] <;> ring

/-- Parity preserves Delta and reverses J. -/
theorem deltaSpin_parity (w : WeightPair) :
    deltaSpin (parity w) = ((deltaSpin w).1, -(deltaSpin w).2) := by
  rcases w with ⟨h,hb⟩
  apply Prod.ext <;> simp [deltaSpin, parity] <;> ring

/-- Principal-series parametrization around the two chiral unitary axes. -/
def principalWeights (a b : ℝ) : WeightPair :=
  ((1 / 2 : ℂ) + Complex.I * a, (1 / 2 : ℂ) + Complex.I * b)

/-- The left light reflection flips only the left principal-series spectral parameter. -/
theorem lightL_principal (a b : ℝ) :
    lightL (principalWeights a b) = principalWeights (-a) b := by
  apply Prod.ext <;> simp [lightL, principalWeights] <;> ring

/-- The right light reflection flips only the right principal-series spectral parameter. -/
theorem lightR_principal (a b : ℝ) :
    lightR (principalWeights a b) = principalWeights a (-b) := by
  apply Prod.ext <;> simp [lightR, principalWeights] <;> ring

/-- Full shadow flips both principal-series spectral parameters. -/
theorem shadow_principal (a b : ℝ) :
    shadow (principalWeights a b) = principalWeights (-a) (-b) := by
  apply Prod.ext <;> simp [shadow, principalWeights] <;> ring

/-- Parity swaps the two chiral spectral parameters. -/
theorem parity_principal (a b : ℝ) :
    parity (principalWeights a b) = principalWeights b a := by
  rfl

/-- The four transformations generated by the commuting light involutions form the
expected Klein-four orbit at the level of weights. -/
theorem light_klein_four_orbit (w : WeightPair) :
    lightL (lightR (lightL (lightR w))) = w := by
  rcases w with ⟨h,hb⟩
  simp [lightL, lightR]

end GppCelestialLightWeylIntertwiners
