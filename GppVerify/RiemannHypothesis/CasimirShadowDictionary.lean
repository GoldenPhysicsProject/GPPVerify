import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Shadow / principal-series Casimir dictionary

This file records the elementary algebraic core of the celestial/arithmetic
dictionary used in the RH boundary program.

Set

  h = s,
  Delta = 2 s,
  nu = h - 1 = s - 1.

Then the celestial shadow involution Delta -> 2 - Delta is the same affine
reflection as s -> 1 - s, the Legendre degree transforms by
nu -> -nu - 1, and the quadratic Casimir agrees exactly:

  -nu (nu + 1) = s (1 - s).

Writing s = 1/2 + u gives the centered form

  s (1 - s) = 1/4 - u^2.

On the unitary line u = i t this becomes 1/4 + t^2.  The latter specialization
is mathematically immediate once i^2 = -1 is inserted; the ring identities
below isolate the convention-independent part.

These identities do not prove RH.  They verify that the arithmetic
half-density Casimir and the celestial Legendre/conical Casimir are literally
the same polynomial invariant under the proposed dictionary.
-/

namespace GppCasimirShadowDictionary

noncomputable section

/-- If nu = s - 1, celestial degree reflection is exactly s -> 1 - s. -/
theorem shadow_degree_map (s : ℂ) :
    ((1 - s) - 1) = - (s - 1) - 1 := by
  ring

/-- The Legendre/conical Casimir equals the arithmetic shadow Casimir. -/
theorem shadow_casimir_identity (s : ℂ) :
    -((s - 1) * ((s - 1) + 1)) = s * (1 - s) := by
  ring

/-- Centering at the half-density line isolates the universal 1/4 shift. -/
theorem centered_casimir_identity (u : ℂ) :
    ((1 / 2 : ℂ) + u) * (1 - ((1 / 2 : ℂ) + u))
      = (1 / 4 : ℂ) - u ^ 2 := by
  ring

/--
Abstract unitary-line specialization: whenever u^2 = -t^2 (in particular
u = i t), the Casimir is 1/4 + t^2.
-/
theorem unitary_line_casimir
    (u t : ℂ) (h : u ^ 2 = -(t ^ 2)) :
    ((1 / 2 : ℂ) + u) * (1 - ((1 / 2 : ℂ) + u))
      = (1 / 4 : ℂ) + t ^ 2 := by
  rw [centered_casimir_identity, h]
  ring

/-- Doubling the arithmetic weight turns s-reflection into celestial shadow. -/
theorem doubled_shadow_identity (s : ℂ) :
    2 * (1 - s) = 2 - 2 * s := by
  ring

end

end GppCasimirShadowDictionary
