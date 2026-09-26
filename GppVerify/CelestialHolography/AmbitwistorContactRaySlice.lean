import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbitwistorContactNeutralCone
import GppVerify.CelestialHolography.AmbitwistorGoldenPGL2Bridge

/-!
# A polarized contact-screen slice is exactly the rank-two ray symplectic carrier

The flat Lagrangian-contact screen is the rank-four real vector space

    H = L_- + L_+,

with `L_- = R^2`, `L_+ = R^2` and Levi form

    L((X,Y),(X',Y')) = X.Y' - X'.Y.

Fix any nonzero transverse screen direction `e in R^2` and restrict to the polarized
rank-two slice

    (x,p) |-> (x e, p e).

On this slice the contact Levi form is

    L = |e|^2 (x q - p y),

so after unit normalization of `e` it is exactly the Wronskian `omega` of the null-ray
Einstein/Sturm carrier.  More importantly, the canonical contact-half exchange

    (X,Y) |-> (Y,X)

restricts *exactly* to

    (x,p) |-> (p,x),

which is the reciprocal anti-symplectic reflection used in
`AmbitwistorGoldenPGL2Bridge`.

This is a genuine finite-dimensional descent theorem, valid for every chosen polarized
screen line.  It does not yet prove that a general curved/projective ambitwistor contact
screen canonically selects a global polarization line, nor that the Penrose/sky/NSF
rank-two bundle is globally this slice.  Those are the remaining bundle/gluing steps.
-/

namespace GppAmbitwistorContactRaySlice

open GppFlatInfinityCelestialFactorization
open GppAmbitwistorContactNeutralCone
open GppEinsteinNullRaySL2Geometry
open GppAmbitwistorGoldenPGL2Bridge

/-- Euclidean squared norm of a transverse screen direction. -/
def screenNormSq (e : ContactHalf) : ℝ := halfPair e e

/-- Scalar multiplication of a screen direction. -/
def screenScale (a : ℝ) (e : ContactHalf) : ContactHalf :=
  (a*e.1,a*e.2)

/-- Polarized rank-two slice of the rank-four contact screen. -/
def polarizedRaySlice (e : ContactHalf) (u : RayState) : ContactVector :=
  (screenScale u.1 e, screenScale u.2 e)

/-- The cross-half pairing on a polarized slice factorizes into scalar amplitudes times
`|e|^2`. -/
theorem halfPair_screenScale
    (a b : ℝ) (e : ContactHalf) :
    halfPair (screenScale a e) (screenScale b e) = a*b*screenNormSq e := by
  rcases e with ⟨e0,e1⟩
  simp [halfPair, screenScale, screenNormSq]
  ring

/-- Main symplectic restriction formula: the contact Levi form is `|e|^2` times the
null-ray Wronskian. -/
theorem levi_on_polarized_slice
    (e : ContactHalf) (u v : RayState) :
    leviForm (polarizedRaySlice e u) (polarizedRaySlice e v) =
      screenNormSq e * omega u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  rcases e with ⟨e0,e1⟩
  simp [leviForm, polarizedRaySlice, screenScale, halfPair, screenNormSq, omega]
  ring

/-- For a unit screen direction the two alternating forms agree exactly. -/
theorem unit_polarization_levi_eq_omega
    (e : ContactHalf) (he : screenNormSq e = 1) (u v : RayState) :
    leviForm (polarizedRaySlice e u) (polarizedRaySlice e v) = omega u v := by
  rw [levi_on_polarized_slice, he, one_mul]

/-- The neutral contact quadratic form restricts to `2*x*p*|e|^2`. -/
theorem neutralQ_on_polarized_slice
    (e : ContactHalf) (u : RayState) :
    neutralQ (polarizedRaySlice e u) =
      2 * u.1 * u.2 * screenNormSq e := by
  rw [neutralQ_eq_twice_halfPair]
  rcases u with ⟨x,p⟩
  rw [halfPair_screenScale]
  ring

/-- **Exact exchange descent on every polarized slice.**  Swapping the two contact halves
is precisely the ray reciprocal reflection `(x,p)->(p,x)`. -/
theorem exchangeHalves_polarized_slice
    (e : ContactHalf) (u : RayState) :
    exchangeHalves (polarizedRaySlice e u) =
      polarizedRaySlice e (act2 rayReciprocal u) := by
  rcases u with ⟨x,p⟩
  rcases e with ⟨e0,e1⟩
  simp [exchangeHalves, polarizedRaySlice, screenScale,
    rayReciprocal, act2]

/-- Consequently contact-half exchange reverses the restricted Levi/Wronskian form. -/
theorem exchangeHalves_reverses_levi_on_slice
    (e : ContactHalf) (u v : RayState) :
    leviForm
        (exchangeHalves (polarizedRaySlice e u))
        (exchangeHalves (polarizedRaySlice e v)) =
      -(screenNormSq e * omega u v) := by
  rw [exchangeHalves_polarized_slice, exchangeHalves_polarized_slice,
      levi_on_polarized_slice, rayReciprocal_reverses_omega]
  ring

/-- At unit polarization this is exactly the anti-symplectic ray reflection theorem. -/
theorem unit_exchange_is_ray_antisymplectic
    (e : ContactHalf) (he : screenNormSq e = 1) (u v : RayState) :
    leviForm
        (exchangeHalves (polarizedRaySlice e u))
        (exchangeHalves (polarizedRaySlice e v)) = -omega u v := by
  rw [exchangeHalves_reverses_levi_on_slice, he, one_mul]

end GppAmbitwistorContactRaySlice
