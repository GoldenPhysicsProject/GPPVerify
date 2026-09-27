import Mathlib.Tactic
import GppVerify.CelestialHolography.CelestialCrossingGoldenSector
import GppVerify.CelestialHolography.LegendreCrossingSturmConnection

/-!
# Golden trace-three lift versus the order-three four-point crossing action

There are two distinct projective coordinates in the modular/Legendre picture and they
must not be conflated:

* `tau` is a projective period ratio.  The integral matrix

      A = [[2,1],[1,1]]

  acts hyperbolically on `tau` by `(2 tau+1)/(tau+1)` and has real fixed points
  `phi` and `-phi^{-1}`; its eigenvalues are `phi^{+2}` and `phi^{-2}`.

* `z` is the four-point cross-ratio / Legendre modular-lambda coordinate.  Modulo the
  pure level-two subgroup, the same matrix class acts as an order-three permutation of
  the three degeneration channels.  A standard representative of that anharmonic action is

      C(z) = 1/(1-z),

  which cycles `infinity -> 0 -> 1 -> infinity` and satisfies `C^3=id`.

The imported files separately proved that `A mod 2` is exactly that three-cycle on the
three cusps, and that the Legendre normal-form Sturm potential is covariant under
`z -> 1/(1-z)`.  This module packages the rational part of the same picture.

The identification of the matrix's mod-two cusp action with the analytic modular-lambda
transformation is a standard external modular-function theorem, not reproved in Lean.
Likewise no physical identification of the Legendre period local system with the curved
Penrose/sky/NSF bundle is assumed.
-/

namespace GppGoldenCrossingLegendreCapstone

open GppGoldenHyperbolic
open GppCelestialCrossingGoldenSector
open GppLegendreCrossingSturmConnection

/-- Order-three anharmonic transformation representing the golden matrix's crossing class. -/
noncomputable def crossingThreeCycle (z : ℝ) : ℝ := 1/(1-z)

/-- Its square is the second nontrivial element of the three-cycle. -/
theorem crossingThreeCycle_sq
    (z : ℝ) (hz : z ≠ 0) (hz1 : z ≠ 1) :
    crossingThreeCycle (crossingThreeCycle z) = (z-1)/z := by
  unfold crossingThreeCycle
  field_simp [hz, hz1]
  ring

/-- Three applications return the cross-ratio exactly away from the degeneration cusps. -/
theorem crossingThreeCycle_order_three
    (z : ℝ) (hz : z ≠ 0) (hz1 : z ≠ 1) :
    crossingThreeCycle
      (crossingThreeCycle (crossingThreeCycle z)) = z := by
  unfold crossingThreeCycle
  field_simp [hz, hz1]
  ring

/-- The Legendre Sturm/projective connection is covariant under this exact three-cycle.
The prefactor is the square of `C'(z)=1/(1-z)^2`. -/
theorem legendrePotential_golden_crossing_covariant
    (z : ℝ) (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (1/(1-z)^4) * legendrePotential (crossingThreeCycle z) = legendrePotential z := by
  simpa [crossingThreeCycle] using
    legendrePotential_one_over_one_sub_covariant z hz1 hz

/-- The finite cusp permutation attached to the golden matrix has the same abstract order
three already proved from its mod-two reduction. -/
theorem golden_mod_two_crossing_class_order_three (c : CrossingCusp) :
    goldenCuspAction (goldenCuspAction (goldenCuspAction c)) = c :=
  goldenCuspAction_order_three c

/-- Meanwhile the lift itself remains genuinely hyperbolic: its trace is three. -/
theorem golden_lift_trace_three : A.trace = 3 :=
  trace_A

/-- The lift therefore retains the independently proved discriminant five. -/
theorem golden_lift_discriminant_five : discrA = 5 :=
  discrA_eq_five

/-- And its expanding characteristic root is the golden square. -/
theorem golden_lift_phi_sq_root :
    ((Real.goldenRatio : ℝ)^2)^2
      - (A.trace : ℝ)*(Real.goldenRatio : ℝ)^2
      + (A.det : ℝ) = 0 :=
  A_charpoly_root_goldSq

end GppGoldenCrossingLegendreCapstone
