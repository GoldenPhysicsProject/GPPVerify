import Mathlib.Tactic
import GppVerify.NumberTheory.GoldenRatioHyperbolicSector

/-!
# The golden hyperbolic element and the three celestial crossing cusps

Four ordered points on a projective line are parametrized by a cross-ratio `z`; after
fixing three points to `0,1,infinity`, permutations of the four marked points act through
the familiar six cross-ratio transforms.  The three degeneration channels are represented
by the cusps `infinity`, `0`, and `1`.

The level-two quotient of the modular group acts on these three cusps as

    PSL(2,F_2) = S_3.

The golden hyperbolic matrix already formalized in
`GoldenRatioHyperbolicSector`,

    A = [[2,1],[1,1]],

reduces modulo two to

    A_2 = [[0,1],[1,1]].

Its projective action on `P^1(F_2)={infinity,0,1}` is the three-cycle

    infinity -> 0 -> 1 -> infinity.

Thus the previously discovered minimal-trace hyperbolic element is not in the pure
level-two subgroup: it is a hyperbolic lift of a nontrivial three-cycle of the three
crossing cusps.  Since `A` has determinant one and minimal hyperbolic trace three, its
quadratic discriminant is five and its expanding/contracting roots are `phi^(+2)` and
`phi^(-2)`, already proved in the imported module.

This file formalizes the finite quotient/cycle algebra only.  It does NOT prove that the
physical neutral Sturm bundle has the Legendre/Gauss--Manin integral lattice, nor that
celestial crossing promotes its pure `Gamma(2)` monodromy to the full modular action.
Those are the global bridge theorems required before this three-cycle can select a
physical holonomy.
-/

namespace GppCelestialCrossingGoldenSector

open GppGoldenHyperbolic

/-- Three degeneration cusps of four-point cross-ratio moduli. -/
inductive CrossingCusp where
  | infinity
  | zero
  | one
  deriving DecidableEq, Repr

/-- Projective action of `A mod 2 = [[0,1],[1,1]]` on `P^1(F_2)`. -/
def goldenCuspAction : CrossingCusp → CrossingCusp
  | .infinity => .zero
  | .zero => .one
  | .one => .infinity

/-- The action is literally a three-cycle. -/
theorem goldenCuspAction_cycle :
    goldenCuspAction .infinity = .zero ∧
    goldenCuspAction .zero = .one ∧
    goldenCuspAction .one = .infinity := by
  decide

/-- Three applications restore every cusp. -/
theorem goldenCuspAction_order_three (c : CrossingCusp) :
    goldenCuspAction (goldenCuspAction (goldenCuspAction c)) = c := by
  cases c <;> rfl

/-- No cusp is fixed by this action. -/
theorem goldenCuspAction_no_fixed_point (c : CrossingCusp) :
    goldenCuspAction c ≠ c := by
  cases c <;> decide

/-- The old golden matrix really has the integer entries displayed in the source theorem;
this is the matrix whose mod-two reduction produces the above cycle. -/
theorem goldenA_entries :
    A (0 : Fin 2) (0 : Fin 2) = 2 ∧
    A (0 : Fin 2) (1 : Fin 2) = 1 ∧
    A (1 : Fin 2) (0 : Fin 2) = 1 ∧
    A (1 : Fin 2) (1 : Fin 2) = 1 := by
  norm_num [A]

/-- Entrywise modulo-two reduction of `A` is `[[0,1],[1,1]]`. -/
theorem goldenA_mod_two_entries :
    A (0 : Fin 2) (0 : Fin 2) % 2 = 0 ∧
    A (0 : Fin 2) (1 : Fin 2) % 2 = 1 ∧
    A (1 : Fin 2) (0 : Fin 2) % 2 = 1 ∧
    A (1 : Fin 2) (1 : Fin 2) % 2 = 1 := by
  norm_num [A]

/-- The orientation-preserving golden lift sits at the smallest possible positive
hyperbolic trace: the imported arithmetic bound says every integral hyperbolic trace has
absolute value at least three, and `A` attains it. -/
theorem golden_crossing_lift_is_minimal_trace :
    |A.trace| = 3 :=
  A_trace_attains_min

/-- Its discriminant is exactly five. -/
theorem golden_crossing_discriminant_five : discrA = 5 :=
  discrA_eq_five

/-- The expanding root of the trace-three characteristic polynomial is `phi^2`. -/
theorem golden_crossing_expanding_root :
    ((Real.goldenRatio : ℝ) ^ 2) ^ 2
      - (A.trace : ℝ) * (Real.goldenRatio : ℝ) ^ 2
      + (A.det : ℝ) = 0 :=
  A_charpoly_root_goldSq

/-- The contracting reciprocal root is `phi^(-2)`. -/
theorem golden_crossing_contracting_root :
    ((Real.goldenRatio : ℝ)⁻¹ ^ 2) ^ 2
      - (A.trace : ℝ) * (Real.goldenRatio : ℝ)⁻¹ ^ 2
      + (A.det : ℝ) = 0 :=
  A_charpoly_root_goldInvSq

/-- The independent finite-place shadow-kernel route still lands on the same number at
the discriminant selected by this matrix. -/
theorem crossing_golden_kernel_convergence :
    (Real.goldenRatio : ℝ) ^ 2 = finitePlaceKernel (discrA : ℝ) (1 / 2) :=
  golden_convergence

end GppCelestialCrossingGoldenSector
