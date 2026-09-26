import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.NumberTheory.GoldenRatioHyperbolicSector
import GppVerify.CelestialHolography.LevelTwoGoldenObstruction

/-!
# The golden crossing lift returns to pure level-two monodromy after three cycles

The golden orientation-preserving matrix

    A = [[2,1],[1,1]]

has nontrivial mod-two class, so it is not itself in the pure level-two subgroup.
Its mod-two class is the three-cycle acting on the three cusps of the four-point
crossing quotient.  Consequently the third power should return to the identity
modulo two.

This file proves that statement directly over the integers:

    A^3 = [[13,8],[8,5]] ≡ I (mod 2).

Thus one application of the golden lift leaves the pure Legendre monodromy group,
while three applications return to it.  This is exactly the finite group pattern
expected from the quotient PSL(2,Z)/Gamma(2) ≅ S_3: the hyperbolic lift can carry a
three-cycle in the crossing quotient while its cube is pure monodromy.

Only the integer matrix/congruence statement is formalized.  The identification with
Gauss--Manin monodromy and celestial crossing is external geometry.
-/

namespace GppGoldenCrossingMonodromyCube

open GppGoldenHyperbolic
open GppLevelTwoGoldenObstruction

/-- Explicit third power of the golden matrix. -/
def A3 : Matrix (Fin 2) (Fin 2) ℤ := !![13,8;8,5]

/-- Exact integer identity `A^3=[[13,8],[8,5]]`. -/
theorem A_cube_eq_A3 : A * A * A = A3 := by
  unfold A A3
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

/-- The third power is congruent to the identity modulo two. -/
theorem A3_levelTwo :
    LevelTwoCongruence
      (A3 (0 : Fin 2) (0 : Fin 2))
      (A3 (0 : Fin 2) (1 : Fin 2))
      (A3 (1 : Fin 2) (0 : Fin 2))
      (A3 (1 : Fin 2) (1 : Fin 2)) := by
  norm_num [A3, LevelTwoCongruence]

/-- Therefore the explicit cube of the golden lift lies in the elementary level-two
congruence class even though `A` itself does not. -/
theorem golden_cube_returns_levelTwo :
    LevelTwoCongruence 13 8 8 5 := by
  norm_num [LevelTwoCongruence]

/-- The cube has trace eighteen; the return to pure monodromy is not a return to the
identity matrix, only to the identity *congruence class* modulo two. -/
theorem A3_trace :
    A3 (0 : Fin 2) (0 : Fin 2) + A3 (1 : Fin 2) (1 : Fin 2) = 18 := by
  norm_num [A3]

end GppGoldenCrossingMonodromyCube
