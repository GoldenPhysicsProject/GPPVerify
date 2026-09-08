import Mathlib.Tactic
import GppVerify.NumberTheory.GoldenRatioHyperbolicSector

/-!
# Why pure level-two monodromy cannot select the golden trace-three sector

The Legendre family over the *ordered* four-point cross-ratio base has pure monodromy
in the principal level-two subgroup `Gamma(2)`.  At the elementary matrix-congruence
level this means

    [[a,b],[c,d]] = [[1,0],[0,1]]  (mod 2).

Consequently its trace is even.  In particular no level-two matrix can have trace `+3`
or `-3`.  The golden hyperbolic element

    A = [[2,1],[1,1]],   tr A = 3,

therefore lies outside the pure level-two subgroup.  Its mod-two class is precisely the
nontrivial three-cycle recorded in `CelestialCrossingGoldenSector`.

This is an important falsifier for the physical program: identifying the ray/Sturm bundle
only with *pure* Legendre `Gamma(2)` monodromy is insufficient to select `phi`.  A physical
golden selection requires the full crossing/permutation extension (or some other
independently proved structure) that leaves the level-two subgroup.

Only the finite congruence obstruction is formalized here.  The external theorem that a
specific Gauss--Manin system has monodromy `Gamma(2)`, and the physical identification of
that system with celestial crossing, are not asserted by Lean.
-/

namespace GppLevelTwoGoldenObstruction

open GppGoldenHyperbolic

/-- Elementary coordinate definition of congruence to the identity modulo two. -/
def LevelTwoCongruence (a b c d : ℤ) : Prop :=
  a % 2 = 1 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 1

/-- Every level-two trace is even. -/
theorem levelTwo_trace_even_mod_two
    {a b c d : ℤ} (h : LevelTwoCongruence a b c d) :
    (a+d) % 2 = 0 := by
  rcases h with ⟨ha,hb,hc,hd⟩
  omega

/-- Therefore trace `+3` is impossible in the pure level-two subgroup. -/
theorem levelTwo_trace_ne_three
    {a b c d : ℤ} (h : LevelTwoCongruence a b c d) :
    a+d ≠ 3 := by
  intro htr
  have heven := levelTwo_trace_even_mod_two h
  omega

/-- Trace `-3` is equally impossible. -/
theorem levelTwo_trace_ne_neg_three
    {a b c d : ℤ} (h : LevelTwoCongruence a b c d) :
    a+d ≠ -3 := by
  intro htr
  have heven := levelTwo_trace_even_mod_two h
  omega

/-- The golden matrix is visibly not congruent to the identity modulo two. -/
theorem goldenA_not_levelTwo :
    ¬ LevelTwoCongruence
      (A (0 : Fin 2) (0 : Fin 2))
      (A (0 : Fin 2) (1 : Fin 2))
      (A (1 : Fin 2) (0 : Fin 2))
      (A (1 : Fin 2) (1 : Fin 2)) := by
  norm_num [LevelTwoCongruence, A]

/-- The obstruction can already be seen from the golden matrix's odd off-diagonal entry. -/
theorem goldenA_offdiag_mod_two :
    A (0 : Fin 2) (1 : Fin 2) % 2 = 1 := by
  norm_num [A]

end GppLevelTwoGoldenObstruction
