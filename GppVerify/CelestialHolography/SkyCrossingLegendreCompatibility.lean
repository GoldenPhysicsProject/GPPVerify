import Mathlib.Tactic
import GppVerify.CelestialHolography.SkyFourSectionCrossRatio
import GppVerify.CelestialHolography.LegendreCrossingSturmConnection

/-!
# Four-section sky crossing is compatible with the Legendre projective connection

`SkyFourSectionCrossRatio` shows that four distinguished projective sections of a rank-two
sky/Sturm bundle produce a basis-independent cross ratio `z`, and that simple section
permutations realize the crossing generators

    z -> 1/z,
    z -> 1-z.

`LegendreCrossingSturmConnection` independently proves that the Legendre/Picard--Fuchs
projective potential

    U(z) = (z^2-z+1)/(4 z^2 (1-z)^2)

is covariant under exactly those transformations.

This module composes the two facts.  Therefore if the missing global sky/ambitwistor
geometry supplies four canonical projective sections, no further arbitrary choice is needed
to obtain the standard crossing action on the Legendre Sturm connection: it is induced by
permutation of those sections and is independent of the chosen solution basis.

The existence of four canonical sections is still the hard geometric input.
-/

namespace GppSkyCrossingLegendreCompatibility

open GppSkyFourSectionCrossRatio
open GppLegendreCrossingSturmConnection

/-- A simultaneous Mobius change of projective solution basis leaves not only the four-point
coordinate but also the Legendre potential evaluated at that coordinate unchanged. -/
theorem legendrePotential_fourSection_basisInvariant
    (A B C D a b c d : ℝ)
    (hdet : A*D-B*C ≠ 0)
    (ha : C*a + D ≠ 0) (hb : C*b + D ≠ 0)
    (hc : C*c + D ≠ 0) (hd : C*d + D ≠ 0)
    (had : a-d ≠ 0) (hbc : b-c ≠ 0) :
    legendrePotential
      (crossRatio (mobius A B C D a) (mobius A B C D b)
        (mobius A B C D c) (mobius A B C D d))
      = legendrePotential (crossRatio a b c d) := by
  rw [crossRatio_mobius_invariant A B C D a b c d hdet ha hb hc hd had hbc]

/-- Swapping the middle two sections induces `z -> 1-z`, under which the Legendre
projective potential is exactly invariant. -/
theorem middle_section_swap_preserves_legendrePotential
    (a b c d : ℝ)
    (had : a-d ≠ 0) (hbc : b-c ≠ 0) :
    legendrePotential (crossRatio a c b d) =
      legendrePotential (crossRatio a b c d) := by
  rw [crossRatio_swap_middle a b c d had hbc]
  exact legendrePotential_one_sub (crossRatio a b c d)

/-- Swapping the first two sections induces inversion.  The Legendre projective connection
then transforms with its correct weight-two factor. -/
theorem first_section_swap_legendre_covariant
    (a b c d : ℝ)
    (hac : a-c ≠ 0) (hbd : b-d ≠ 0)
    (had : a-d ≠ 0) (hbc : b-c ≠ 0)
    (hz : crossRatio a b c d ≠ 0)
    (hz1 : crossRatio a b c d ≠ 1) :
    (1 / (crossRatio a b c d)^4) *
        legendrePotential (crossRatio b a c d)
      = legendrePotential (crossRatio a b c d) := by
  rw [crossRatio_swap_first_two a b c d hac hbd had hbc]
  exact legendrePotential_inv_covariant (crossRatio a b c d) hz hz1

/-- Hence the projective target attached to four sections is simultaneously independent of
solution basis and equivariant under marked-point crossing permutations. -/
theorem fourSection_projective_target_wellDefined
    (A B C D a b c d : ℝ)
    (hdet : A*D-B*C ≠ 0)
    (ha : C*a + D ≠ 0) (hb : C*b + D ≠ 0)
    (hc : C*c + D ≠ 0) (hd : C*d + D ≠ 0)
    (had : a-d ≠ 0) (hbc : b-c ≠ 0) :
    legendrePotential
      (crossRatio (mobius A B C D a) (mobius A B C D b)
        (mobius A B C D c) (mobius A B C D d))
      = legendrePotential (crossRatio a b c d) ∧
    legendrePotential (crossRatio a c b d) =
      legendrePotential (crossRatio a b c d) := by
  exact ⟨legendrePotential_fourSection_basisInvariant
      A B C D a b c d hdet ha hb hc hd had hbc,
    middle_section_swap_preserves_legendrePotential a b c d had hbc⟩

end GppSkyCrossingLegendreCompatibility
