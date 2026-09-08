import Mathlib.Tactic

/-!
# Four projective sky sections give a canonical crossing coordinate

A rank-two Sturm/sky bundle has a projective fibre `P^1`.  A change of solution basis acts
on an affine projective coordinate by a Mobius transformation.  Therefore any proposed map
from the NSF/sky bundle to the four-point moduli space `M_{0,4}` must be independent of that
basis choice.

The cross ratio of four distinguished projective sections is exactly such an invariant.
For affine representatives `a,b,c,d`, define

    cr(a,b;c,d) = ((a-c)(b-d))/((a-d)(b-c)).

This module proves directly that `cr` is invariant under every nondegenerate real Mobius
transformation on the chosen affine chart.  It also proves two elementary permutation laws
which generate the usual six anharmonic/crossing transforms:

    swap(a,b): z -> 1/z,
    swap(b,c): z -> 1-z.

Thus, IF the global sky/NSF geometry canonically supplies four projective sections, their
cross ratio gives a basis-independent local coordinate `z` on four-point moduli, and
permuting the sections produces the standard crossing action.  The existence/canonicity of
those four sections is not assumed or proved here; this file isolates exactly what would be
obtained from them.
-/

namespace GppSkyFourSectionCrossRatio

/-- Affine cross ratio of four real projective coordinates. -/
def crossRatio (a b c d : ℝ) : ℝ :=
  ((a-c) * (b-d)) / ((a-d) * (b-c))

/-- Real Mobius transformation with matrix entries `(A,B;C,D)`. -/
def mobius (A B C D x : ℝ) : ℝ :=
  (A*x+B) / (C*x+D)

/-- Difference of two Mobius images.  This is the cancellation identity behind cross-ratio
invariance. -/
theorem mobius_sub
    (A B C D x y : ℝ)
    (hx : C*x + D ≠ 0) (hy : C*y + D ≠ 0) :
    mobius A B C D x - mobius A B C D y =
      (A*D-B*C) * (x-y) / ((C*x+D)*(C*y+D)) := by
  unfold mobius
  field_simp [hx, hy]
  ring

/-- The cross ratio is invariant under any nondegenerate Mobius basis change, on an affine
chart where all four transformed representatives are finite and the defining denominator
of the source cross ratio is nonzero. -/
theorem crossRatio_mobius_invariant
    (A B C D a b c d : ℝ)
    (hdet : A*D-B*C ≠ 0)
    (ha : C*a + D ≠ 0) (hb : C*b + D ≠ 0)
    (hc : C*c + D ≠ 0) (hd : C*d + D ≠ 0)
    (had : a-d ≠ 0) (hbc : b-c ≠ 0) :
    crossRatio (mobius A B C D a) (mobius A B C D b)
      (mobius A B C D c) (mobius A B C D d)
      = crossRatio a b c d := by
  unfold crossRatio
  rw [mobius_sub A B C D a c ha hc]
  rw [mobius_sub A B C D b d hb hd]
  rw [mobius_sub A B C D a d ha hd]
  rw [mobius_sub A B C D b c hb hc]
  field_simp [hdet, ha, hb, hc, hd, had, hbc]
  ring

/-- Exchanging the first two marked sections sends the cross ratio to its reciprocal. -/
theorem crossRatio_swap_first_two
    (a b c d : ℝ)
    (hac : a-c ≠ 0) (hbd : b-d ≠ 0)
    (had : a-d ≠ 0) (hbc : b-c ≠ 0) :
    crossRatio b a c d = 1 / crossRatio a b c d := by
  unfold crossRatio
  field_simp [hac, hbd, had, hbc]
  ring

/-- Exchanging the middle two marked sections sends the cross ratio to `1-z`. -/
theorem crossRatio_swap_middle
    (a b c d : ℝ)
    (had : a-d ≠ 0) (hbc : b-c ≠ 0) :
    crossRatio a c b d = 1 - crossRatio a b c d := by
  unfold crossRatio
  field_simp [had, hbc]
  ring

/-- The two elementary permutation laws therefore realize the standard crossing generators
`z -> 1/z` and `z -> 1-z` on the four-section coordinate. -/
theorem crossing_generators_from_section_permutations
    (a b c d : ℝ)
    (hac : a-c ≠ 0) (hbd : b-d ≠ 0)
    (had : a-d ≠ 0) (hbc : b-c ≠ 0) :
    crossRatio b a c d = 1 / crossRatio a b c d ∧
    crossRatio a c b d = 1 - crossRatio a b c d := by
  exact ⟨crossRatio_swap_first_two a b c d hac hbd had hbc,
    crossRatio_swap_middle a b c d had hbc⟩

end GppSkyFourSectionCrossRatio
