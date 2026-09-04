import Mathlib.Tactic
import GppVerify.CelestialHolography.FourierSliceSupportGeometry
import GppVerify.CelestialHolography.SplitPolarityComplementBridge

/-!
# Fourier dual space versus split metric polarity

The four-dimensional Fourier transform naturally takes a twistor variable in `V` to
a dual variable in `V*`.  The split metric diag(+,+,-,-) identifies `V*` back with
`V` by the musical isomorphism which changes the signs of the final two coordinates.

Under this identification, the ordinary annihilator plane selected by Fourier-slice
support becomes the split-orthogonal plane, up to the central projective sign `-1`.
Thus the apparent sign difference between

  ordinary annihilator:  -A^{-T}
  split Hodge polarity:  +A^{-T}

is exactly the metric identification `V* -> V` plus projectivization.
-/

namespace GppFourierDualSplitPolarity

open GppTwistorAnnihilatorIncidence
open GppIncidenceKernelGoogly
open GppFourierSliceSupportGeometry
open GppSplitPolarityComplementBridge

/-- The split metric sharp map on coordinate covectors: diag(+,+,-,-). -/
def splitSharp (ξ : V4) : V4 :=
  (ξ.1, ξ.2.1, -ξ.2.2.1, -ξ.2.2.2)

/-- A general vector on the split-orthogonal 2-plane. -/
def splitDualLineVector (a b c d t u : ℝ) : V4 :=
  (t*a + u*b, t*c + u*d, t, u)

/-- Coordinate scaling on four-vectors. -/
def scaleV4 (λ : ℝ) (x : V4) : V4 :=
  (λ*x.1, λ*x.2.1, λ*x.2.2.1, λ*x.2.2.2)

/-- The split metric identification sends an ordinary annihilator covector to minus
the corresponding split-orthogonal vector. -/
theorem sharp_annihilator_eq_minus_split_polarity
    (a b c d t u : ℝ) :
    splitSharp (dualLineVector a b c d t u) =
      scaleV4 (-1) (splitDualLineVector a b c d t u) := by
  simp [splitSharp, dualLineVector, splitDualLineVector, scaleV4]
  constructor <;> ring

/-- The split-dual vector is indeed orthogonal to every graph-line vector for the
split metric. -/
theorem splitDualLineVector_is_orthogonal
    (a b c d r s t u : ℝ) :
    splitPair4 (lineVector a b c d r s)
      (splitDualLineVector a b c d t u) = 0 := by
  simp [splitPair4, lineVector, splitDualLineVector]
  ring

/-- Fourier-slice support, after the split musical identification, lies on the same
projective plane as split metric polarity.  The equality is explicit up to `-1`. -/
theorem fourier_support_sharp_is_projective_split_polarity
    (a b c d : ℝ) (ξ : V4)
    (h1 : phaseConstraint1 a b ξ = 0)
    (h2 : phaseConstraint2 c d ξ = 0) :
    splitSharp ξ =
      scaleV4 (-1)
        (splitDualLineVector a b c d ξ.2.2.1 ξ.2.2.2) := by
  have hξ := constraints_parameterize_annihilator a b c d ξ h1 h2
  rw [hξ]
  exact sharp_annihilator_eq_minus_split_polarity
    a b c d ξ.2.2.1 ξ.2.2.2

/-- The split musical map is involutive. -/
theorem splitSharp_involutive (ξ : V4) :
    splitSharp (splitSharp ξ) = ξ := by
  rcases ξ with ⟨x0,x1,x2,x3⟩
  simp [splitSharp]

/-- Central sign scaling is itself involutive. -/
theorem scaleV4_minus_one_sq (x : V4) :
    scaleV4 (-1) (scaleV4 (-1) x) = x := by
  rcases x with ⟨x0,x1,x2,x3⟩
  simp [scaleV4]

end GppFourierDualSplitPolarity
