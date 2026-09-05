import Mathlib.Tactic
import GppVerify.CelestialHolography.FourierSliceSupportGeometry
import GppVerify.CelestialHolography.SplitPolarityComplementBridge

/-!
# Fourier dual space versus a chosen split polarity

The four-dimensional Fourier transform naturally takes a twistor variable in `V` to
a dual variable in `V*`.  This file studies what happens after choosing the bilinear
form `diag(+,+,-,-)` on the ambient four-dimensional coordinate space and using its
musical isomorphism to identify `V*` back with `V`.

Under this chosen identification, the ordinary annihilator plane selected by Fourier-slice
support becomes the split-orthogonal plane, up to the central projective sign `-1`.
Thus the apparent sign difference between

  ordinary annihilator:  -A^{-T}
  chosen split polarity: +A^{-T}

is exactly the musical identification `V* -> V` plus projectivization.

IMPORTANT CANONICALITY CAVEAT: in the standard split twistor model the conformal group
acts as `SL(4,R)` on the twistor fundamental, while the spacetime split conformal metric
arises on the Grassmannian/tangent `M_2(R)` (or equivalently from the Klein form on
`Λ²V`).  A symmetric form `diag(+,+,-,-)` on the twistor fundamental is additional
structure; it is not invariant under all determinant-one changes of twistor basis.  The
last theorem gives an explicit determinant-one counterexample.  Consequently the
support-to-polarity bridge below is exact conditional geometry for this chosen polarity,
not an epsilon-only or conformally canonical identification `V* ≅ V`.
-/

namespace GppFourierDualSplitPolarity

open GppTwistorAnnihilatorIncidence
open GppIncidenceKernelGoogly
open GppFourierSliceSupportGeometry
open GppSplitPolarityComplementBridge

/-- The chosen split sharp map on coordinate covectors: diag(+,+,-,-). -/
def splitSharp (ξ : V4) : V4 :=
  (ξ.1, ξ.2.1, -ξ.2.2.1, -ξ.2.2.2)

/-- A general vector on the split-orthogonal 2-plane. -/
def splitDualLineVector (a b c d t u : ℝ) : V4 :=
  (t*a + u*b, t*c + u*d, t, u)

/-- Coordinate scaling on four-vectors. -/
def scaleV4 (λ : ℝ) (x : V4) : V4 :=
  (λ*x.1, λ*x.2.1, λ*x.2.2.1, λ*x.2.2.2)

/-- The chosen split metric identification sends an ordinary annihilator covector to
minus the corresponding split-orthogonal vector. -/
theorem sharp_annihilator_eq_minus_split_polarity
    (a b c d t u : ℝ) :
    splitSharp (dualLineVector a b c d t u) =
      scaleV4 (-1) (splitDualLineVector a b c d t u) := by
  simp [splitSharp, dualLineVector, splitDualLineVector, scaleV4]
  constructor <;> ring

/-- The split-dual vector is indeed orthogonal to every graph-line vector for the
chosen split bilinear form. -/
theorem splitDualLineVector_is_orthogonal
    (a b c d r s t u : ℝ) :
    splitPair4 (lineVector a b c d r s)
      (splitDualLineVector a b c d t u) = 0 := by
  simp [splitPair4, lineVector, splitDualLineVector]
  ring

/-- Fourier-slice support, after the chosen musical identification, lies on the same
projective plane as the chosen split metric polarity.  The equality is explicit up to
`-1`. -/
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

/-- The chosen musical map is involutive. -/
theorem splitSharp_involutive (ξ : V4) :
    splitSharp (splitSharp ξ) = ξ := by
  rcases ξ with ⟨x0,x1,x2,x3⟩
  simp [splitSharp]

/-- Central sign scaling is itself involutive. -/
theorem scaleV4_minus_one_sq (x : V4) :
    scaleV4 (-1) (scaleV4 (-1) x) = x := by
  rcases x with ⟨x0,x1,x2,x3⟩
  simp [scaleV4]

/-! ## The chosen polarity is extra structure -/

/-- A simple diagonal determinant-one change of ambient twistor coordinates.  Its
coordinate product is `2 * (1/2) * 1 * 1 = 1`, so it is an elementary `SL(4,R)` test
transformation without importing matrix determinant machinery. -/
def detOneTestScale (x : V4) : V4 :=
  (2*x.1, x.2.1/2, x.2.2.1, x.2.2.2)

/-- Coordinate determinant factor of the test transformation is exactly one. -/
theorem detOneTestScale_volume_factor :
    (2 : ℝ) * (1/2 : ℝ) * 1 * 1 = 1 := by
  norm_num

/-- First standard basis vector. -/
def basis0 : V4 := (1,0,0,0)

/-- The chosen split bilinear form is not invariant under the determinant-one test
transformation: the squared norm of `e0` changes from `1` to `4`.  Hence this polarity
is not preserved by the full `SL(4,R)` action and cannot be attributed to the split
conformal real slice alone. -/
theorem chosen_split_pair_not_SL4_invariant :
    splitPair4 (detOneTestScale basis0) (detOneTestScale basis0) = 4 ∧
    splitPair4 basis0 basis0 = 1 := by
  norm_num [splitPair4, detOneTestScale, basis0]

/-- The sharp map itself has diagonal determinant factor `(+1)(+1)(-1)(-1)=+1`.
In particular, even after choosing it, this musical identification is not a four-orientation
reversal (which would require negative determinant for a linear automorphism). -/
theorem splitSharp_diagonal_determinant_factor :
    (1 : ℝ) * 1 * (-1) * (-1) = 1 := by
  norm_num

end GppFourierDualSplitPolarity
