import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorAnnihilatorIncidence

/-!
# Incidence kernel for the twistor/dual-twistor googly transform

The annihilator of a spacetime 2-plane does not select a single dual twistor point.
Instead it produces an entire dual projective line.  Consequently the canonical
finite-dimensional geometry is a correspondence: every point on the twistor line of
`W` pairs to zero with every point on the dual twistor line of `W^0`.

This file proves that statement on the Gr(2,4) big cell.  It is the algebraic kernel
that a genuine field-level integral/cohomological transform may use.  No claim is made
here that the analytic Penrose/Fourier transform has already been constructed.
-/

namespace GppIncidenceKernelGoogly

open GppTwistorAnnihilatorIncidence

/-- A general vector on the graph-plane twistor line. -/
def lineVector (a b c d r s : ℝ) : V4 :=
  (r, s, r*a + s*c, r*b + s*d)

/-- A general covector on the annihilator dual-twistor line. -/
def dualLineVector (a b c d t u : ℝ) : V4 :=
  (-(t*a + u*b), -(t*c + u*d), t, u)

/-- Every point of the graph line is incident with every point of its annihilator
line: the ambient twistor/dual-twistor pairing vanishes identically. -/
theorem line_dualLine_pair_zero
    (a b c d r s t u : ℝ) :
    pair4 (lineVector a b c d r s) (dualLineVector a b c d t u) = 0 := by
  simp [pair4, lineVector, dualLineVector]
  ring

/-- The displayed line vector is exactly the linear combination of the two graph rows. -/
theorem lineVector_eq_span
    (a b c d r s : ℝ) :
    lineVector a b c d r s =
      (r * (graphRow1 a b).1 + s * (graphRow2 c d).1,
       r * (graphRow1 a b).2.1 + s * (graphRow2 c d).2.1,
       r * (graphRow1 a b).2.2.1 + s * (graphRow2 c d).2.2.1,
       r * (graphRow1 a b).2.2.2 + s * (graphRow2 c d).2.2.2) := by
  simp [lineVector, graphRow1, graphRow2]

/-- Likewise the dual-line vector is the linear combination of the two canonical
annihilator directions. -/
theorem dualLineVector_eq_span
    (a b c d t u : ℝ) :
    dualLineVector a b c d t u =
      (t * (annihilator1 a c).1 + u * (annihilator2 b d).1,
       t * (annihilator1 a c).2.1 + u * (annihilator2 b d).2.1,
       t * (annihilator1 a c).2.2.1 + u * (annihilator2 b d).2.2.1,
       t * (annihilator1 a c).2.2.2 + u * (annihilator2 b d).2.2.2) := by
  simp [dualLineVector, annihilator1, annihilator2]
  constructor <;> ring

/-- The annihilator correspondence is non-pointlike: the two parameter choices
`(t,u)=(1,0)` and `(0,1)` give distinct dual directions. -/
theorem dualLine_has_two_distinct_directions (a b c d : ℝ) :
    dualLineVector a b c d 1 0 ≠ dualLineVector a b c d 0 1 := by
  intro h
  have h3 := congrArg (fun x : V4 => x.2.2.1) h
  norm_num [dualLineVector] at h3

/-- Both canonical dual directions annihilate every point of the original twistor
line, making the correspondence a whole `P(W) x P(W^0)` fibre rather than a graph of
a point map. -/
theorem both_dual_directions_annihilate_line
    (a b c d r s : ℝ) :
    pair4 (lineVector a b c d r s) (dualLineVector a b c d 1 0) = 0 ∧
    pair4 (lineVector a b c d r s) (dualLineVector a b c d 0 1) = 0 := by
  constructor <;> apply line_dualLine_pair_zero

end GppIncidenceKernelGoogly
