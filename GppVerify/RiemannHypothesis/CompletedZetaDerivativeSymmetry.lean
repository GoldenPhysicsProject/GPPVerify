import GppVerify.RiemannHypothesis.FunctionalEquation
import Mathlib.Tactic

/-!
# Derivative symmetry of the completed Riemann zeta function

Mathlib proves the completed functional equation

  Lambda(1-s) = Lambda(s)

for `completedRiemannZeta`, and proves differentiability away from its two poles `0,1`.
Differentiating the functional equation therefore gives the exact antisymmetry

  Lambda'(s) = -Lambda'(1-s).

This is a genuinely global statement about the analytically continued completed zeta
function, not a finite Euler-product approximation.  It is one of the constraints any
prime--Archimedean completed logarithmic-derivative operator must reproduce.

No RH claim is made here.
-/

namespace GppCompletedZetaDerivative

open Complex

/-- The reflected point `1-s` avoids the pole at `0` whenever `s != 1`. -/
lemma one_sub_ne_zero {s : ℂ} (hs1 : s ≠ 1) : 1 - s ≠ 0 := by
  intro h
  apply hs1
  linarith

/-- The reflected point `1-s` avoids the pole at `1` whenever `s != 0`. -/
lemma one_sub_ne_one {s : ℂ} (hs0 : s ≠ 0) : 1 - s ≠ 1 := by
  intro h
  apply hs0
  linarith

/-- **Differentiated completed functional equation.** Away from the poles,
`Lambda'(s) = -Lambda'(1-s)`. -/
theorem completedRiemannZeta_deriv_reflection {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv completedRiemannZeta s = -deriv completedRiemannZeta (1 - s) := by
  have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_const (x := s) (c := (1 : ℂ))).sub (hasDerivAt_id s)
  have hrefDiff : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta (one_sub_ne_zero hs1) (one_sub_ne_one hs0)
  have hcomp : HasDerivAt (fun z : ℂ => completedRiemannZeta (1 - z))
      (deriv completedRiemannZeta (1 - s) * (-1)) s :=
    hrefDiff.hasDerivAt.comp s hinner
  have hfun : completedRiemannZeta = fun z : ℂ => completedRiemannZeta (1 - z) := by
    funext z
    exact (completedRiemannZeta_one_sub z).symm
  have hd : deriv completedRiemannZeta s =
      deriv (fun z : ℂ => completedRiemannZeta (1 - z)) s :=
    congrArg (fun f : ℂ → ℂ => deriv f s) hfun
  rw [hcomp.deriv] at hd
  simpa using hd

/-- Equivalent reflected orientation. -/
theorem completedRiemannZeta_deriv_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv completedRiemannZeta (1 - s) = -deriv completedRiemannZeta s := by
  have h := completedRiemannZeta_deriv_reflection hs0 hs1
  linarith

end GppCompletedZetaDerivative

#print axioms GppCompletedZetaDerivative.completedRiemannZeta_deriv_reflection
#print axioms GppCompletedZetaDerivative.completedRiemannZeta_deriv_one_sub
