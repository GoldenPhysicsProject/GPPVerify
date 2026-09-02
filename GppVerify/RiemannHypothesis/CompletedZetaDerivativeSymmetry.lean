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
  exact (sub_eq_zero.mp h).symm

/-- The reflected point `1-s` avoids the pole at `1` whenever `s != 0`. -/
lemma one_sub_ne_one {s : ℂ} (hs0 : s ≠ 0) : 1 - s ≠ 1 := by
  intro h
  apply hs0
  exact sub_eq_self.mp h

/-- **Differentiated completed functional equation.** Away from the poles,
`Lambda'(s) = -Lambda'(1-s)`. -/
theorem completedRiemannZeta_deriv_reflection {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv completedRiemannZeta s = -deriv completedRiemannZeta (1 - s) := by
  have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    -- Mathlib 4.33: `HasDerivAt.sub` returns the point-free `(fun _ => 1) - id` with
    -- derivative `0 - 1`. Fix the value arithmetically, then let `exact` absorb the
    -- Pi-lifting by defeq — do not simp the hypothesis, which moves it onto another
    -- instance path.
    have h := (hasDerivAt_const (x := s) (c := (1 : ℂ))).sub (hasDerivAt_id s)
    have hval : (0 : ℂ) - 1 = -1 := by ring
    rw [hval] at h
    exact h
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
  simpa using (congrArg Neg.neg h).symm

/-- **Reflected logarithmic derivative.** Wherever the completed zeta factor is nonzero,
its logarithmic derivative is odd under `s ↦ 1-s`. -/
theorem completedRiemannZeta_logDeriv_reflection {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv completedRiemannZeta s / completedRiemannZeta s =
      -(deriv completedRiemannZeta (1 - s) / completedRiemannZeta (1 - s)) := by
  have hval : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  rw [completedRiemannZeta_deriv_reflection hs0 hs1, hval]
  ring

/-- **Central stationary point.** Reflection symmetry forces the derivative of the
completed zeta function to vanish at the fixed point `s = 1/2`. -/
theorem completedRiemannZeta_deriv_one_half :
    deriv completedRiemannZeta (1 / 2 : ℂ) = 0 := by
  have h0 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have h1 : (1 / 2 : ℂ) ≠ 1 := by norm_num
  have h := completedRiemannZeta_deriv_reflection h0 h1
  have hreflect : (1 : ℂ) - (1 / 2 : ℂ) = 1 / 2 := by ring
  rw [hreflect] at h
  have htwo : (2 : ℂ) * deriv completedRiemannZeta (1 / 2 : ℂ) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end GppCompletedZetaDerivative

#print axioms GppCompletedZetaDerivative.completedRiemannZeta_deriv_reflection
#print axioms GppCompletedZetaDerivative.completedRiemannZeta_deriv_one_sub
#print axioms GppCompletedZetaDerivative.completedRiemannZeta_logDeriv_reflection
#print axioms GppCompletedZetaDerivative.completedRiemannZeta_deriv_one_half
