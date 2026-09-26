import GppVerify.RiemannHypothesis.CompletedZetaReality
import GppVerify.RiemannHypothesis.CompletedZetaDerivativeSymmetry
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
# Completed-zeta critical-line logarithmic response

The completed zeta function is real on `Re s = 1/2`. Combining its conjugation
symmetry with Mathlib's derivative-under-conjugation theorem shows that its complex
derivative is purely imaginary there. Consequently its logarithmic derivative has
zero real part wherever the completed zeta value is nonzero.

No zero-location statement is inferred.
-/

namespace GppCompletedZetaCriticalResponse

open Complex
open scoped ComplexConjugate

/-- Positive real half-plane used for the conjugation identity. -/
def positiveHalfPlane : Set ℂ := {s | 0 < s.re}

lemma isOpen_positiveHalfPlane : IsOpen positiveHalfPlane := by
  exact isOpen_lt continuous_const continuous_re

/-- On the positive half-plane, `conj ∘ Λ ∘ conj` equals `Λ`. -/
theorem completedZeta_eqOn_conj_conj :
    positiveHalfPlane.EqOn completedRiemannZeta
      (conj ∘ completedRiemannZeta ∘ conj) := by
  intro s hs
  have hcs : 0 < (conj s).re := by simpa using hs
  have h := GppCompletedZetaReality.completedRiemannZeta_conj hcs
  simpa [Function.comp_def] using h

/-- The derivative of completed zeta respects complex conjugation on `Re s > 0`. -/
theorem completedRiemannZeta_deriv_conj {s : ℂ} (hs : 0 < s.re) :
    deriv completedRiemannZeta (conj s) = conj (deriv completedRiemannZeta s) := by
  have hd := completedZeta_eqOn_conj_conj.iteratedDeriv_of_isOpen
    isOpen_positiveHalfPlane 1 hs
  simp [iteratedDeriv_one, Function.comp_def, deriv_conj_conj] at hd
  have hc := congrArg conj hd
  simpa using hc.symm

/-- On the critical line the completed-zeta derivative is purely imaginary. -/
theorem completedRiemannZeta_deriv_re_eq_zero_of_re_half {s : ℂ}
    (hs : s.re = 1 / 2) :
    (deriv completedRiemannZeta s).re = 0 := by
  have hspos : 0 < s.re := by rw [hs]; norm_num
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hreflect : conj s = 1 - s :=
    GppFE.critical_line_is_fixed_locus s |>.2 hs
  have hderConj := completedRiemannZeta_deriv_conj hspos
  have hderRefl := GppCompletedZetaDerivative.completedRiemannZeta_deriv_reflection hs0 hs1
  rw [← hreflect] at hderRefl
  rw [hderConj] at hderRefl
  have hre := congrArg Complex.re hderRefl
  simp [Complex.conj_re] at hre
  linarith

/-- Wherever completed zeta is nonzero on the critical line, its logarithmic
response has zero real part. The nonzero hypothesis records the analytic domain of
the logarithmic derivative even though Lean's division is totalized. -/
theorem completedRiemannZeta_logDeriv_re_eq_zero_of_re_half {s : ℂ}
    (hs : s.re = 1 / 2) (hΛ : completedRiemannZeta s ≠ 0) :
    (deriv completedRiemannZeta s / completedRiemannZeta s).re = 0 := by
  have hvalIm := GppCompletedZetaReality.completedRiemannZeta_im_eq_zero_of_re_half hs
  have hderRe := completedRiemannZeta_deriv_re_eq_zero_of_re_half hs
  have hnum : deriv completedRiemannZeta s =
      Complex.I * ((deriv completedRiemannZeta s).im : ℂ) := by
    apply Complex.ext
    · simp [hderRe]
    · simp
  have hden : completedRiemannZeta s = ((completedRiemannZeta s).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hvalIm]
  rw [hnum, hden]
  simp

end GppCompletedZetaCriticalResponse

#print axioms GppCompletedZetaCriticalResponse.completedRiemannZeta_deriv_conj
#print axioms GppCompletedZetaCriticalResponse.completedRiemannZeta_deriv_re_eq_zero_of_re_half
#print axioms GppCompletedZetaCriticalResponse.completedRiemannZeta_logDeriv_re_eq_zero_of_re_half
