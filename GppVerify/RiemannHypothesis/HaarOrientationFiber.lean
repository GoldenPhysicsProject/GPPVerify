import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# Two-frequency Haar orientation fiber

For each nonzero spectral pair {+t,-t}, the Haar boundary has an exact two-state
orientation algebra.  This file formalizes the finite fiber:

  R      = frequency reflection,
  Sigma  = sign of frequency,
  Iq     = R Sigma,
  It     = i I,
  chi    = - Iq It,
  D      = swap plus coefficient conjugation.

The relations are exactly the four-lift relations from the orientation carrier.

A generic reflected boundary multiplier has matrix [[0,f+],[f-,0]].  Its anticommutator
with Iq is (f+ - f-) I.  Thus self-adjointness only requires f-=conj(f+), while
orientation oddness requires the stronger equality f+=f-.  On the xi critical line
the boundary value is real/even and both hold.
-/

namespace GppHaarOrientationFiber

open Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev V2C := Fin 2 → ℂ

/-- Reflection exchanging +t and -t. -/
def refl : M2C := !![0,1;1,0]

/-- Frequency-sign grading. -/
def freqSign : M2C := !![1,0;0,-1]

/-- Canonical Haar quarter-turn `R Sigma`. -/
def Iq : M2C := refl * freqSign

/-- Ambient Hilbert complex structure. -/
def It : M2C := !![Complex.I,0;0,Complex.I]

/-- Relative orientation grading. -/
def chi : M2C := -(Iq * It)

/-- Antiunitary critical real structure: reflect frequency and conjugate coefficients. -/
def critD (v : V2C) : V2C :=
  ![(starRingEnd ℂ) (v 1), (starRingEnd ℂ) (v 0)]

theorem Iq_explicit : Iq = !![0,-1;1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Iq, refl, freqSign, Matrix.mul_apply, Fin.sum_univ_two]

theorem chi_explicit : chi = !![0,Complex.I;-Complex.I,0] := by
  rw [Iq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chi, It, Matrix.mul_apply, Fin.sum_univ_two]

theorem Iq_sq_neg_one : Iq * Iq = -(1 : M2C) := by
  rw [Iq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem It_sq_neg_one : It * It = -(1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [It, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Complex.I_mul_I]

theorem Iq_It_commute : Iq * It = It * Iq := by
  rw [Iq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [It, Matrix.mul_apply, Fin.sum_univ_two]

theorem chi_sq_one : chi * chi = (1 : M2C) := by
  rw [chi_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Complex.I_mul_I] <;> ring

/-- `D` is conjugate-linear over the ambient Hilbert scalar field. -/
theorem critD_smul (c : ℂ) (v : V2C) :
    critD (c • v) = (starRingEnd ℂ c) • critD v := by
  ext i
  fin_cases i <;> simp [critD]

theorem critD_sq (v : V2C) : critD (critD v) = v := by
  ext i
  fin_cases i <;> simp [critD]

/-- `D` reverses the Haar quarter-turn. -/
theorem critD_anticommutes_Iq (v : V2C) :
    critD (Iq *ᵥ v) = -(Iq *ᵥ critD v) := by
  rw [Iq_explicit]
  ext i
  fin_cases i <;>
    simp [critD, Matrix.mulVec, Fin.sum_univ_two]

/-- `D` also reverses the scalar complex structure because it is anti-linear. -/
theorem critD_anticommutes_It (v : V2C) :
    critD (It *ᵥ v) = -(It *ᵥ critD v) := by
  ext i
  fin_cases i <;>
    simp [critD, It, Matrix.mulVec, Fin.sum_univ_two]

/-- Their relative grading is D-even. -/
theorem critD_commutes_chi (v : V2C) :
    critD (chi *ᵥ v) = chi *ᵥ critD v := by
  rw [chi_explicit]
  ext i
  fin_cases i <;>
    simp [critD, Matrix.mulVec, Fin.sum_univ_two]

/-- Generic multiplication-reflection boundary block on the +/-t pair. -/
def reflectedBoundary (fplus fminus : ℂ) : M2C :=
  !![0,fplus;fminus,0]

/-- Its square is the scalar product f+ f-. -/
theorem reflectedBoundary_sq (fplus fminus : ℂ) :
    reflectedBoundary fplus fminus * reflectedBoundary fplus fminus =
      (fplus * fminus) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectedBoundary, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> ring

/-- Reality relation f-=conj(f+) is exactly self-adjointness of the reflected block. -/
theorem reflectedBoundary_selfAdjoint_of_reality
    (fplus fminus : ℂ)
    (hreal : fminus = (starRingEnd ℂ) fplus) :
    Matrix.conjTranspose (reflectedBoundary fplus fminus) =
      reflectedBoundary fplus fminus := by
  subst fminus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectedBoundary, Matrix.conjTranspose_apply]

/-- The orientation anticommutator measures the mismatch of the two reflected values. -/
theorem reflectedBoundary_anticommutator_Iq
    (fplus fminus : ℂ) :
    reflectedBoundary fplus fminus * Iq +
      Iq * reflectedBoundary fplus fminus =
      (fplus - fminus) • (1 : M2C) := by
  rw [Iq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectedBoundary, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> ring

/-- On a real/even boundary fiber the first-order block is orientation-odd. -/
theorem reflectedBoundary_anticommutes_of_equal
    (f : ℂ) :
    reflectedBoundary f f * Iq + Iq * reflectedBoundary f f = 0 := by
  rw [reflectedBoundary_anticommutator_Iq]
  simp

/-- A real/even scalar has a positive square. -/
theorem real_even_boundary_sq (x : ℝ) :
    reflectedBoundary (x : ℂ) (x : ℂ) *
      reflectedBoundary (x : ℂ) (x : ℂ) =
      ((x : ℂ)^2) • (1 : M2C) := by
  rw [reflectedBoundary_sq]

end GppHaarOrientationFiber

#print axioms GppHaarOrientationFiber.Iq_sq_neg_one
#print axioms GppHaarOrientationFiber.critD_anticommutes_Iq
#print axioms GppHaarOrientationFiber.critD_commutes_chi
#print axioms GppHaarOrientationFiber.reflectedBoundary_anticommutator_Iq
