import GppVerify.RiemannHypothesis.L2Constraint
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

/-!
# Scale-invariance diagnostic

For a positive scale `a`, the half-density-normalized multiplicative character is

  χ_s(a) = exp(log(a) * (s - 1/2)).

Its norm is `exp(log(a) * (Re s - 1/2))`. Hence on the critical line it is unitary under
all positive dilations. Off the line it grows or decays exponentially in logarithmic scale.
This is the exact mathematical content behind the heuristic comparison with a massless
scale-invariant sector versus a scale-breaking deformation.
-/

namespace GppScaleMass

open Complex

/-- Half-density-normalized dilation character. -/
noncomputable def dilationCharacter (s : ℂ) (a : ℝ) : ℂ :=
  Complex.exp ((Real.log a : ℂ) * (s - (1/2 : ℂ)))

/-- Exact norm of the normalized dilation character. -/
theorem norm_dilationCharacter (s : ℂ) (a : ℝ) :
    ‖dilationCharacter s a‖ = Real.exp (Real.log a * (s.re - 1/2)) := by
  unfold dilationCharacter
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.sub_re]

/-- On the critical line, every positive dilation has unit modulus. -/
theorem critical_line_dilation_unitary {s : ℂ} (hs : s.re = 1/2) (a : ℝ) :
    ‖dilationCharacter s a‖ = 1 := by
  rw [norm_dilationCharacter, hs]
  norm_num

/-- A single nontrivial positive scale detects the critical line from unit modulus. -/
theorem critical_line_of_dilation_unitary {s : ℂ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1)
    (hunit : ‖dilationCharacter s a‖ = 1) :
    s.re = 1/2 := by
  rw [norm_dilationCharacter] at hunit
  have hexp : Real.log a * (s.re - 1/2) = 0 := by
    apply Real.exp_injective
    simpa using hunit
  have hloga : Real.log a ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one ha ha1
  have hsub : s.re - 1/2 = 0 := (mul_eq_zero.mp hexp).resolve_left hloga
  exact sub_eq_zero.mp hsub

/-- Therefore the critical line is exactly the unitary dilation locus for any fixed
nontrivial positive scale. -/
theorem critical_line_iff_dilation_unitary {s : ℂ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1) :
    s.re = 1/2 ↔ ‖dilationCharacter s a‖ = 1 := by
  constructor
  · intro hs
    exact critical_line_dilation_unitary hs a
  · intro hu
    exact critical_line_of_dilation_unitary ha ha1 hu

end GppScaleMass

#print axioms GppScaleMass.norm_dilationCharacter
#print axioms GppScaleMass.critical_line_dilation_unitary
#print axioms GppScaleMass.critical_line_of_dilation_unitary
#print axioms GppScaleMass.critical_line_iff_dilation_unitary
