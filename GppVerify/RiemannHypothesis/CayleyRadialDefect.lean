import Mathlib.Tactic
import GppVerify.RiemannHypothesis.CayleyShadowAdjointBridge

/-!
# Quantitative Cayley radial defect

For the RH Cayley coordinate

    beta(s)=(s-1)/s,

the distance from the unitary boundary is not merely qualitative.  Away from s=0,

    1 - |beta(s)|^2 = (2 Re(s)-1)/|s|^2.

Thus the radial disk defect is exactly the horizontal displacement from the critical line,
normalized by |s|^2.

For a hypothetical bad zero rho with Re(rho)>1/2, beta(rho) lies strictly inside the disk
and the positive defect is explicit.
-/

namespace GppCayleyRadialDefect

open Complex
open GppCayleyShadowAdjointBridge

/-- Numerator identity behind the Cayley defect formula. -/
theorem normSq_sub_one_defect (s : ℂ) :
    Complex.normSq s - Complex.normSq (s - 1) = 2*s.re - 1 := by
  simp [Complex.normSq_apply]
  ring

/-- Exact normalized horizontal-displacement formula. -/
theorem cayley_radial_defect
    (s : ℂ) (hs : s ≠ 0) :
    1 - Complex.normSq (beta s) =
      (2*s.re - 1) / Complex.normSq s := by
  unfold beta
  rw [Complex.normSq_div]
  have hns : Complex.normSq s ≠ 0 := by
    exact ne_of_gt ((Complex.normSq_pos).2 hs)
  field_simp [hns]
  exact normSq_sub_one_defect s

/-- Right-half-plane points lie strictly inside the Cayley disk. -/
theorem normSq_beta_lt_one_of_half_lt_re
    (s : ℂ) (hs : s ≠ 0)
    (hcrit : (1/2 : ℝ) < s.re) :
    Complex.normSq (beta s) < 1 := by
  have hd := cayley_radial_defect s hs
  have hden : 0 < Complex.normSq s := (Complex.normSq_pos).2 hs
  have hnum : 0 < 2*s.re - 1 := by linarith
  have hquot : 0 < (2*s.re - 1) / Complex.normSq s :=
    div_pos hnum hden
  linarith

/-- Left-half-plane points lie strictly outside the Cayley unit circle. -/
theorem one_lt_normSq_beta_of_re_lt_half
    (s : ℂ) (hs : s ≠ 0)
    (hcrit : s.re < (1/2 : ℝ)) :
    1 < Complex.normSq (beta s) := by
  have hd := cayley_radial_defect s hs
  have hden : 0 < Complex.normSq s := (Complex.normSq_pos).2 hs
  have hnum : 2*s.re - 1 < 0 := by linarith
  have hquot : (2*s.re - 1) / Complex.normSq s < 0 :=
    div_neg_of_neg_of_pos hnum hden
  linarith

/-- The Cayley norm-square equals one exactly on the critical line. -/
theorem normSq_beta_eq_one_iff_critical
    (s : ℂ) (hs : s ≠ 0) :
    Complex.normSq (beta s) = 1 ↔ s.re = (1/2 : ℝ) := by
  constructor
  · intro h
    have hd := cayley_radial_defect s hs
    rw [h] at hd
    have hden : Complex.normSq s ≠ 0 :=
      ne_of_gt ((Complex.normSq_pos).2 hs)
    have hnum : 2*s.re - 1 = 0 := by
      apply (div_eq_zero_iff).mp
      simpa using hd.symm
    linarith
  · intro h
    have hd := cayley_radial_defect s hs
    have hnum : 2*s.re - 1 = 0 := by linarith
    rw [hnum, zero_div] at hd
    linarith

end GppCayleyRadialDefect

#print axioms GppCayleyRadialDefect.cayley_radial_defect
#print axioms GppCayleyRadialDefect.normSq_beta_eq_one_iff_critical
