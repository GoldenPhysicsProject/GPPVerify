import GppVerify.RiemannHypothesis.ScaleMassDiagnostic
import Mathlib.Tactic

/-!
# Finite-Haar quotient transport and the principal series

For a finite quotient H ->> G with kernel size k, the constant-function line in
l2 with counting Haar measure acquires a factor sqrt(k) in norm under raw pullback.

Twisting the pullback by k^(-s) therefore gives the centered norm factor

  k^(1/2 - Re s).

This module packages that scalar law in the same normalization as the existing
half-density dilation character. It is the finite-group counterpart of the
continuous principal-series/dilation theorem.

No zeta-zero survival statement is made here.
-/

namespace GppFiniteHaarQuotientPrincipalSeries

open Complex
open GppScaleMass

/-- Centered character carried by an s-twisted finite quotient of kernel size k.
It is the inverse of the half-density-normalized dilation character. -/
noncomputable def haarQuotientCharacter (s : ℂ) (k : ℝ) : ℂ :=
  (dilationCharacter s k)⁻¹

/-- Exact norm law for the Haar-normalized quotient character. -/
theorem norm_haarQuotientCharacter (s : ℂ) (k : ℝ) :
    ‖haarQuotientCharacter s k‖ =
      Real.exp (Real.log k * ((1 : ℝ) / 2 - s.re)) := by
  unfold haarQuotientCharacter
  rw [norm_inv, norm_dilationCharacter]
  rw [← Real.exp_neg]
  congr 1
  ring

/-- A single nontrivial finite quotient is Haar-isometric exactly at Re(s)=1/2. -/
theorem critical_line_iff_haar_quotient_isometry
    {s : ℂ} {k : ℝ} (hk : 0 < k) (hk1 : k ≠ 1) :
    s.re = (1 : ℝ) / 2 ↔ ‖haarQuotientCharacter s k‖ = 1 := by
  rw [norm_haarQuotientCharacter]
  constructor
  · intro hs
    rw [hs]
    norm_num
  · intro hunit
    have hexp : Real.log k * ((1 : ℝ) / 2 - s.re) = 0 := by
      apply Real.exp_injective
      simpa using hunit
    have hlog : Real.log k ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hk hk1
    have hsub : (1 : ℝ) / 2 - s.re = 0 :=
      (mul_eq_zero.mp hexp).resolve_left hlog
    linarith

/-- Above the critical line, quotient pullback contracts in the counting-Haar norm. -/
theorem supercritical_haar_quotient_contracts
    {s : ℂ} {k : ℝ} (hk : 1 < k) (hs : (1 : ℝ) / 2 < s.re) :
    ‖haarQuotientCharacter s k‖ < 1 := by
  rw [norm_haarQuotientCharacter, Real.exp_lt_one_iff]
  exact mul_neg_of_pos_of_neg (Real.log_pos hk) (sub_neg.mpr hs)

/-- Below the critical line, quotient pullback expands in the counting-Haar norm. -/
theorem subcritical_haar_quotient_expands
    {s : ℂ} {k : ℝ} (hk : 1 < k) (hs : s.re < (1 : ℝ) / 2) :
    1 < ‖haarQuotientCharacter s k‖ := by
  rw [norm_haarQuotientCharacter, Real.one_lt_exp_iff]
  exact mul_pos (Real.log_pos hk) (sub_pos.mpr hs)

/-- One-sided contractive survival for a parameter and its shadow-conjugate already forces
the critical line. This is weaker than asking the quotient transport to be unitary or
two-sided bounded.

In an RH application, the second hypothesis is supplied by applying the same physical
survival theorem to the functional-equation companion zero `1 - (starRingEnd ℂ) s`. -/
theorem critical_line_of_reflected_quotient_contractions
    {s : ℂ} {k : ℝ} (hk : 1 < k)
    (hs : ‖haarQuotientCharacter s k‖ ≤ 1)
    (href : ‖haarQuotientCharacter (1 - (starRingEnd ℂ) s) k‖ ≤ 1) :
    s.re = (1 : ℝ) / 2 := by
  have hs_ge : (1 : ℝ) / 2 ≤ s.re := by
    by_contra h
    have hlt : s.re < (1 : ℝ) / 2 := lt_of_not_ge h
    have hexpand := subcritical_haar_quotient_expands hk hlt
    linarith
  have href_ge : (1 : ℝ) / 2 ≤ (1 - (starRingEnd ℂ) s).re := by
    by_contra h
    have hlt : (1 - (starRingEnd ℂ) s).re < (1 : ℝ) / 2 := lt_of_not_ge h
    have hexpand :=
      subcritical_haar_quotient_expands (s := 1 - (starRingEnd ℂ) s) hk hlt
    linarith
  have href_re : (1 - (starRingEnd ℂ) s).re = 1 - s.re := by
    simp [Complex.sub_re, Complex.one_re, RCLike.star_def, Complex.conj_re]
  rw [href_re] at href_ge
  linarith

end GppFiniteHaarQuotientPrincipalSeries

#print axioms GppFiniteHaarQuotientPrincipalSeries.norm_haarQuotientCharacter
#print axioms GppFiniteHaarQuotientPrincipalSeries.critical_line_iff_haar_quotient_isometry
#print axioms GppFiniteHaarQuotientPrincipalSeries.supercritical_haar_quotient_contracts
#print axioms GppFiniteHaarQuotientPrincipalSeries.subcritical_haar_quotient_expands
#print axioms GppFiniteHaarQuotientPrincipalSeries.critical_line_of_reflected_quotient_contractions
