import GppVerify.RiemannHypothesis.VonMangoldtCumulantDerivativeBridge
import GppVerify.RiemannHypothesis.ZetaGibbsFisher
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Strict positivity of the zeta-Gibbs third cumulant

This file closes the analytic transfer from the strictly positive cubic von Mangoldt
series to the actual third Gibbs cumulant already defined in `ZetaGibbsFisher`.

On `Re s > 1`, zeta is analytic and nonzero.  We therefore differentiate the genuine
negative logarithmic derivative twice and identify the result with

  -zeta'''/zeta + 3 (zeta''/zeta)(zeta'/zeta) - 2 (zeta'/zeta)^3.

The preceding von-Mangoldt derivative bridge proves that this same quantity is the
strictly positive arithmetic series `sum Lambda(n) (log n)^2 n^-beta` on the real axis.
No analytic continuation of the sign is used or claimed.
-/

namespace GppZetaThirdCumulantStrict

open Complex LSeries Set
open GppGlobalVonMangoldt
open GppZetaGibbsMoments
open GppZetaGibbsFisher
open GppVonMangoldtCumulantDerivativeBridge
open GppVonMangoldtCubicPositivity

/-- The Dirichlet-series half-plane avoids zeta's pole at `1`. -/
theorem zetaHalfPlane_subset_compl_one :
    zetaHalfPlane ⊆ ({1} : Set ℂ)ᶜ := by
  intro s hs
  have hs' : s ≠ 1 := by
    intro h
    subst s
    norm_num [zetaHalfPlane] at hs
  simpa using hs'

/-- Zeta is analytic throughout the honest Gibbs half-plane. -/
theorem analyticOnNhd_riemannZeta_zetaHalfPlane :
    AnalyticOnNhd ℂ riemannZeta zetaHalfPlane := by
  intro s hs
  have hdiff : DifferentiableOn ℂ riemannZeta zetaHalfPlane := by
    intro z hz
    have hz1 : z ≠ 1 := by
      simpa using zetaHalfPlane_subset_compl_one hz
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  exact hdiff.analyticAt (isOpen_zetaHalfPlane.mem_nhds hs)

/-- First derivative of the negative logarithmic derivative, written as an explicit
quotient. -/
noncomputable def firstResponse (s : ℂ) : ℂ :=
  -((deriv (deriv riemannZeta) s * riemannZeta s -
      deriv riemannZeta s * deriv riemannZeta s) /
    riemannZeta s ^ 2)

/-- Pointwise first-derivative quotient formula on `Re s > 1`. -/
theorem deriv_negZetaLogDeriv_eq_firstResponse
    {s : ℂ} (hs : 1 < s.re) :
    deriv negZetaLogDeriv s = firstResponse s := by
  have hsset : s ∈ zetaHalfPlane := hs
  have h0 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane s hsset).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (deriv riemannZeta) (deriv (deriv riemannZeta) s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv s hsset).differentiableAt.hasDerivAt
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_right_half_plane hs
  have hbase := h1.div h0 hne
  have hneg : HasDerivAt negZetaLogDeriv
      (-((deriv (deriv riemannZeta) s * riemannZeta s -
          deriv riemannZeta s * deriv riemannZeta s) / riemannZeta s ^ 2)) s := by
    convert hbase.neg using 1 <;> simp [negZetaLogDeriv] <;> field_simp [hne] <;> ring
  simpa [firstResponse] using hneg.deriv

/-- The first derivative identity holds on the whole open half-plane. -/
theorem deriv_negZetaLogDeriv_eqOn_firstResponse :
    zetaHalfPlane.EqOn (deriv negZetaLogDeriv) firstResponse := by
  intro s hs
  exact deriv_negZetaLogDeriv_eq_firstResponse hs

/-- Differentiating the explicit first response produces exactly the standard third
logarithmic cumulant expression. -/
theorem deriv_firstResponse_eq_thirdLogResponse
    {s : ℂ} (hs : 1 < s.re) :
    deriv firstResponse s =
      -(deriv (deriv (deriv riemannZeta)) s / riemannZeta s) +
      3 * (deriv (deriv riemannZeta) s / riemannZeta s) *
        (deriv riemannZeta s / riemannZeta s) -
      2 * (deriv riemannZeta s / riemannZeta s) ^ 3 := by
  have hsset : s ∈ zetaHalfPlane := hs
  have h0 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane s hsset).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (deriv riemannZeta) (deriv (deriv riemannZeta) s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv s hsset).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (deriv (deriv riemannZeta))
      (deriv (deriv (deriv riemannZeta)) s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv.deriv s hsset).differentiableAt.hasDerivAt
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_right_half_plane hs
  have hnum' : HasDerivAt
      (fun z => deriv (deriv riemannZeta) z * riemannZeta z -
        deriv riemannZeta z * deriv riemannZeta z)
      ((deriv (deriv (deriv riemannZeta)) s * riemannZeta s +
          deriv (deriv riemannZeta) s * deriv riemannZeta s) -
        (deriv (deriv riemannZeta) s * deriv riemannZeta s +
          deriv riemannZeta s * deriv (deriv riemannZeta) s)) s := by
    exact (h2.mul h0).sub (h1.mul h1)
  have hden : HasDerivAt (fun z => riemannZeta z ^ 2)
      (2 * riemannZeta s * deriv riemannZeta s) s := by
    convert h0.pow 2 using 1 <;> ring
  have hbase := hnum'.div hden (pow_ne_zero 2 hne)
  have hneg : HasDerivAt firstResponse
      (-((((deriv (deriv (deriv riemannZeta)) s * riemannZeta s +
              deriv (deriv riemannZeta) s * deriv riemannZeta s) -
            (deriv (deriv riemannZeta) s * deriv riemannZeta s +
              deriv riemannZeta s * deriv (deriv riemannZeta) s)) *
            riemannZeta s ^ 2 -
          (deriv (deriv riemannZeta) s * riemannZeta s -
            deriv riemannZeta s * deriv riemannZeta s) *
            (2 * riemannZeta s * deriv riemannZeta s)) /
        (riemannZeta s ^ 2) ^ 2)) s := by
    convert hbase.neg using 1 <;> simp [firstResponse] <;> field_simp [hne] <;> ring
  have hd := hneg.deriv
  rw [hd]
  field_simp [hne]
  ring

/-- The second derivative of `-zeta'/zeta` is the standard third-cumulant response. -/
theorem iteratedDeriv_two_negZetaLogDeriv_eq_zetaThirdCumulantResponse
    {β : ℝ} (hβ : 1 < β) :
    iteratedDeriv 2 negZetaLogDeriv (β : ℂ) =
      zetaThirdCumulantResponse β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hsset : (β : ℂ) ∈ zetaHalfPlane := hs
  have heq :=
    (deriv_negZetaLogDeriv_eqOn_firstResponse.iteratedDeriv_of_isOpen
      isOpen_zetaHalfPlane 1) hsset
  have hiter :
      iteratedDeriv 2 negZetaLogDeriv (β : ℂ) =
        deriv firstResponse (β : ℂ) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ']
    simpa [iteratedDeriv_one] using heq
  rw [hiter, deriv_firstResponse_eq_thirdLogResponse hs]
  unfold zetaThirdCumulantResponse
  simp [iteratedDeriv_succ', iteratedDeriv_one]

/-- The actual complex zeta third-cumulant response has strictly positive real part. -/
theorem zetaThirdCumulantResponse_re_pos
    {β : ℝ} (hβ : 1 < β) :
    0 < (zetaThirdCumulantResponse β).re := by
  rw [← iteratedDeriv_two_negZetaLogDeriv_eq_zetaThirdCumulantResponse hβ]
  exact iteratedDeriv_two_negZetaLogDeriv_re_pos hβ

/-- **Strict zeta-Gibbs third cumulant positivity** on the honest Gibbs domain. -/
theorem logEnergyThirdCumulant_pos
    {β : ℝ} (hβ : 1 < β) :
    0 < logEnergyThirdCumulant β := by
  have h := zetaThirdCumulantResponse_re_pos hβ
  rw [zetaThirdCumulantResponse_eq_ofReal_logEnergyThirdCumulant hβ] at h
  simpa using h

end GppZetaThirdCumulantStrict

#print axioms GppZetaThirdCumulantStrict.iteratedDeriv_two_negZetaLogDeriv_eq_zetaThirdCumulantResponse
#print axioms GppZetaThirdCumulantStrict.zetaThirdCumulantResponse_re_pos
#print axioms GppZetaThirdCumulantStrict.logEnergyThirdCumulant_pos
