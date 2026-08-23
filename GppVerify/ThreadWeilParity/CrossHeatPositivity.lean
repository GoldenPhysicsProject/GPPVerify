import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Cross-heat positivity implies resolvent positivity: the Laplace-transform core

`formalization_queue` item `68566b83` ("Cross-heat positivity implies resolvent positivity
and even ground ordering"), Weil-Parity thread. The item's own framing:

  "For Hermitian A and vectors eta,e0, if k(t)=Re(eta^* exp(-t A) e0)>0 for all t>=0, then
  for every real z<lambda_min(A), Re(eta^*(A-zI)^(-1)e0)=integral_0^infty exp(t z) k(t) dt
  >0. ... Formalize the matrix exponential/Laplace-resolvent implication separately if
  Mathlib supports it; otherwise prove finite spectral-sum version first."

## What this file proves

The genuinely substantive real-analysis content, once the Laplace-transform identity
`Re(η^*(A-zI)^{-1}e0) = ∫₀^∞ e^{tz} k(t) dt` is taken as given (that identity itself is
the "matrix exponential/Laplace-resolvent" part the queue item explicitly separates out,
not attempted here): an integral of an everywhere-positive integrable function over `[0,∞)`
is strictly positive. Via `MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae`, reduced
to showing the support of the (everywhere positive, hence everywhere nonzero) integrand
intersected with `[0,∞)` has positive measure — which it does, since it equals all of
`[0,∞)`, a set of infinite (in particular positive) Lebesgue measure.

## What this file does NOT do

Does **not** define Hermitian matrices, the matrix exponential `exp(-tA)`, or the resolvent
`(A-zI)^{-1}`, and does not prove the Laplace-transform identity connecting them to `k` and
the integral above — that identity (or its "finite spectral-sum version" fallback the queue
item names) is separate, substantial, and not attempted here. No axiom, no sorry.
-/

namespace GppWeilParity

open MeasureTheory Set

/-- **Laplace-transform positivity core.** If `k : ℝ → ℝ` is strictly positive everywhere
on `[0,∞)` and `t ↦ exp(tz) * k t` is integrable there, its integral over `[0,∞)` is
strictly positive. Once `k(t) = Re(η^* exp(-tA) e0)` and the integral is identified with
`Re(η^*(A-zI)^{-1}e0)` (the queue item's separate Laplace-resolvent identity), this is
exactly "cross-heat positivity forces cross-resolvent positivity." -/
theorem laplace_integral_pos_of_pos_on_Ici {k : ℝ → ℝ}
    (hkpos : ∀ t ∈ Ici (0 : ℝ), 0 < k t) {z : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (t * z) * k t) (Ici (0 : ℝ))) :
    0 < ∫ t in Ici (0 : ℝ), Real.exp (t * z) * k t := by
  have hfpos : ∀ t ∈ Ici (0 : ℝ), 0 < Real.exp (t * z) * k t := fun t ht =>
    mul_pos (Real.exp_pos _) (hkpos t ht)
  have hnonneg : 0 ≤ᵐ[(volume).restrict (Ici (0 : ℝ))] fun t => Real.exp (t * z) * k t :=
    ae_restrict_of_forall_mem measurableSet_Ici (fun t ht => (hfpos t ht).le)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsupp : (Function.support fun t => Real.exp (t * z) * k t) ∩ Ici (0 : ℝ) = Ici (0 : ℝ) :=
    Set.inter_eq_right.mpr (fun t ht => (hfpos t ht).ne')
  rw [hsupp, Real.volume_Ici]
  exact ENNReal.zero_lt_top

end GppWeilParity
