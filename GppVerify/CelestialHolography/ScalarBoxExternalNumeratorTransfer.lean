import GppVerify.CelestialHolography.ScalarBoxStructuredPhysicalConvergence
import Mathlib.Tactic

/-!
# External numerator transfer for the regulated scalar box

An external cut numerator that is independent of the regulator and of the cut
integration variable multiplies the already-controlled scalar remainder without
changing its regulator order.  This is the exact algebraic step used to transfer
the scalar-box regulator theorem to four-dimensional cut-constructible Yang--Mills
numerators.
-/

namespace GppScalarBoxExternalNumeratorTransfer

open Filter
open scoped Topology
open GppScalarBoxStructuredPhysicalConvergence
open GppScalarBoxPhysicalCoreBound
open GppScalarBoxSpecialFunctionRemainder

/-- Multiplying both the regulated object and its asymptotic/core approximation by a
fixed external numerator multiplies the error bound by the numerator's absolute value. -/
theorem abs_external_mul_remainder_le
    (N J J0 B : ℝ) (hB : |J - J0| ≤ B) :
    |N * J - N * J0| ≤ |N| * B := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left hB (abs_nonneg N)

/-- A fixed external numerator preserves convergence of a regulator remainder to zero. -/
theorem tendsto_external_mul_remainder_zero
    (N : ℝ) {J J0 : ℝ → ℝ}
    (h : Tendsto (fun m : ℝ => J m - J0 m) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun m : ℝ => N * J m - N * J0 m) (𝓝[>] 0) (𝓝 0) := by
  have hmul := tendsto_const_nhds.mul h
  simpa [mul_sub] using hmul

/-- In the physical four-point continuation `s=-S`, `u=-U`, masslessness fixes
`t=S+U`; consequently the stripped MHV Yang--Mills box numerator `s*t` is
`-S*(S+U)`. -/
theorem ym_mhv_st_numerator (S U : ℝ) :
    (-S) * (S + U) = -(S * (S + U)) := by
  ring

/-- For positive channel variables, the absolute value of the MHV numerator is
exactly `S*(S+U)`. -/
theorem abs_ym_mhv_numerator
    {S U : ℝ} (hS : 0 < S) (hU : 0 < U) :
    |-(S * (S + U))| = S * (S + U) := by
  rw [abs_neg, abs_of_pos]
  positivity

/-- The scalar remainder estimate transfers verbatim to the stripped MHV
Yang--Mills numerator.  This theorem is deliberately only the external-numerator
step: state sums, global amplitude phases, and D-dimensional rational terms are
not asserted here. -/
theorem abs_ym_mhv_remainder_le
    {S U J J0 B : ℝ} (hS : 0 < S) (hU : 0 < U)
    (hB : |J - J0| ≤ B) :
    |(-(S * (S + U))) * J - (-(S * (S + U))) * J0| ≤
      S * (S + U) * B := by
  have h := abs_external_mul_remainder_le (-(S * (S + U))) J J0 B hB
  rw [abs_ym_mhv_numerator hS hU] at h
  exact h

/-- **Final four-dimensional stripped-MHV regulator transfer.**  Under the same
physical chamber and exact kinematic relations as the certified scalar-box theorem,
the structured regulated scalar core multiplied by the fixed MHV numerator
`-S*(S+U)` converges to the same numerator times the scalar asymptotic core.

This is deliberately a four-dimensional cut-constructible statement.  It does not
assert the global amplitude phase, internal state sums, D-dimensional rational terms,
or the gravity four-denominator KLT reduction. -/
theorem tendsto_physical_structured_ym_mhv_remainder_zero
    {S U : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    {R κ q a t ρ η B x δ : ℝ → ℝ}
    (hmS4 : ∀ᶠ m in 𝓝[>] 0, m ≤ S / 4)
    (hmU16 : ∀ᶠ m in 𝓝[>] 0, m ≤ U / 16)
    (hRlo : ∀ᶠ m in 𝓝[>] 0, 8 / 9 ≤ R m)
    (hRhi : ∀ᶠ m in 𝓝[>] 0, R m ≤ 1)
    (hκlo : ∀ᶠ m in 𝓝[>] 0, 1 ≤ κ m)
    (hκhi : ∀ᶠ m in 𝓝[>] 0, κ m ≤ 9 / 8)
    (hxlo : ∀ᶠ m in 𝓝[>] 0, 15 / 16 ≤ x m)
    (hxhi : ∀ᶠ m in 𝓝[>] 0, x m ≤ 1)
    (hq : ∀ᶠ m in 𝓝[>] 0, q m = (1 - R m) / (1 + R m))
    (ha : ∀ᶠ m in 𝓝[>] 0, a m = (κ m - 1) / (κ m + 1))
    (hRsq : ∀ᶠ m in 𝓝[>] 0, (R m) ^ 2 = U / (U + 4 * m))
    (hκsq : ∀ᶠ m in 𝓝[>] 0,
      (κ m) ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hρ : ∀ᶠ m in 𝓝[>] 0, ρ m = m / U)
    (hη : ∀ᶠ m in 𝓝[>] 0, η m = m / S)
    (hδ : ∀ᶠ m in 𝓝[>] 0, δ m = 4 * m / U)
    (ht : ∀ᶠ m in 𝓝[>] 0, t m = η m * B m)
    (hBdef : ∀ᶠ m in 𝓝[>] 0,
      B m = 2 * (1 + κ m) /
        ((1 + δ m) * (1 + x m) * (1 + R m) * (1 - η m)))
    (hκsqScale : ∀ᶠ m in 𝓝[>] 0,
      (κ m) ^ 2 = 1 + δ m * (1 - η m))
    (hxsq : ∀ᶠ m in 𝓝[>] 0,
      (x m) ^ 2 = 1 - δ m * η m / (1 + δ m))
    (hRsqScale : ∀ᶠ m in 𝓝[>] 0,
      (R m) ^ 2 = 1 / (1 + δ m)) :
    Tendsto
      (fun m : ℝ =>
        (-(S * (S + U))) *
            (structuredScalarBoxCore (a m) (t m)
                (specialRemainder (a m) (q m) (t m)) / κ m) -
          (-(S * (S + U))) * scalarBoxD0 S U m)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_external_mul_remainder_zero (-(S * (S + U)))
  exact tendsto_physical_structured_scalarBox_core_zero
    hS hU hmS4 hmU16 hRlo hRhi hκlo hκhi hxlo hxhi hq ha hRsq hκsq
    hρ hη hδ ht hBdef hκsqScale hxsq hRsqScale

end GppScalarBoxExternalNumeratorTransfer

#print axioms GppScalarBoxExternalNumeratorTransfer.abs_external_mul_remainder_le
#print axioms GppScalarBoxExternalNumeratorTransfer.tendsto_external_mul_remainder_zero
#print axioms GppScalarBoxExternalNumeratorTransfer.ym_mhv_st_numerator
#print axioms GppScalarBoxExternalNumeratorTransfer.abs_ym_mhv_numerator
#print axioms GppScalarBoxExternalNumeratorTransfer.abs_ym_mhv_remainder_le
#print axioms GppScalarBoxExternalNumeratorTransfer.tendsto_physical_structured_ym_mhv_remainder_zero
