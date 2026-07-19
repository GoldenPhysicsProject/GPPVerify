import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds

/-!
# Li's criterion: the entire Riemann Xi function and its first coefficient

Task #75 (long pending): a second equivalence for RH. Li's criterion (Li 1997) states
that RH holds iff `λₙ ≥ 0` for every `n ≥ 1`, where
`λₙ := (1/(n-1)!) · dⁿ/dsⁿ [sⁿ⁻¹ log ξ(s)] |_{s=1}`
and `ξ` is the *entire* completed zeta function. The full equivalence needs the Hadamard
factorization of `ξ(s)` (not in Mathlib; previously assessed this session as a genuine
multi-week undertaking, not attempted here).

## What this file does

Mathlib's `completedRiemannZeta` is `Λ(s) = π^{-s/2}Γ(s/2)ζ(s)`, meromorphic with simple
poles at `s = 0, 1`. The entire Riemann Xi function is `ξ(s) := (1/2)s(s-1)Λ(s)`, whose
`s(s-1)` prefactor exactly cancels both poles. Mathlib already provides
`completedRiemannZeta₀ := Λ(s) + 1/s + 1/(1-s)`, entire (`differentiable_completedZeta₀`),
and — the key fact this file leans on — its exact value at `s = 1`:
`completedRiemannZeta₀ 1 = (γ - log(4π))/2 + 1` (`completedRiemannZeta₀_one`, already in
Mathlib via `Mathlib.NumberTheory.Harmonic.ZetaAsymp`).

Algebraically, `s(s-1)·Λ(s) = s(s-1)·completedRiemannZeta₀(s) + 1` exactly (the `1/s` and
`1/(1-s)` correction terms in `completedRiemannZeta₀`'s definition exactly cancel the
`s(s-1)` factor's zeros against Λ's poles), so
`ξ(s) = (1/2)·(s(s-1)·completedRiemannZeta₀(s) + 1)`.

The point of this file is `deriv_riemannXi_one`: computing `ξ'(1)` via the product rule,
the *double zero* of `s(s-1)` at `s = 1` annihilates every term involving the unknown
derivative `completedRiemannZeta₀'(1)`, leaving `ξ'(1) = (1/2)·completedRiemannZeta₀(1)`
— a clean closed form requiring no new deep analysis, only this elementary
product-rule cancellation. Combined with `ξ(1) = 1/2` and Mathlib's
`completedRiemannZeta₀_one`, this gives Li's λ₁ in exact closed form
(`li_lambda_one`): `ξ'(1)/ξ(1) = (γ - log(4π))/2 + 1`, matching the classical numerical
value `λ₁ ≈ 0.0230957` (Li 1997).

## Unconditional positivity of λ₁ (New)

`eulerMascheroniConstant_gt_log_four_pi_sub_two` proves `γ > log(4π) - 2`, i.e.
`li_lambda_one_pos : λ₁ > 0`, unconditionally. Mathlib's own bound
`Real.one_half_lt_eulerMascheroniConstant` (`γ > 1/2`) is not tight enough on its own
(`0.5 < 0.531...`), so this uses `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant` at
`n = 63` (so `n + 1 = 64 = 2⁶`, giving an *exact* multiple of `log 2` for the subtracted
term) together with the tangent-line bound `log π ≤ π / e` (from
`Real.log_le_sub_one_of_pos` applied at `π/e`, using `log e = 1`) and Mathlib's decimal
bounds `Real.pi_lt_d4`, `Real.exp_one_gt_d9`, `Real.log_two_lt_d9` for the resulting
numerics, closed by comparing against the *exact* rational value of `harmonic 63`. What
remains open: the full Li ⟺ RH equivalence for all `n` (needs Hadamard factorization of
`ξ`, not in Mathlib) is the separately-assessed, much larger undertaking.
-/

namespace GppRH

open Complex

/-- The entire completed Riemann Xi function `ξ(s) = (1/2)s(s-1)Λ(s)`, expressed via
Mathlib's already-entire `completedRiemannZeta₀` to avoid pole bookkeeping:
`s(s-1)Λ(s) = s(s-1)·completedRiemannZeta₀(s) + 1` exactly. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- `ξ` is entire. -/
theorem riemannXi_entire : Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1 |>.const_mul _

/-- `ξ(1) = 1/2`: the `s(s-1)` prefactor vanishes at `s = 1`, leaving only the `+1`. -/
theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

/-- The derivative of `s ↦ s(s-1)` at `s = 1` is `1`. -/
theorem hasDerivAt_mul_sub_one_at_one :
    HasDerivAt (fun s : ℂ => s * (s - 1)) 1 1 := by
  have h := (hasDerivAt_id' (1 : ℂ)).mul ((hasDerivAt_id' (1 : ℂ)).sub_const 1)
  norm_num at h
  exact h

/-- **Li's first coefficient, exact closed form.** The double zero of `s(s-1)` at `s = 1`
annihilates every term of the product rule involving the unknown derivative
`completedRiemannZeta₀'(1)`, leaving only `completedRiemannZeta₀`'s *value* at `1`. -/
theorem deriv_riemannXi_one :
    deriv riemannXi 1 = (1 / 2) * completedRiemannZeta₀ 1 := by
  have hG : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ 1) 1 :=
    differentiable_completedZeta₀.differentiableAt.hasDerivAt
  have hFG := hasDerivAt_mul_sub_one_at_one.mul hG
  have hFG' : HasDerivAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s)
      (completedRiemannZeta₀ 1) 1 := by
    convert hFG using 1
    simp
  have hXi : HasDerivAt riemannXi ((1 / 2) * completedRiemannZeta₀ 1) 1 :=
    (hFG'.add_const 1).const_mul ((1 : ℂ) / 2)
  exact hXi.deriv

/-- **Li's λ₁, exact real closed form.** `ξ'(1)/ξ(1) = (γ - log(4π))/2 + 1`, matching
Li's classical value `λ₁ ≈ 0.0230957`. -/
theorem li_lambda_one :
    deriv riemannXi 1 / riemannXi 1 =
      (Real.eulerMascheroniConstant - Complex.log (4 * Real.pi)) / 2 + 1 := by
  rw [deriv_riemannXi_one, riemannXi_one, completedRiemannZeta₀_one]
  ring

/-- **Unconditional numeric inequality: `γ > log(4π) - 2`.** The tangent-line bound
`log π ≤ π / e` (from `Real.log_le_sub_one_of_pos` at `π/e`, using `log e = 1`) combined
with `Real.pi_lt_d4` and `Real.exp_one_gt_d9` gives `log π < 1.156`; combined with
`Real.log_two_lt_d9` this gives `log(4π) < 2.5423` and `log 64 < 4.1588830848`. Comparing
`harmonic 63 - log 64` against `log(4π) - 2` via these bounds and the exact rational
value of `harmonic 63` gives `eulerMascheroniSeq 63 > log(4π) - 2`, and
`Real.eulerMascheroniSeq_lt_eulerMascheroniConstant` transports this to `γ`. -/
theorem eulerMascheroniConstant_gt_log_four_pi_sub_two :
    Real.log (4 * Real.pi) - 2 < Real.eulerMascheroniConstant := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hlogpi : Real.log Real.pi ≤ Real.pi / Real.exp 1 := by
    have hxpos : (0 : ℝ) < Real.pi / Real.exp 1 := div_pos Real.pi_pos he
    have h1 := Real.log_le_sub_one_of_pos hxpos
    rw [Real.log_div (ne_of_gt Real.pi_pos) (ne_of_gt he), Real.log_exp] at h1
    linarith
  have hpilt : Real.pi < 1.156 * Real.exp 1 := by
    linarith [Real.pi_lt_d4, Real.exp_one_gt_d9]
  have hlogpi' : Real.log Real.pi < 1.156 := by
    have hdiv : Real.pi / Real.exp 1 < 1.156 := (div_lt_iff₀ he).mpr hpilt
    linarith [hlogpi, hdiv]
  have hlog4 : Real.log 4 < 1.3862943616 := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [h4]; linarith [Real.log_two_lt_d9]
  have hlog4pi : Real.log (4 * Real.pi) < 2.5423 := by
    rw [Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
    linarith [hlog4, hlogpi']
  have hlog64 : Real.log 64 < 4.1588830848 := by
    have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [h64]; linarith [Real.log_two_lt_d9]
  have hharm' : (4.71 : ℝ) ≤ (harmonic 63 : ℝ) := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    norm_num
  have hseq : Real.log (4 * Real.pi) - 2 < Real.eulerMascheroniSeq 63 := by
    have h641 : ((63 : ℕ) : ℝ) + 1 = 64 := by norm_num
    unfold Real.eulerMascheroniSeq
    rw [h641]
    linarith [hharm', hlog64, hlog4pi]
  exact hseq.trans (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 63)

/-- **Li's λ₁ is unconditionally positive.** -/
theorem li_lambda_one_pos :
    0 < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 := by
  linarith [eulerMascheroniConstant_gt_log_four_pi_sub_two]

end GppRH
