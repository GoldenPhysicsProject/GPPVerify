import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

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

## What this does NOT do

The *unconditional positivity* `λ₁ > 0` — equivalent to the numerical inequality
`γ > log(4π) - 2 ≈ 0.531` — is NOT proved here. Mathlib's own bound
`Real.one_half_lt_eulerMascheroniConstant` (`γ > 1/2`) is not tight enough on its own
(0.5 < 0.531); a genuine proof needs either a sharper rigorous lower bound on `γ` (e.g.
via `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant` at a large enough concrete `n`,
combined with numerical control of `log n`) or a sharper upper bound on `log(4π)`. Left
as an explicit next step, not glossed over. The full Li ⟺ RH equivalence (all `n`, via
Hadamard factorization) remains the separately-assessed, much larger open undertaking.
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
Li's classical value `λ₁ ≈ 0.0230957`. The unconditional positivity of this value —
equivalent to `γ > log(4π) - 2` — is left as an explicit next step (see the module
docstring): Mathlib's `Real.one_half_lt_eulerMascheroniConstant` alone is not tight
enough (`0.5 < 0.531...`). -/
theorem li_lambda_one :
    deriv riemannXi 1 / riemannXi 1 =
      (Real.eulerMascheroniConstant - Complex.log (4 * Real.pi)) / 2 + 1 := by
  rw [deriv_riemannXi_one, riemannXi_one, completedRiemannZeta₀_one]
  ring

end GppRH
