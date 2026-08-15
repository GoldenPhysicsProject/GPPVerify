import GppVerify.RiemannHypothesis.WeilSupportLadder
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Thread HT — the prime–Archimedean heat trace: elementary layer

From `arithmetic_principal_series_RH_program34.tex` (the BPY prime–Archimedean spectral
program). That paper reformulates RH as an exact **zero-independent** statement: with

  `m_*(u) = (1/(2√(1+u))) · (ξ'/ξ)(1/2 + √(1+u))`,
  `𝒲 = ν_∞ − ν_p` the completed prime–Archimedean boundary distribution,
  `𝒦(t) = (4πt)^{-1/2} ⟨𝒲, e^{−(·)²/(4t)}⟩`,

subordination of the massive resolvent gives `m_*(u) = ∫₀^∞ e^{−(1+u)t} 𝒦(t) dt`, and the
paper's heat-trace criterion states

  **RH ⟺ `𝒦` is completely monotone on `(0,∞)`**,

with `𝒦(t) = Σ_{γ>0} m_γ e^{−γ²t}` under RH.

This file formalizes the **elementary, kernel-checkable layer** of that chain. What is
proved here is exactly the arithmetic and Laplace-transform bookkeeping; the two genuinely
hard inputs are named and NOT claimed (see the boundary section at the end).

## Contents

* `CompletelyMonotone` — the definition (absent from Mathlib at the pinned commit
  `c44e0c8`; checked, there is no Bernstein/Hausdorff–Widder theory upstream).
* `completelyMonotone_exp_neg` — `t ↦ e^{−at}` is completely monotone for `a ≥ 0`. This is
  the single-mode building block of the paper's `Σ_{γ>0} m_γ e^{−γ²t}`.
* `resolvent_laplace` — `∫₀^∞ e^{−ct} dt = 1/c` for `c > 0`, and its shifted form
  `laplace_resolvent_shift`: `∫₀^^∞ e^{−(1+u)t} e^{−γ²t} dt = 1/(u + 1 + γ²)`. This is the
  displayed step in the paper's proof of the heat-trace criterion, where uniqueness of the
  Laplace transform converts the Hadamard partial-fraction sum into the heat expansion.
* `subordination_at_zero` — the `x = 0` case of the paper's boxed subordination formula,
  `∫₀^∞ e^{−r²t} (4πt)^{-1/2} dt = 1/(2r)`.
* `primeSide_heatGaussian` — **the bridge to Thread L**: the paper's arithmetic sum
  `Σ_{n≥2} Λ(n) n^{-1/2} e^{−(log n)²/(4t)}` is exactly one half of
  `GppWeilLadder.primeSide` evaluated at the heat Gaussian, because that test function is
  even. So the new paper's prime side *is* the Weil support ladder's prime side, and
  inherits its truncation lemmas verbatim.

## What is deliberately NOT claimed

1. **The general subordination formula** `e^{−rx}/(2r) = ∫₀^∞ e^{−(1+u)t} (4πt)^{-1/2}
   e^{−x²/(4t)} dt` for `x > 0`. Only `x = 0` is proved here. The general case is the
   classical `∫₀^∞ e^{−at−b/t} t^{-1/2} dt = √(π/a) e^{−2√(ab)}` (a `K_{1/2}` Bessel
   evaluation), which is **not in Mathlib at the pin** — verified by direct search of
   `Mathlib/Analysis/SpecialFunctions/`. Proving it needs the Glasser-type substitution
   `u = √(at) − √(b/t)`; that is a genuine thread of its own, not a corollary.
2. **Bernstein's theorem** (completely monotone ⟺ Laplace transform of a positive measure).
   Absent from Mathlib at the pin. The paper's `(2) ⇒ (3) ⇒ (1)` direction rests on it.
3. **The heat-trace criterion itself.** Nothing here proves, or assumes, RH. The forward
   direction additionally needs the centered Hadamard product for `ξ` and a zero-counting
   argument — the same missing infrastructure recorded repo-wide, and the reason the RH
   thread is blocked regardless of reformulation.

The honest summary: this file kernel-checks that *if* the heat expansion
`𝒦(t) = Σ m_γ e^{−γ²t}` holds with `m_γ ≥ 0`, then each mode is completely monotone and the
Laplace bookkeeping in the paper's proof is exact; and it identifies the paper's prime side
with the repo's existing Weil ladder. It does not prove the criterion.
-/

namespace GppHeatTrace

open MeasureTheory Set ArithmeticFunction

/-! ### Complete monotonicity -/

/-- `f` is **completely monotone** on `(0,∞)`: every derivative alternates in sign,
`(−1)ⁿ f⁽ⁿ⁾ ≥ 0`. Not present in Mathlib at the pinned commit. -/
def CompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f t

/-- The single heat mode `t ↦ e^{−at}` is completely monotone for `a ≥ 0`.

In the paper's notation this is one term of `𝒦(t) = Σ_{γ>0} m_γ e^{−γ²t}`, with
`a = γ² ≥ 0` — so complete monotonicity of `𝒦` under RH is, modewise, this lemma. -/
theorem completelyMonotone_exp_neg {a : ℝ} (ha : 0 ≤ a) :
    CompletelyMonotone (fun t => Real.exp (-a * t)) := by
  intro n t _
  -- NOTE (pin lesson): `iteratedDeriv_exp_const_mul` lives in the ROOT namespace at
  -- `c44e0c8` (ExpDeriv.lean:366, declared under `open Real in` after `end Real`),
  -- NOT in `Real`. Verified by reading the pinned source.
  have hd := congrFun (iteratedDeriv_exp_const_mul n (-a)) t
  rw [hd]
  have hsign : (-1 : ℝ) ^ n * ((-a) ^ n * Real.exp (-a * t))
      = a ^ n * Real.exp (-a * t) := by
    rw [← mul_assoc, ← mul_pow]
    ring_nf
  rw [hsign]
  positivity

/-! ### Laplace bookkeeping

The paper's proof of the heat-trace criterion turns the Hadamard partial-fraction sum
`Σ_γ m_γ/(u + 1 + γ²)` into the heat expansion by uniqueness of the Laplace transform,
using the elementary identity below termwise. -/

/-- `∫₀^∞ e^{−ct} dt = 1/c` for `c > 0`. -/
theorem resolvent_laplace {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi (0:ℝ), Real.exp (-(c * t)) = 1 / c := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := c) one_pos hc
  simp only [sub_self, Real.rpow_zero, one_mul, Real.Gamma_one, mul_one,
    Real.rpow_one] at h
  exact h

/-- The paper's displayed termwise step:
`∫₀^∞ e^{−(1+u)t} e^{−γ²t} dt = 1/(u + 1 + γ²)`. -/
theorem laplace_resolvent_shift {u γ : ℝ} (hu : 0 < u) :
    ∫ t : ℝ in Ioi (0:ℝ), Real.exp (-((1 + u) * t)) * Real.exp (-(γ ^ 2 * t))
      = 1 / (u + 1 + γ ^ 2) := by
  have hc : 0 < 1 + u + γ ^ 2 := by positivity
  have hint : ∀ t : ℝ, Real.exp (-((1 + u) * t)) * Real.exp (-(γ ^ 2 * t))
      = Real.exp (-((1 + u + γ ^ 2) * t)) := by
    intro t
    rw [← Real.exp_add]
    ring_nf
  simp only [hint]
  rw [resolvent_laplace hc]
  ring_nf

/-! ### Subordination at the origin

The paper's boxed subordination formula, at `x = 0`. -/

/-- `∫₀^∞ e^{−r²t} · (4πt)^{−1/2} dt = 1/(2r)` for `r > 0`.

This is the `x = 0` case of the paper's boxed identity
`e^{−rx}/(2r) = ∫₀^∞ e^{−r²t} (4πt)^{−1/2} e^{−x²/(4t)} dt`; at `x = 0` both the Gaussian
factor and `e^{−rx}` are `1`. The general `x > 0` case is NOT proved (see the file header). -/
theorem subordination_at_zero {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Ioi (0:ℝ), Real.exp (-(r ^ 2 * t)) / Real.sqrt (4 * Real.pi * t)
      = 1 / (2 * r) := by
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  -- Rewrite the integrand as a constant times the Gamma integrand at `a = 1/2`.
  have hpt : ∀ t ∈ Ioi (0:ℝ),
      Real.exp (-(r ^ 2 * t)) / Real.sqrt (4 * Real.pi * t)
        = (1 / (2 * Real.sqrt Real.pi)) * (t ^ ((1:ℝ) / 2 - 1) * Real.exp (-(r ^ 2 * t))) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have hs4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have h4 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
      rw [show (4:ℝ) * Real.pi * t = 4 * (Real.pi * t) by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_mul Real.pi_pos.le, hs4]
      ring
    have hts : Real.sqrt t = t ^ ((1:ℝ) / 2) := Real.sqrt_eq_rpow t
    have hexp : t ^ ((1:ℝ) / 2 - 1) = (t ^ ((1:ℝ) / 2))⁻¹ := by
      rw [show (1:ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg ht0.le]
    have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
    have htp : t ^ ((1:ℝ) / 2) ≠ 0 := by positivity
    rw [h4, hts, hexp]
    -- `field_simp` closes this outright; a trailing `ring` would error "no goals"
    -- (recorded lesson, docs/FORMALIZATION_PLAN.md Thread P).
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [integral_const_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ) < 1/2) hr2]
  rw [Real.Gamma_one_half_eq]
  -- `(1/r²)^(1/2) = 1/r`
  have hinv : ((1:ℝ) / r ^ 2) ^ ((1:ℝ) / 2) = 1 / r := by
    rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, Real.sqrt_sq hr.le, one_div]
  rw [hinv]
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp
  ring

/-! ### The bridge to Thread L: the paper's prime side is the Weil ladder's prime side -/

/-- The heat Gaussian `x ↦ e^{−x²/(4t)}`, the test function the paper pairs `𝒲` against. -/
noncomputable def heatGaussian (t : ℝ) : ℝ → ℝ := fun x => Real.exp (-x ^ 2 / (4 * t))

/-- The heat Gaussian is even. -/
theorem heatGaussian_even (t : ℝ) (x : ℝ) : heatGaussian t (-x) = heatGaussian t x := by
  simp only [heatGaussian, neg_pow, even_two.neg_pow]

/-- **Thread L bridge.** The paper's arithmetic sum
`Σ_{n} Λ(n) n^{−1/2} e^{−(log n)²/(4t)}` is exactly half of the repo's existing
`GppWeilLadder.primeSide` at the heat Gaussian — the two halves `f(log n)` and `f(−log n)`
coincide because the Gaussian is even.

Consequence: the whole support-ladder toolkit of `WeilSupportLadder.lean`
(`primeSide_term_eq_zero`, `primeSide_eq_truncation`,
`primeSide_eq_zero_of_support_lt_log_two`) applies verbatim to the heat trace's prime side.
The two threads are the same object. -/
theorem primeSide_heatGaussian (t : ℝ) :
    GppWeilLadder.primeSide (heatGaussian t)
      = 2 * ∑' n : ℕ, (Λ n / Real.sqrt n) * Real.exp (-(Real.log n) ^ 2 / (4 * t)) := by
  rw [GppWeilLadder.primeSide, ← tsum_mul_left]
  congr 1
  funext n
  rw [heatGaussian_even]
  simp only [heatGaussian]
  ring

/-! ### The Archimedean Laplace transform: two elementary sub-identities

The paper's "Exact Archimedean Laplace transform" theorem (§, immediately preceding the
heat-trace section) proves, for `r > 1`, `⟨ν_∞, e^{−r(·)}⟩ = A_∞(r)`, where `A_∞` is built
from a digamma difference **plus** two elementary exponential integrals. The digamma piece
needs Mathlib's digamma/polygamma function, which is **confirmed absent from Mathlib
entirely at this pin** (searched — no `digamma`, `polyGamma`, or `deriv_Gamma`-based
integral representation anywhere in the tree). That piece is out of reach without building
digamma from scratch, a separate and much larger undertaking.

The two purely elementary sub-identities, however, need nothing beyond what
`resolvent_laplace` already supplies, applied twice and subtracted. They are proved here
as standalone facts, not wired into `A_∞` (which is not defined in this file — only its
two elementary building blocks are). -/

/-- First elementary sub-identity of the Archimedean Laplace transform: for `r > −1/2`,
`∫₀^∞ (e^{−rx} − e^{−x})·e^{−x/2} dx = 1/(r+1/2) − 2/3`. -/
theorem archimedeanLaplace_aux_one {r : ℝ} (hr : -(1/2 : ℝ) < r) :
    ∫ x : ℝ in Ioi (0:ℝ), (Real.exp (-(r * x)) - Real.exp (-x)) * Real.exp (-(x / 2))
      = 1 / (r + 1/2) - 2/3 := by
  have hc1 : (0:ℝ) < r + 1/2 := by linarith
  have hc2 : (0:ℝ) < (3:ℝ)/2 := by norm_num
  have hpt : ∀ x : ℝ, (Real.exp (-(r * x)) - Real.exp (-x)) * Real.exp (-(x / 2))
      = Real.exp (-((r + 1/2) * x)) - Real.exp (-((3:ℝ)/2 * x)) := by
    intro x
    rw [sub_mul, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x)]
  rw [integral_sub (by simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hc1)
      (by simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hc2)]
  rw [resolvent_laplace hc1, resolvent_laplace hc2]
  norm_num

/-- Second elementary sub-identity of the Archimedean Laplace transform: for `r > 1/2`,
`∫₀^∞ (e^{−rx} − e^{−x})·e^{x/2} dx = 1/(r−1/2) − 2`. -/
theorem archimedeanLaplace_aux_two {r : ℝ} (hr : (1/2 : ℝ) < r) :
    ∫ x : ℝ in Ioi (0:ℝ), (Real.exp (-(r * x)) - Real.exp (-x)) * Real.exp (x / 2)
      = 1 / (r - 1/2) - 2 := by
  have hc1 : (0:ℝ) < r - 1/2 := by linarith
  have hc2 : (0:ℝ) < (1:ℝ)/2 := by norm_num
  have hpt : ∀ x : ℝ, (Real.exp (-(r * x)) - Real.exp (-x)) * Real.exp (x / 2)
      = Real.exp (-((r - 1/2) * x)) - Real.exp (-((1:ℝ)/2 * x)) := by
    intro x
    rw [sub_mul, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x)]
  rw [integral_sub (by simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hc1)
      (by simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hc2)]
  rw [resolvent_laplace hc1, resolvent_laplace hc2]
  norm_num

end GppHeatTrace
