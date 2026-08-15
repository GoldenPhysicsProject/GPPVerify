import GppVerify.RiemannHypothesis.WeilSupportLadder
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.ExpDecay

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
* `subordination_general` — **the general-`x` subordination formula, in full**:
  `∫₀^∞ t^{-1/2} e^{−at−b/t} dt = √(π/a) e^{−2√(ab)}` for `a,b > 0` — a genuine `K_{1/2}`
  Bessel evaluation, proved **without any Bessel-function machinery** (none exists in
  Mathlib at the pin). Route, fully elementary: substitute `t = (√b/√a)w²`, reducing to an
  auxiliary integral `auxK(c) := ∫₀^∞ e^{−c(w²+w⁻²)}dw`; the `w ↦ 1/w` symmetry of that
  integrand (via `MeasureTheory.integral_comp_rpow_Ioi`, `p = -1`) doubles it to
  `2·auxK(c) = ∫₀^∞(1+w⁻²)e^{−c(w²+w⁻²)}dw`; the substitution `p = w − 1/w` — a genuine
  bijection `(0,∞) → ℝ`, whose derivative is exactly the weight `1+w⁻²`, proved via
  `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` with surjectivity onto `ℝ`
  closed by `IsPreconnected.intermediate_value_Ioi`/`_Iio` — turns this into a two-sided
  Gaussian integral, closed by `Real.integral_gaussian`. Every lemma named and verified
  against the pinned source before use, per standing discipline.
* `primeSide_heatGaussian` — **the bridge to Thread L**: the paper's arithmetic sum
  `Σ_{n≥2} Λ(n) n^{-1/2} e^{−(log n)²/(4t)}` is exactly one half of
  `GppWeilLadder.primeSide` evaluated at the heat Gaussian, because that test function is
  even. So the new paper's prime side *is* the Weil support ladder's prime side, and
  inherits its truncation lemmas verbatim.

## What is deliberately NOT claimed

1. **Bernstein's theorem** (completely monotone ⟺ Laplace transform of a positive measure).
   Absent from Mathlib at the pin. The paper's `(2) ⇒ (3) ⇒ (1)` direction rests on it.
2. **The heat-trace criterion itself.** Nothing here proves, or assumes, RH. The forward
   direction additionally needs the centered Hadamard product for `ξ` and a zero-counting
   argument — the same missing infrastructure recorded repo-wide, and the reason the RH
   thread is blocked regardless of reformulation.

The honest summary: this file kernel-checks that *if* the heat expansion
`𝒦(t) = Σ m_γ e^{−γ²t}` holds with `m_γ ≥ 0`, then each mode is completely monotone and the
Laplace bookkeeping in the paper's proof is exact; and it identifies the paper's prime side
with the repo's existing Weil ladder. It does not prove the criterion.
-/

namespace GppHeatTrace

open MeasureTheory Set ArithmeticFunction Filter Topology

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
factor and `e^{−rx}` are `1`. The general `x > 0` case is proved separately, in full, as
`subordination_general` below (stated in the equivalent `a,b` form via `a=r²`, `b=x²/4`). -/
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

/-! ### The general-x subordination formula, in full -/

noncomputable def subInvolution (w : ℝ) : ℝ := w - w⁻¹

theorem subInvolution_continuousOn : ContinuousOn subInvolution (Ioi (0:ℝ)) := by
  unfold subInvolution
  apply ContinuousOn.sub continuousOn_id
  apply continuousOn_inv₀.mono
  intro x hx
  exact ne_of_gt hx

theorem subInvolution_one : subInvolution 1 = 0 := by unfold subInvolution; norm_num

theorem subInvolution_tendsto_atTop : Tendsto subInvolution atTop atTop := by
  unfold subInvolution
  have h1 : Tendsto (fun w : ℝ => w⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 : ∀ᶠ w : ℝ in atTop, w - 1 ≤ w - w⁻¹ := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with w hw
    have : w⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; exact hw
    linarith
  have h3 : Tendsto (fun w : ℝ => w - 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) tendsto_id
  exact tendsto_atTop_mono' atTop h2 h3

theorem subInvolution_tendsto_atBot : Tendsto subInvolution (𝓝[>] (0:ℝ)) atBot := by
  unfold subInvolution
  have h1 : Tendsto (fun w : ℝ => w⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun w : ℝ => -w⁻¹) (𝓝[>] (0:ℝ)) atBot := tendsto_neg_atTop_atBot.comp h1
  have h4 : ∀ᶠ w : ℝ in 𝓝[>] (0:ℝ), w - w⁻¹ ≤ 1 - w⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT_of_mem (left_mem_Ico.mpr one_pos)] with w hw1
    linarith [hw1.2.le]
  have h5 : Tendsto (fun w : ℝ => 1 - w⁻¹) (𝓝[>] (0:ℝ)) atBot := by
    have : (fun w : ℝ => 1 - w⁻¹) = (fun w : ℝ => -w⁻¹ + 1) := by funext w; ring
    rw [this]
    exact tendsto_atBot_add_const_right (𝓝[>] (0:ℝ)) 1 h2
  exact tendsto_atBot_mono' (𝓝[>] (0:ℝ)) h4 h5

theorem subInvolution_image_eq_univ : subInvolution '' (Ioi (0:ℝ)) = Set.univ := by
  have hconn : IsPreconnected (Ioi (0:ℝ)) := isPreconnected_Ioi
  have hIoi1_sub : Ioi (1:ℝ) ⊆ Ioi (0:ℝ) :=
    fun x hx => Set.mem_Ioi.mpr (lt_trans one_pos (Set.mem_Ioi.mp hx))
  have hsub_pos : (𝓝[>] (1:ℝ)) ≤ 𝓟 (Ioi (0:ℝ)) :=
    le_trans (le_principal_iff.mpr self_mem_nhdsWithin) (principal_mono.mpr hIoi1_sub)
  have h0_sub : (𝓝[>] (0:ℝ)) ≤ 𝓟 (Ioi (0:ℝ)) := le_principal_iff.mpr self_mem_nhdsWithin
  have h1atTop : (atTop : Filter ℝ) ≤ 𝓟 (Ioi (0:ℝ)) :=
    le_principal_iff.mpr (eventually_gt_atTop (0:ℝ))
  have hcont1 : Tendsto subInvolution (𝓝[>] (1:ℝ)) (𝓝 (0:ℝ)) := by
    have hcw : ContinuousWithinAt subInvolution (Ioi (0:ℝ)) 1 := subInvolution_continuousOn 1 (by norm_num)
    have hmono : (𝓝[>] (1:ℝ)) ≤ 𝓝[Ioi (0:ℝ)] (1:ℝ) := nhdsWithin_mono 1 hIoi1_sub
    rw [← subInvolution_one]
    exact hcw.mono_left hmono
  have hpos : Ioi (0:ℝ) ⊆ subInvolution '' (Ioi (0:ℝ)) :=
    hconn.intermediate_value_Ioi hsub_pos h1atTop subInvolution_continuousOn hcont1 subInvolution_tendsto_atTop
  have hneg : Iio (0:ℝ) ⊆ subInvolution '' (Ioi (0:ℝ)) :=
    hconn.intermediate_value_Iio h0_sub hsub_pos subInvolution_continuousOn subInvolution_tendsto_atBot hcont1
  have hzero : (0:ℝ) ∈ subInvolution '' (Ioi (0:ℝ)) := ⟨1, by norm_num, subInvolution_one⟩
  ext y
  simp only [mem_univ, iff_true]
  rcases lt_trichotomy y 0 with h | h | h
  · exact hneg h
  · rw [h]; exact hzero
  · exact hpos h

theorem subInvolution_hasDerivAt {w : ℝ} (hw : 0 < w) : HasDerivAt subInvolution (1 + w⁻¹^2) w := by
  unfold subInvolution
  have h1 : HasDerivAt (fun y : ℝ => y) 1 w := hasDerivAt_id w
  have h2 : HasDerivAt (fun y : ℝ => y⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw.ne'
  have := h1.sub h2
  convert this using 1
  field_simp

theorem subInvolution_strictMonoOn : StrictMonoOn subInvolution (Ioi (0:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) subInvolution_continuousOn
  intro x hx
  rw [interior_Ioi] at hx
  rw [(subInvolution_hasDerivAt hx).deriv]
  positivity

theorem subInvolution_injOn : InjOn subInvolution (Ioi (0:ℝ)) := subInvolution_strictMonoOn.injOn

/-- The key change of variables: for any `c`, integrating `exp(-c(p²+2))` over all of `ℝ`
equals integrating `(1+w⁻²)·exp(-c(w²+w⁻²))` over `w ∈ Ioi 0`. -/
theorem subInvolution_subst (c : ℝ) :
    (∫ p : ℝ, Real.exp (-(c * (p ^ 2 + 2))))
      = ∫ w : ℝ in Ioi (0:ℝ), (1 + w⁻¹ ^ 2) * Real.exp (-(c * (w ^ 2 + w⁻¹ ^ 2))) := by
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivWithinAt subInvolution (1 + x⁻¹ ^ 2) (Ioi (0:ℝ)) x :=
    fun x hx => (subInvolution_hasDerivAt hx).hasDerivWithinAt
  have hsubst := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv subInvolution_injOn
    (fun p => Real.exp (-(c * (p ^ 2 + 2))))
  rw [subInvolution_image_eq_univ] at hsubst
  rw [← setIntegral_univ, hsubst]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  simp only [smul_eq_mul]
  have hpos : (0:ℝ) ≤ 1 + w⁻¹ ^ 2 := by positivity
  rw [abs_of_nonneg hpos]
  have hfw : subInvolution w ^ 2 + 2 = w ^ 2 + w⁻¹ ^ 2 := by
    unfold subInvolution
    have hne : w ≠ 0 := ne_of_gt hw
    field_simp
    ring
  rw [hfw]

/-- Definition of the auxiliary integral `auxK(c)`. -/
noncomputable def auxK (c : ℝ) : ℝ := ∫ w : ℝ in Ioi (0:ℝ), Real.exp (-(c * (w ^ 2 + w⁻¹ ^ 2)))

/-- `x ↦ exp(-c(x²+x⁻²))` is continuous on `Ioi 0`. -/
theorem auxK_integrand_continuousOn (c : ℝ) :
    ContinuousOn (fun x : ℝ => Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2)))) (Ioi (0:ℝ)) := by
  apply Real.continuous_exp.comp_continuousOn
  apply ContinuousOn.neg
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.add (continuousOn_pow 2)
  apply ContinuousOn.pow
  intro x hx
  exact (continuousAt_inv₀ (ne_of_gt hx)).continuousWithinAt

/-- The weight function `fun x => (1:ℝ)` bounds `exp(-c(x²+x⁻²))` pointwise (the exponent
is `≤ 0`), so integrability on any finite-measure subset of `Ioi 0` follows from domination
by a constant. -/
theorem auxK_integrand_le_one (c : ℝ) (hc : 0 ≤ c) (x : ℝ) :
    Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))) ≤ 1 := by
  rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have : 0 ≤ x ^ 2 + x⁻¹ ^ 2 := by positivity
  nlinarith

/-- `x^n · exp(-c(x²+x⁻²))` is integrable on `(0,∞)` for `c > 0`. Split at `x=1`: bounded
(hence integrable, finite measure) on `(0,1]`; dominated by `exp(-cx)` on `[1,∞)` since
`x²≥x` there. -/
theorem integrableOn_auxK_integrand {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2)))) (Ioi (0:ℝ)) := by
  have hset : (Ioi (0:ℝ)) = Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ) := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx; rcases le_or_lt x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  rw [hset]
  apply IntegrableOn.union
  · -- bounded (by 1) on a finite-measure set
    apply Integrable.mono' (g := fun _ : ℝ => (1:ℝ))
    · exact integrableOn_const.mpr (Or.inr (by simp [Real.volume_Ioc]))
    · exact ((auxK_integrand_continuousOn c).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact auxK_integrand_le_one c hc.le x
  · -- dominated by exp(-c*x) on Ioi 1
    apply integrable_of_isBigO_exp_neg hc
    · exact (auxK_integrand_continuousOn c).mono (fun x (hx : x ∈ Ici (1:ℝ)) =>
        Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos (Set.mem_Ici.mp hx)))
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
      have hsq : x ≤ x ^ 2 := by nlinarith
      have hinv2 : (0:ℝ) ≤ x⁻¹ ^ 2 := by positivity
      have hexp_le : Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))) ≤ Real.exp (-c * x) := by
        rw [neg_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      simp only [Real.norm_eq_abs, one_mul]
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact hexp_le

/-- `x ↦ t · exp(-c·t)` is bounded for `t ≥ 0`, `c > 0` — a standard exponential-beats-any-
polynomial estimate, via `1 + c·t/2 ≤ exp(c·t/2)` (`Real.add_one_le_exp`). -/
theorem mul_exp_neg_bound {c : ℝ} (hc : 0 < c) (t : ℝ) (ht : 0 ≤ t) :
    t * Real.exp (-(c * t)) ≤ 2 / c := by
  have hbound : 1 + c * t / 2 ≤ Real.exp (c * t / 2) := by
    have := Real.add_one_le_exp (c * t / 2); linarith
  have hct2 : 0 ≤ c * t / 2 := by positivity
  have hstep : c * t / 2 ≤ Real.exp (c * t / 2) := by linarith
  have ht2 : t ≤ (2 / c) * Real.exp (c * t / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  have hsplit : Real.exp (-(c * t)) = Real.exp (c * t / 2) * Real.exp (-(c * t) - c * t / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hne : Real.exp (-(c * t) - c * t / 2) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    linarith
  calc t * Real.exp (-(c * t))
      ≤ (2 / c) * Real.exp (c * t / 2) * Real.exp (-(c * t)) := by
        apply mul_le_mul_of_nonneg_right ht2 (Real.exp_pos _).le
    _ = (2 / c) * (Real.exp (c * t / 2) * Real.exp (-(c * t))) := by ring
    _ ≤ (2 / c) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc Real.exp (c * t / 2) * Real.exp (-(c * t))
            = Real.exp (c * t / 2 - c * t) := by rw [← Real.exp_add]; ring_nf
          _ ≤ Real.exp 0 := by apply Real.exp_le_exp.mpr; linarith
          _ = 1 := Real.exp_zero
    _ = 2 / c := by ring

/-- `x⁻² · exp(-c(x²+x⁻²))` is integrable on `(0,∞)`. Same split as `integrableOn_auxK_integrand`: on
`(0,1]`, `x⁻²·exp(-c·x⁻²) ≤ 2/c` by `mul_exp_neg_bound` (with `t=x⁻²`, using `E(x)≤exp(-cx⁻²)`
since the `x²` factor in the exponent only helps); on `[1,∞)`, `x⁻²≤1` folds into the
`exp(-c(x²+x⁻²)) ≤ exp(-cx)` bound already proved. -/
theorem integrableOn_invsq_mul_auxK_integrand {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x⁻¹ ^ 2 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2)))) (Ioi (0:ℝ)) := by
  have hset : (Ioi (0:ℝ)) = Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ) := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx; rcases le_or_lt x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  rw [hset]
  apply IntegrableOn.union
  · apply Integrable.mono' (g := fun _ : ℝ => (2 / c : ℝ))
    · exact integrableOn_const.mpr (Or.inr (by simp [Real.volume_Ioc]))
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
      apply ContinuousOn.mul
      · exact (continuousOn_id.inv₀ (fun x hx => ne_of_gt hx.1)).pow 2
      · exact (auxK_integrand_continuousOn c).mono Ioc_subset_Ioi_self
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hx0 : (0:ℝ) < x := hx.1
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hle : Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))) ≤ Real.exp (-(c * x⁻¹ ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have : (0:ℝ) ≤ c * x ^ 2 := by positivity
        nlinarith
      calc x⁻¹ ^ 2 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2)))
          ≤ x⁻¹ ^ 2 * Real.exp (-(c * x⁻¹ ^ 2)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ 2 / c := mul_exp_neg_bound hc (x⁻¹ ^ 2) (by positivity)
  · apply Integrable.mono' (g := fun x : ℝ => Real.exp (-(c * x)))
    · simpa only [neg_mul] using exp_neg_integrableOn_Ioi (1:ℝ) hc
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      apply ContinuousOn.mul
      · exact (continuousOn_id.inv₀
          (fun x (hx : x ∈ Ioi (1:ℝ)) => ne_of_gt (lt_trans one_pos hx))).pow 2
      · exact (auxK_integrand_continuousOn c).mono (fun x (hx : x ∈ Ioi (1:ℝ)) =>
          Set.mem_Ioi.mpr (lt_trans one_pos (Set.mem_Ioi.mp hx)))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) < x := hx
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx1
      rw [Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < x⁻¹ ^ 2 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))))]
      have hinv_le : x⁻¹ ^ 2 ≤ 1 := by
        rw [inv_pow]
        apply inv_le_one_of_one_le₀
        nlinarith
      have hsq : x ≤ x ^ 2 := by nlinarith
      have hexp_le : Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))) ≤ Real.exp (-(c * x)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc x⁻¹ ^ 2 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2)))
          ≤ 1 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))) :=
            mul_le_mul_of_nonneg_right hinv_le (Real.exp_pos _).le
        _ = Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))) := one_mul _
        _ ≤ Real.exp (-(c * x)) := hexp_le

theorem two_auxK_eq {c : ℝ} (hc : 0 < c) :
    2 * auxK c = ∫ w : ℝ in Ioi (0:ℝ), (1 + w⁻¹ ^ 2) * Real.exp (-(c * (w ^ 2 + w⁻¹ ^ 2))) := by
  have hsymm := integral_comp_rpow_Ioi
    (g := fun y : ℝ => Real.exp (-(c * (y ^ 2 + y⁻¹ ^ 2)))) (p := (-1:ℝ)) (by norm_num)
  have hpt : ∀ x ∈ Ioi (0:ℝ),
      (|(-1:ℝ)| * x ^ ((-1:ℝ) - 1)) • Real.exp (-(c * ((x ^ (-1:ℝ)) ^ 2 + (x ^ (-1:ℝ))⁻¹ ^ 2)))
        = x⁻¹ ^ 2 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))) := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hxinv : x ^ (-1:ℝ) = x⁻¹ := Real.rpow_neg_one x
    rw [hxinv]
    have halg : (x⁻¹) ^ 2 + (x⁻¹)⁻¹ ^ 2 = x ^ 2 + x⁻¹ ^ 2 := by
      rw [inv_inv]; ring
    rw [halg, abs_neg, abs_one, one_mul]
    have hexp : x ^ ((-1:ℝ) - 1) = x⁻¹ ^ 2 := by
      rw [show (-1:ℝ) - 1 = (-2:ℝ) by norm_num, Real.rpow_neg hx.le,
        show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hexp]
    simp [smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt] at hsymm
  have hKflip : (∫ x : ℝ in Ioi (0:ℝ), x⁻¹ ^ 2 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2)))) = auxK c := hsymm
  -- Replace only the SECOND `auxK c` summand (the two are syntactically identical, so plain
  -- `rw` cannot target one without the other) via `congrArg` applied to the equation itself.
  have hstep : auxK c + auxK c
      = (∫ w : ℝ in Ioi (0:ℝ), Real.exp (-(c * (w ^ 2 + w⁻¹ ^ 2))))
        + ∫ x : ℝ in Ioi (0:ℝ), x⁻¹ ^ 2 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2))) :=
    congrArg (fun t => auxK c + t) hKflip.symm
  have hcombine : (∫ w : ℝ in Ioi (0:ℝ), Real.exp (-(c * (w ^ 2 + w⁻¹ ^ 2))))
      + ∫ x : ℝ in Ioi (0:ℝ), x⁻¹ ^ 2 * Real.exp (-(c * (x ^ 2 + x⁻¹ ^ 2)))
      = ∫ w : ℝ in Ioi (0:ℝ), (1 + w⁻¹ ^ 2) * Real.exp (-(c * (w ^ 2 + w⁻¹ ^ 2))) := by
    rw [← integral_add (integrableOn_auxK_integrand hc) (integrableOn_invsq_mul_auxK_integrand hc)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  rw [show (2:ℝ) * auxK c = auxK c + auxK c by ring, hstep, hcombine]

/-- `∫_ℝ exp(-c(p²+2))dp = exp(-2c)·√(π/c)`, via `Real.integral_gaussian` and factoring
out the constant `exp(-2c)`. -/
theorem gaussian_shifted_aux (c : ℝ) :
    (∫ p : ℝ, Real.exp (-(c * (p ^ 2 + 2)))) = Real.exp (-(2 * c)) * Real.sqrt (Real.pi / c) := by
  have hpt : ∀ p : ℝ, Real.exp (-(c * (p ^ 2 + 2))) = Real.exp (-(2 * c)) * Real.exp (-(c * p ^ 2)) := by
    intro p; rw [← Real.exp_add]; ring_nf
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  have heq : (fun p : ℝ => Real.exp (-(c * p ^ 2))) = (fun p : ℝ => Real.exp (-c * p ^ 2)) := by
    funext p; rw [neg_mul]
  rw [heq, integral_gaussian]

/-- **`auxK(c) = (1/2)√(π/c)·e^{-2c}` for `c > 0`.** The mathematical heart of the general-`x`
subordination formula, fully closed. -/
theorem auxK_eq {c : ℝ} (hc : 0 < c) :
    auxK c = (1 / 2) * Real.sqrt (Real.pi / c) * Real.exp (-(2 * c)) := by
  have h1 := two_auxK_eq hc
  rw [← subInvolution_subst c, gaussian_shifted_aux c] at h1
  linarith [h1]

/-! ### Step 1: connecting `auxK` back to the actual subordination target -/

/-- The scaling substitution `subScale(w) = k·w²`, `k > 0`. -/
noncomputable def subScale (k w : ℝ) : ℝ := k * w ^ 2

theorem subScale_continuousOn (k : ℝ) : ContinuousOn (subScale k) (Ioi (0:ℝ)) :=
  (continuous_const.mul (continuous_pow 2)).continuousOn

theorem subScale_hasDerivAt (k w : ℝ) : HasDerivAt (subScale k) (2 * k * w) w := by
  unfold subScale
  have h := (hasDerivAt_pow 2 w).const_mul k
  convert h using 1
  push_cast
  ring

theorem subScale_strictMonoOn {k : ℝ} (hk : 0 < k) : StrictMonoOn (subScale k) (Ioi (0:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (subScale_continuousOn k)
  intro x hx
  rw [interior_Ioi] at hx
  have hx' : (0:ℝ) < x := hx
  rw [(subScale_hasDerivAt k x).deriv]
  positivity

theorem subScale_injOn {k : ℝ} (hk : 0 < k) : InjOn (subScale k) (Ioi (0:ℝ)) := (subScale_strictMonoOn hk).injOn

theorem subScale_image_eq {k : ℝ} (hk : 0 < k) : subScale k '' (Ioi (0:ℝ)) = Ioi (0:ℝ) := by
  have hconn : IsPreconnected (Ioi (0:ℝ)) := isPreconnected_Ioi
  have h0_sub : (𝓝[>] (0:ℝ)) ≤ 𝓟 (Ioi (0:ℝ)) := le_principal_iff.mpr self_mem_nhdsWithin
  have h0_val : Tendsto (subScale k) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have : Tendsto (subScale k) (𝓝 (0:ℝ)) (𝓝 (subScale k 0)) := by
      apply Continuous.tendsto
      exact continuous_const.mul (continuous_pow 2)
    simp only [subScale, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hgtop : Tendsto (subScale k) atTop atTop := by
    unfold subScale
    exact Tendsto.const_mul_atTop hk (tendsto_pow_atTop (by norm_num))
  have h1atTop : (atTop : Filter ℝ) ≤ 𝓟 (Ioi (0:ℝ)) :=
    le_principal_iff.mpr (eventually_gt_atTop (0:ℝ))
  have hpos : Ioi (0:ℝ) ⊆ subScale k '' (Ioi (0:ℝ)) :=
    hconn.intermediate_value_Ioi h0_sub h1atTop (subScale_continuousOn k) h0_val hgtop
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨w, hw, hgw⟩ := hy
    rw [Set.mem_Ioi] at hw ⊢
    rw [← hgw]; unfold subScale; positivity
  · exact hpos

/-- The substitution step: `∫ t in Ioi 0, h t = ∫ w in Ioi 0, 2kw • h(kw²)`. -/
theorem subScale_subst {k : ℝ} (hk : 0 < k) (h : ℝ → ℝ) :
    (∫ t : ℝ in Ioi (0:ℝ), h t) = ∫ w : ℝ in Ioi (0:ℝ), (2 * k * w) * h (k * w ^ 2) := by
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivWithinAt (subScale k) (2 * k * x) (Ioi (0:ℝ)) x :=
    fun x _ => (subScale_hasDerivAt k x).hasDerivWithinAt
  have hsubst := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv (subScale_injOn hk) h
  rw [subScale_image_eq hk] at hsubst
  rw [hsubst]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx' : (0:ℝ) < x := hx
  have hnn : (0:ℝ) ≤ 2 * k * x := by positivity
  simp only [abs_of_nonneg hnn, smul_eq_mul]
  unfold subScale
  rfl

/-- **The general-`x` subordination formula**, `I(a,b) = ∫₀^∞ t^{-1/2}e^{-at-b/t}dt =
√(π/a)·e^{-2√(ab)}`, for `a, b > 0`. -/
theorem subordination_general {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in Ioi (0:ℝ), t ^ (-(1:ℝ)/2) * Real.exp (-(a * t) - b / t))
      = Real.sqrt (Real.pi / a) * Real.exp (-(2 * Real.sqrt (a * b))) := by
  set k : ℝ := Real.sqrt b / Real.sqrt a with hkdef
  have hk : 0 < k := by rw [hkdef]; positivity
  have hsa : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.mpr ha
  have hsb : Real.sqrt b ≠ 0 := Real.sqrt_ne_zero'.mpr hb
  have ha' : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hb' : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have hsab : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha.le b
  have hak : a * k = Real.sqrt (a * b) := by
    have step : a * k = (Real.sqrt a * Real.sqrt a) * (Real.sqrt b / Real.sqrt a) := by
      rw [ha', hkdef]
    rw [step, hsab,
      show Real.sqrt a * Real.sqrt a * (Real.sqrt b / Real.sqrt a)
        = Real.sqrt a * Real.sqrt b * (Real.sqrt a / Real.sqrt a) from by ring,
      div_self hsa, mul_one]
  have hbk : b / k = Real.sqrt (a * b) := by
    have step : b / k = (Real.sqrt b * Real.sqrt b) / (Real.sqrt b / Real.sqrt a) := by
      rw [hb', hkdef]
    rw [step, hsab, div_div_eq_mul_div,
      show Real.sqrt b * Real.sqrt b * Real.sqrt a / Real.sqrt b
        = Real.sqrt a * Real.sqrt b * (Real.sqrt b / Real.sqrt b) from by ring,
      div_self hsb, mul_one]
  -- Sever the `let`-transparency of `k` (from `set`) so later `field_simp`/`ring` calls
  -- cannot silently unfold it back to `√b/√a` mid-proof — a real pitfall hit this session.
  clear_value k
  have hstep := subScale_subst hk (fun t => t ^ (-(1:ℝ)/2) * Real.exp (-(a * t) - b / t))
  rw [hstep]
  have hpt : ∀ w : ℝ, w ∈ Ioi (0:ℝ) → (2 * k * w) * ((k * w ^ 2) ^ (-(1:ℝ)/2) *
      Real.exp (-(a * (k * w ^ 2)) - b / (k * w ^ 2)))
      = (2 * Real.sqrt k) * Real.exp (-(Real.sqrt (a * b) * (w ^ 2 + w⁻¹ ^ 2))) := by
    intro w hw
    have hw0 : (0:ℝ) < w := hw
    have hrpow : (k * w ^ 2 : ℝ) ^ (-(1:ℝ)/2) = (Real.sqrt (k * w ^ 2))⁻¹ := by
      rw [show (-(1:ℝ)/2) = -(1/2 : ℝ) by ring, Real.rpow_neg (by positivity),
        ← Real.sqrt_eq_rpow]
    have hsqkw2 : Real.sqrt (k * w ^ 2) = Real.sqrt k * w := by
      rw [Real.sqrt_mul hk.le, Real.sqrt_sq hw0.le]
    have hexp_eq : -(a * (k * w ^ 2)) - b / (k * w ^ 2)
        = -(Real.sqrt (a * b) * (w ^ 2 + w⁻¹ ^ 2)) := by
      have h1 : a * (k * w ^ 2) = Real.sqrt (a * b) * w ^ 2 := by
        rw [← hak]; ring
      have h2 : b / (k * w ^ 2) = Real.sqrt (a * b) * w⁻¹ ^ 2 := by
        rw [← hbk, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
      rw [h1, h2]; ring
    rw [hrpow, hsqkw2, hexp_eq]
    have hsk : Real.sqrt k ≠ 0 := by positivity
    have hw' : w ≠ 0 := ne_of_gt hw0
    have factor : (2 * k * w) * (Real.sqrt k * w)⁻¹ = 2 * Real.sqrt k := by
      have hkdiv : k / Real.sqrt k = Real.sqrt k := by
        rw [div_eq_iff hsk]; exact (Real.mul_self_sqrt hk.le).symm
      rw [mul_inv, show (2:ℝ) * k * w * ((Real.sqrt k)⁻¹ * w⁻¹)
          = 2 * (k / Real.sqrt k) * (w * w⁻¹) from by rw [div_eq_mul_inv]; ring, hkdiv,
        mul_inv_cancel₀ hw', mul_one]
    calc (2 * k * w) * ((Real.sqrt k * w)⁻¹ * Real.exp (-(Real.sqrt (a * b) * (w ^ 2 + w⁻¹ ^ 2))))
        = ((2 * k * w) * (Real.sqrt k * w)⁻¹) * Real.exp (-(Real.sqrt (a * b) * (w ^ 2 + w⁻¹ ^ 2))) := by
          ring
      _ = (2 * Real.sqrt k) * Real.exp (-(Real.sqrt (a * b) * (w ^ 2 + w⁻¹ ^ 2))) := by rw [factor]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hKfold : (∫ w : ℝ in Ioi (0:ℝ), Real.exp (-(Real.sqrt (a * b) * (w ^ 2 + w⁻¹ ^ 2))))
      = auxK (Real.sqrt (a * b)) := rfl
  rw [hKfold, auxK_eq (show (0:ℝ) < Real.sqrt (a * b) by positivity)]
  have hkval : k = Real.sqrt (a * b) / a := by
    have step : (Real.sqrt a * Real.sqrt b) / (Real.sqrt a * Real.sqrt a) = k := by
      rw [hkdef, show Real.sqrt a * Real.sqrt b / (Real.sqrt a * Real.sqrt a)
          = Real.sqrt b / Real.sqrt a * (Real.sqrt a / Real.sqrt a) from by ring,
        div_self hsa, mul_one]
    rw [← step, ha', hsab]
  have hprod : Real.sqrt (Real.sqrt (a * b) / a) * Real.sqrt (Real.pi / Real.sqrt (a * b))
      = Real.sqrt (Real.pi / a) := by
    have hsab_pos : (0:ℝ) < Real.sqrt (a * b) := by positivity
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    rw [div_mul_div_comm, mul_comm a (Real.sqrt (a * b)), mul_div_mul_left _ _ hsab_pos.ne']
  have hfinal : (2 * Real.sqrt k) * ((1:ℝ) / 2 * Real.sqrt (Real.pi / Real.sqrt (a * b)))
      = Real.sqrt (Real.pi / a) := by
    rw [hkval]
    rw [show (2:ℝ) * Real.sqrt (Real.sqrt (a * b) / a)
        * (1 / 2 * Real.sqrt (Real.pi / Real.sqrt (a * b)))
        = Real.sqrt (Real.sqrt (a * b) / a) * Real.sqrt (Real.pi / Real.sqrt (a * b)) from by
      ring]
    exact hprod
  rw [← mul_assoc, hfinal]

end GppHeatTrace
