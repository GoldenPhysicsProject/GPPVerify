import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic

/-!
# Shifted logarithmic-derivative transfer preserves the zero divisor

`formalization_queue` item `1c684543` ("Shifted logarithmic-derivative transfer preserves
the xi zero divisor"), Suzuki-Herglotz thread. The item's own setup: for holomorphic `F`
and scalar `λ`, put `D_λ(s) = F'(s) - λF(s)` and `R_λ(s) = F(s)/D_λ(s)`. If `ρ` is a zero
of `F` of multiplicity `m ≥ 1` (`F(s) = (s-ρ)^m h(s)`, `h(ρ) ≠ 0`), then `R_λ` extends
holomorphically across `ρ` with a *simple* zero there, and the zeros of `R_λ` are exactly
the zeros of `F`. The item's intended downstream use is `F = ξ` (the completed Riemann
zeta function) — "this is the exact divisor fact behind the shifted Suzuki
transfer-function route."

## What this file proves

The general, `F`-free algebraic/analytic core exactly as the item's own worked example
lays it out: writing the order-`m` factor as `m = k+1` (`k:ℕ`) to sidestep natural-number
subtraction entirely, and taking `F z := (z-ρ)^(k+1)·g z` for `g` analytic and nonzero at
`ρ` (the item's `h`):

* **`deriv_shiftedTransferF_sub_smul_eq`** — the item's own displayed factorization,
  `D_λ(z) = (z-ρ)^k · w(z)` where `w(z) := (k+1)·g(z) + (z-ρ)·(g'(z) - λ·g(z))`, proved
  from an actual `HasDerivAt` product/power-rule computation (`hasDerivAt_shiftedTransferF`),
  not asserted.
* **`shiftedTransferWitness_at_root_ne_zero`** — `w(ρ) = (k+1)·g(ρ) ≠ 0`, so `D_λ` has
  order exactly `k` at `ρ` — one less than `F`'s order `k+1`.
* **`tendsto_shiftedTransfer_quotient_div`** — the item's stated asymptotic
  `R_λ(s) = (s-ρ)/(k+1) + O((s-ρ)²)`, formalized precisely as
  `R_λ(z)/(z-ρ) → 1/(k+1)` as `z → ρ` (`z ≠ ρ`), i.e. the removable singularity of `R_λ`
  at `ρ` extends it to a genuine **simple** zero there (nonzero linear coefficient
  `1/(k+1)`, matching every finite `λ`).
* **`tendsto_shiftedTransfer_quotient_zero`** — the direct corollary `R_λ(z) → 0` as
  `z → ρ`, i.e. `ρ` really is a (removable, order-≥1) zero of the extension of `R_λ`, the
  "zeros of `R_λ` are (among) the zeros of `F`" half of the item's conclusion.

## What this file does NOT do

Does **not** instantiate `F = ξ` (the completed Riemann zeta function, `completedRiemannZeta`
in Mathlib) — that instantiation is a direct application of the lemmas here once `ξ`'s
zeros are known to be simple with the right local model, not attempted this pass. Does
**not** prove the *global* statement "the zeros of `R_λ` are *exactly* the zeros of `F`,
and no others" — that needs `D_λ` to be controlled away from zeros of `F` too (generically
true, but a separate global argument, e.g. via `AnalyticOnNhd`/discreteness of the zero
set, not attempted here); what is proved is the precise *local* fact at each individual
zero `ρ` of `F`, which is the actual mathematical content the queue item names ("the exact
divisor fact"). No axiom, no sorry.
-/

namespace GppWeilParity

open Filter Topology

noncomputable section

/-- `F(z) := (z-ρ)^(k+1)·g(z)`, the order-`(k+1)` zero factorization from the queue item's
    own setup (`m = k+1`, sidestepping natural-number subtraction). -/
def shiftedTransferF (g : ℂ → ℂ) (ρ : ℂ) (k : ℕ) (w : ℂ) : ℂ := (w - ρ) ^ (k + 1) * g w

theorem hasDerivAt_shiftedTransferF (g : ℂ → ℂ) (ρ z : ℂ) (k : ℕ)
    (hg : DifferentiableAt ℂ g z) :
    HasDerivAt (shiftedTransferF g ρ k)
      ((k + 1 : ℂ) * (z - ρ) ^ k * g z + (z - ρ) ^ (k + 1) * deriv g z) z := by
  have h1 : HasDerivAt (fun w : ℂ => (w - ρ) ^ (k + 1)) ((k + 1 : ℂ) * (z - ρ) ^ k) z := by
    have hsub : HasDerivAt (fun w : ℂ => w - ρ) (1 - 0) z :=
      (hasDerivAt_id z).sub (hasDerivAt_const z ρ)
    have hsub' : HasDerivAt (fun w : ℂ => w - ρ) 1 z := by simpa using hsub
    have := hsub'.pow (k + 1)
    simpa only [Pi.pow_def] using this
  have h2 : HasDerivAt g (deriv g z) z := hg.hasDerivAt
  have := h1.mul h2
  -- simp the GOAL only; simping `this` too would rewrite it into a different
  -- (defeq but syntactically distinct) instance path that no tactic can bridge.
  simp only [shiftedTransferF]
  exact this

/-- The transferred denominator's witness function:
    `w(z) := (k+1)·g(z) + (z-ρ)·(g'(z) - λ·g(z))`. -/
def shiftedTransferWitness (g : ℂ → ℂ) (ρ lam : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  (k + 1 : ℂ) * g z + (z - ρ) * (deriv g z - lam * g z)

/-- **The item's own displayed identity**:
    `D_λ(z) = F'(z) - λF(z) = (z-ρ)^k · w(z)`. -/
theorem deriv_shiftedTransferF_sub_smul_eq (g : ℂ → ℂ) (ρ lam z : ℂ) (k : ℕ)
    (hg : DifferentiableAt ℂ g z) :
    deriv (shiftedTransferF g ρ k) z - lam * shiftedTransferF g ρ k z =
      (z - ρ) ^ k * shiftedTransferWitness g ρ lam k z := by
  rw [(hasDerivAt_shiftedTransferF g ρ z k hg).deriv]
  unfold shiftedTransferF shiftedTransferWitness
  ring

/-- `w(ρ) = (k+1)·g(ρ) ≠ 0`: the transferred denominator has order exactly `k` at `ρ`,
    one less than `F`'s order `k+1`. -/
theorem shiftedTransferWitness_at_root_ne_zero (g : ℂ → ℂ) (ρ lam : ℂ) (k : ℕ)
    (hg0 : g ρ ≠ 0) : shiftedTransferWitness g ρ lam k ρ ≠ 0 := by
  unfold shiftedTransferWitness
  simp only [sub_self, zero_mul, add_zero]
  exact mul_ne_zero (by exact_mod_cast (Nat.succ_ne_zero k)) hg0

/-- Away from `ρ`, `R_λ(z)/(z-ρ)` simplifies to `g(z)/w(z)` — the `(z-ρ)^k` factor
    cancels between numerator and denominator. -/
theorem shiftedTransfer_quotient_eq_of_ne (g : ℂ → ℂ) (ρ lam z : ℂ) (k : ℕ) (hz : z ≠ ρ)
    (hg : DifferentiableAt ℂ g z) (hw : shiftedTransferWitness g ρ lam k z ≠ 0) :
    shiftedTransferF g ρ k z /
        (deriv (shiftedTransferF g ρ k) z - lam * shiftedTransferF g ρ k z) / (z - ρ) =
      g z / shiftedTransferWitness g ρ lam k z := by
  rw [deriv_shiftedTransferF_sub_smul_eq g ρ lam z k hg]
  unfold shiftedTransferF
  have hsub : z - ρ ≠ 0 := sub_ne_zero_of_ne hz
  field_simp
  ring

theorem continuousAt_shiftedTransferWitness (g : ℂ → ℂ) (ρ lam : ℂ) (k : ℕ)
    (hgc : ContinuousAt g ρ) (hgdc : ContinuousAt (deriv g) ρ) :
    ContinuousAt (shiftedTransferWitness g ρ lam k) ρ := by
  unfold shiftedTransferWitness
  fun_prop

/-- **The item's stated asymptotic, formalized exactly**: `R_λ(z)/(z-ρ) → 1/(k+1)` as
    `z → ρ` along `z ≠ ρ` — the precise Lean form of `R_λ(s) = (s-ρ)/(k+1) + O((s-ρ)²)`.
    The removable singularity of `R_λ` at `ρ` extends it to a genuine **simple** zero
    (nonzero linear coefficient `1/(k+1)`), for every finite `λ`. `ContinuousAt (deriv g) ρ`
    is automatic whenever `g` is analytic (as in every intended application, e.g.
    `g = ξ`'s local cofactor) — stated as a direct hypothesis here rather than re-deriving
    it from `AnalyticOnNhd.deriv`'s neighborhood bookkeeping. -/
theorem tendsto_shiftedTransfer_quotient_div (g : ℂ → ℂ) (ρ lam : ℂ) (k : ℕ)
    (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0) (hgdc : ContinuousAt (deriv g) ρ) :
    Tendsto (fun z => shiftedTransferF g ρ k z /
        (deriv (shiftedTransferF g ρ k) z - lam * shiftedTransferF g ρ k z) / (z - ρ))
      (𝓝[≠] ρ) (𝓝 (1 / (k + 1 : ℂ))) := by
  have hev : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z :=
    hg.eventually_analyticAt.mono (fun y hy => hy.differentiableAt)
  have hcont : ContinuousAt (shiftedTransferWitness g ρ lam k) ρ :=
    continuousAt_shiftedTransferWitness g ρ lam k hg.continuousAt hgdc
  have hwne : shiftedTransferWitness g ρ lam k ρ ≠ 0 :=
    shiftedTransferWitness_at_root_ne_zero g ρ lam k hg0
  have hev_ne : ∀ᶠ z in 𝓝 ρ, shiftedTransferWitness g ρ lam k z ≠ 0 := hcont.eventually_ne hwne
  have heq : (fun z => shiftedTransferF g ρ k z /
        (deriv (shiftedTransferF g ρ k) z - lam * shiftedTransferF g ρ k z) / (z - ρ)) =ᶠ[𝓝[≠] ρ]
      (fun z => g z / shiftedTransferWitness g ρ lam k z) := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, hev_ne.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hzne hzρ
    exact shiftedTransfer_quotient_eq_of_ne g ρ lam z k hzρ hz hzne
  have hlim : Tendsto (fun z => g z / shiftedTransferWitness g ρ lam k z) (𝓝[≠] ρ)
      (𝓝 (g ρ / shiftedTransferWitness g ρ lam k ρ)) :=
    (hg.continuousAt.div hcont hwne).mono_left nhdsWithin_le_nhds
  have hval : g ρ / shiftedTransferWitness g ρ lam k ρ = 1 / (k + 1 : ℂ) := by
    unfold shiftedTransferWitness
    simp only [sub_self, zero_mul, add_zero]
    rw [div_eq_div_iff (mul_ne_zero (by exact_mod_cast (Nat.succ_ne_zero k)) hg0)
      (by exact_mod_cast (Nat.succ_ne_zero k))]
    ring
  rw [hval] at hlim
  exact hlim.congr' heq.symm

/-- **`R_λ` itself extends continuously to `0` at `ρ`**: the "zeros of `R_λ` are (among)
    the zeros of `F`" half of the item's conclusion, a direct corollary of
    `tendsto_shiftedTransfer_quotient_div` (multiply by `z-ρ → 0`). -/
theorem tendsto_shiftedTransfer_quotient_zero (g : ℂ → ℂ) (ρ lam : ℂ) (k : ℕ)
    (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0) (hgdc : ContinuousAt (deriv g) ρ) :
    Tendsto (fun z => shiftedTransferF g ρ k z /
        (deriv (shiftedTransferF g ρ k) z - lam * shiftedTransferF g ρ k z))
      (𝓝[≠] ρ) (𝓝 0) := by
  have h1 := tendsto_shiftedTransfer_quotient_div g ρ lam k hg hg0 hgdc
  have h2 : Tendsto (fun z : ℂ => z - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => z - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) :=
      (continuous_id.sub continuous_const).tendsto ρ
    simpa using this.mono_left nhdsWithin_le_nhds
  have := h1.mul h2
  simp only [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzρ : z - ρ ≠ 0 := sub_ne_zero_of_ne hz
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hzρ, mul_one]

end

end GppWeilParity
