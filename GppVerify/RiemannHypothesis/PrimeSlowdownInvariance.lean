import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Slowing or freezing finitely many prime rotations moves no zeta zero

Source: Codex, GPP-bridge PR #11 comment 6394506081, answering Daniel's "are the zeros prime
circles interfering?". Daniel Toupin / Golden Physics Project, with AI assistance from Codex
(statement) and Claude Code (formalization).

Fix a finite set `P` of integers `p ≥ 2` and rates `α_p ∈ [0, 1]`. Slow the `p`-th rotation by
`α_p` about `σ₀ = 1/2`, i.e. replace `s` by `s'_p = 1/2 + α_p (s − 1/2)` in its Euler factor:
`ζ_{P,α}(s) = ζ(s) · M(s)` with `M(s) = ∏_{p ∈ P} (1 − p^{−s}) / (1 − p^{−s'_p})`.
`α_p = 0` freezes the `p`-th circle entirely.

* `slow_re_pos`: `Re s > 0` and `α ∈ [0, 1]` give `Re s'_p > 0`.
* `one_sub_cpow_ne_zero`: `1 − p^{−z} ≠ 0` for `p ≥ 2` and `Re z > 0`, since `|p^{−z}| = p^{−Re z} < 1`.
* `multiplier_ne_zero`: `M(s) ≠ 0` on `Re s > 0`.
* `differentiableAt_multiplier`: `M` is holomorphic on `Re s > 0`.
* `zeros_invariant`: on `Re s > 0`, `ζ_{P,α}(s) = 0 ↔ ζ(s) = 0`.

So any finite set of prime circles can be slowed or frozen individually without moving a single
zero in `Re s > 0`. The zeros come from global (all-prime, completed) interference, not from
particular prime circles lining up.

**All-prime freezing is a singular limit** (Codex, PR #11 comment 6394642859; checkpoint
`work/codex/2026-10-25_sol_support_normalized_prime_freezing_limit.md`). Freeze every prime below
`n` and drop the `s`-independent constant: `R_n(s) = ζ(s) ∏_{p < n} (1 − p^{−s})`.

* `R_tendsto_one`: `R_n(s) → 1` for `Re s > 1` (Euler product).
* `R_eq_zero`: `R_n(ρ) = 0` at every zero `ρ` of `ζ`, for every `n`.
* `no_locallyUniform_limit`: on any open preconnected `D` with `1 ∉ D`, meeting `Re s > 1` and
  containing a zero of `ζ`, **no** subsequence `R_{φ(k)}` converges locally uniformly on `D`. A
  limit would be holomorphic, equal to `1` near the point with `Re s > 1`, hence `1` on `D` by the
  identity theorem, yet `0` at the zero. So finite zero invariance cannot be exchanged with the
  all-prime limit. Codex's version uses `(s − 1)R_n` and allows `1 ∈ D`; that is not formalized,
  and neither is the Montel conclusion "not locally bounded".

**Scope.** This is an edit of finitely many Euler factors, not of the conditionally convergent
`η` summands. `ζ_{P,α}` need not satisfy the functional equation. Equality of multiplicities
(true, since `M` is a holomorphic unit) is not stated, and the uniform reparametrisation
`t = ατ` is not formalized. Elementary; not claimed novel. No claim about RH.
-/

set_option autoImplicit false

open Complex

namespace GppPrimeSlowdown

/-- The slowed spectral point `s'_p = 1/2 + α (s − 1/2)`. -/
noncomputable def slow (α : ℝ) (s : ℂ) : ℂ := 1 / 2 + α * (s - 1 / 2)

theorem slow_re_pos {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    0 < (slow α s).re := by
  simp only [slow, add_re, mul_re, ofReal_re, ofReal_im, sub_re, sub_im, zero_mul, sub_zero]
  norm_num
  have hr : 0 ≤ α * s.re := mul_nonneg h0 hs.le
  rcases lt_or_eq_of_le h1 with h | rfl
  · nlinarith
  · linarith

theorem one_sub_cpow_ne_zero {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    1 - (p : ℂ) ^ (-z) ≠ 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hnorm : ‖(p : ℂ) ^ (-z)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos (by omega), neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  intro h
  have : (p : ℂ) ^ (-z) = 1 := by linear_combination -h
  rw [this, norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- The finite Euler multiplier `M(s) = ∏_{p ∈ P} (1 − p^{−s}) / (1 − p^{−s'_p})`. -/
noncomputable def multiplier (P : Finset ℕ) (α : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, (1 - (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-slow (α p) s))

/-- The modified zeta `ζ_{P,α} = ζ · M`. -/
noncomputable def zetaSlow (P : Finset ℕ) (α : ℕ → ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * multiplier P α s

variable {P : Finset ℕ} {α : ℕ → ℝ}

theorem multiplier_ne_zero (hP : ∀ p ∈ P, 2 ≤ p) (hα : ∀ p ∈ P, 0 ≤ α p ∧ α p ≤ 1) {s : ℂ}
    (hs : 0 < s.re) : multiplier P α s ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  exact div_ne_zero (one_sub_cpow_ne_zero (hP p hp) hs)
    (one_sub_cpow_ne_zero (hP p hp) (slow_re_pos (hα p hp).1 (hα p hp).2 hs))

theorem differentiableAt_multiplier (hP : ∀ p ∈ P, 2 ≤ p)
    (hα : ∀ p ∈ P, 0 ≤ α p ∧ α p ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (multiplier P α) s := by
  unfold multiplier
  refine DifferentiableAt.fun_finsetProd
    (f := fun (p : ℕ) (z : ℂ) => (1 - (p : ℂ) ^ (-z)) / (1 - (p : ℂ) ^ (-slow (α p) z))) fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by have := hP p hp; omega)
  have hden := one_sub_cpow_ne_zero (hP p hp) (slow_re_pos (hα p hp).1 (hα p hp).2 hs)
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    (differentiableAt_const _).sub ((differentiableAt_id.neg).const_cpow (Or.inl hp0))
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-slow (α p) z)) s := by
    unfold slow
    exact (differentiableAt_const _).sub
      (((differentiableAt_const _).add ((differentiableAt_const _).mul
        (differentiableAt_id.sub (differentiableAt_const _)))).neg.const_cpow (Or.inl hp0))
  exact hd1.div hd2 hden

/-- **Zero invariance.** On `Re s > 0`, slowing or freezing finitely many prime rotations moves
no zero: `ζ_{P,α}(s) = 0 ↔ ζ(s) = 0`. -/
theorem zeros_invariant (hP : ∀ p ∈ P, 2 ≤ p) (hα : ∀ p ∈ P, 0 ≤ α p ∧ α p ≤ 1) {s : ℂ}
    (hs : 0 < s.re) : zetaSlow P α s = 0 ↔ riemannZeta s = 0 := by
  rw [zetaSlow, mul_eq_zero, or_iff_left (multiplier_ne_zero hP hα hs)]

section Freezing

open Filter Topology Nat

/-- Freeze every prime below `n`: `R_n(s) = ζ(s) ∏_{p < n} (1 − p^{−s})`. -/
noncomputable def R (n : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * ∏ p ∈ primesBelow n, (1 - (p : ℂ) ^ (-s))

theorem R_tendsto_one {s : ℂ} (hs : 1 < s.re) : Tendsto (fun n => R n s) atTop (𝓝 1) := by
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have h := (riemannZeta_eulerProduct hs).inv₀ hz
  have h2 := h.const_mul (riemannZeta s)
  rw [mul_inv_cancel₀ hz] at h2
  refine h2.congr fun n => ?_
  rw [R, ← Finset.prod_inv_distrib]
  simp

theorem R_eq_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) (n : ℕ) : R n ρ = 0 := by
  rw [R, hρ, zero_mul]

lemma differentiableOn_R (n : ℕ) {D : Set ℂ} (hD1 : (1 : ℂ) ∉ D) :
    DifferentiableOn ℂ (R n) D := by
  intro s hs
  have hs1 : s ≠ 1 := fun h => hD1 (h ▸ hs)
  refine (DifferentiableAt.mul (differentiableAt_riemannZeta hs1) ?_).differentiableWithinAt
  refine DifferentiableAt.fun_finsetProd (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z))
    fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := by
    have := (Nat.prime_of_mem_primesBelow hp).pos
    exact_mod_cast this.ne'
  exact (differentiableAt_const _).sub ((differentiableAt_id.neg).const_cpow (Or.inl hp0))

/-- **No locally uniform limit across a zero.** -/
theorem no_locallyUniform_limit {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hD1 : (1 : ℂ) ∉ D) {s₀ : ℂ} (hs₀ : s₀ ∈ D) (hre : 1 < s₀.re) {ρ : ℂ} (hρD : ρ ∈ D)
    (hρ : riemannZeta ρ = 0) {sub : ℕ → ℕ} (hsub : Tendsto sub atTop atTop) (g : ℂ → ℂ) :
    ¬ TendstoLocallyUniformlyOn (fun k => R (sub k)) g atTop D := by
  intro hlu
  have hg : DifferentiableOn ℂ g D :=
    hlu.differentiableOn (Eventually.of_forall fun k => differentiableOn_R _ hD1) hDo
  have hpt : ∀ s ∈ D, Tendsto (fun k => R (sub k) s) atTop (𝓝 (g s)) :=
    fun s hs => hlu.tendsto_at hs
  -- `g = 1` on the open set `D ∩ {Re s > 1}`
  have hU : IsOpen (D ∩ {s : ℂ | 1 < s.re}) :=
    hDo.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hone : ∀ s ∈ D ∩ {s : ℂ | 1 < s.re}, g s = 1 := fun s hs =>
    tendsto_nhds_unique (hpt s hs.1) ((R_tendsto_one hs.2).comp hsub)
  have hev : g =ᶠ[𝓝 s₀] fun _ => (1 : ℂ) :=
    Filter.eventually_of_mem (hU.mem_nhds ⟨hs₀, hre⟩) hone
  have heq := (hg.analyticOnNhd hDo).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hDc hs₀ hev
  have h0 : g ρ = 0 := by
    have := hpt ρ hρD
    simp only [R_eq_zero hρ] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have h1 := heq hρD
  rw [h0] at h1
  exact zero_ne_one h1

end Freezing

end GppPrimeSlowdown
