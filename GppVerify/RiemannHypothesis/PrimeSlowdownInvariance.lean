import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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

end GppPrimeSlowdown
