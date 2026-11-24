/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central

/-!
# Dyadic Chebyshev bound (Heart claim #5, `HR16_chebyshev_dyadic`)

For every `n : ℕ`, with `ψ(x) = Σ_{k ≤ x} Λ(k)` (Mathlib's `Chebyshev.psi`),

`ψ(2n) − ψ(n) ≤ log C(2n, n) ≤ 2 n log 2`.

Proof: `ψ(m) = log lcm(1, …, m)`, and `lcm(1..2n) ∣ lcm(1..n) · C(2n, n)`: for a prime `p` with
`log_p(2n) > log_p(n)` the power `p^{log_p 2n}` lies in `(n, 2n]`, so the carry count
`#{i : p^i ≤ 2 (n mod p^i)}` of `C(2n, n)` contains `i = log_p 2n`. Elementary and zero-free.
No `sorry`, no `axiom`.
-/

namespace GppHeartChebyshev

open Nat Finset

/-- `lcm(1..2n) ∣ lcm(1..n) · C(2n, n)`. -/
theorem lcmUpto_two_mul_dvd (n : ℕ) :
    Nat.lcmUpto (2 * n) ∣ Nat.lcmUpto n * Nat.centralBinom n := by
  have hne1 : Nat.lcmUpto (2 * n) ≠ 0 := Nat.lcmUpto_ne_zero _
  have hne2 : Nat.lcmUpto n * Nat.centralBinom n ≠ 0 :=
    mul_ne_zero (Nat.lcmUpto_ne_zero _) (Nat.centralBinom_ne_zero n)
  rw [← Nat.factorization_le_iff_dvd hne1 hne2]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (Nat.lcmUpto_ne_zero _) (Nat.centralBinom_ne_zero n),
      Finsupp.add_apply, Nat.factorization_lcmUpto _ hp, Nat.factorization_lcmUpto _ hp]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    by_cases hlog : p.log (2 * n) = p.log n
    · rw [hlog]; exact Nat.le_add_right _ _
    · have hp1 : 1 < p := hp.one_lt
      have hle : p.log (2 * n) ≤ p.log n + 1 := by
        calc p.log (2 * n) ≤ p.log (n * p) :=
              Nat.log_mono_right (by nlinarith [hp.two_le])
          _ = p.log n + 1 := Nat.log_mul_base hp1 hn.ne'
      have hge : p.log n ≤ p.log (2 * n) := Nat.log_mono_right (by omega)
      have hj : p.log (2 * n) = p.log n + 1 := by omega
      -- the power p ^ j lies in (n, 2n]
      set j := p.log (2 * n) with hjdef
      have hpj_le : p ^ j ≤ 2 * n := Nat.pow_log_le_self p (by omega)
      have hpj_gt : n < p ^ j := by
        rw [hj]; exact Nat.lt_pow_succ_log_self hp1 n
      have hv : 1 ≤ (Nat.centralBinom n).factorization p := by
        have hcb : Nat.centralBinom n = Nat.choose (2 * n) n := rfl
        rw [hcb, Nat.factorization_choose (b := j + 1) hp (by omega) (by omega)]
        refine Finset.card_pos.mpr ⟨j, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        have h2 : 2 * n - n = n := by omega
        rw [h2, Nat.mod_eq_of_lt hpj_gt]
        omega
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **Heart claim #5.** `ψ(2n) − ψ(n) ≤ log C(2n, n) ≤ 2 n log 2`. -/
theorem chebyshev_dyadic (n : ℕ) :
    Chebyshev.psi (2 * n) - Chebyshev.psi n ≤ Real.log (Nat.centralBinom n) ∧
      Real.log (Nat.centralBinom n) ≤ 2 * n * Real.log 2 := by
  constructor
  · have hdvd := lcmUpto_two_mul_dvd n
    have hle : Nat.lcmUpto (2 * n) ≤ Nat.lcmUpto n * Nat.centralBinom n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero (Nat.lcmUpto_ne_zero _)
        (Nat.centralBinom_ne_zero n))) hdvd
    have h1 : Chebyshev.psi (2 * (n : ℝ)) = Real.log (Nat.lcmUpto (2 * n)) := by
      have := Chebyshev.psi_eq_log_lcmUpto (2 * n)
      push_cast at this
      exact this
    have h2 : Chebyshev.psi (n : ℝ) = Real.log (Nat.lcmUpto n) :=
      Chebyshev.psi_eq_log_lcmUpto n
    rw [h1, h2]
    have hpos1 : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
    have hpos2 : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
    have hle' : (Nat.lcmUpto (2 * n) : ℝ) ≤ Nat.lcmUpto n * Nat.centralBinom n := by
      exact_mod_cast hle
    have := Real.log_le_log (by exact_mod_cast Nat.lcmUpto_pos (2 * n)) hle'
    rw [Real.log_mul hpos1.ne' hpos2.ne'] at this
    linarith
  · have h4 : (Nat.centralBinom n : ℝ) ≤ 4 ^ n := by exact_mod_cast Nat.centralBinom_le_four_pow n
    have hpos2 : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
    have := Real.log_le_log hpos2 h4
    rw [Real.log_pow] at this
    have h22 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h22] at this
    linarith

end GppHeartChebyshev

#print axioms GppHeartChebyshev.lcmUpto_two_mul_dvd
#print axioms GppHeartChebyshev.chebyshev_dyadic
