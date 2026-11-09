/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import Mathlib.NumberTheory.Padics.PadicNorm


/-!
# Adelic Poisson layer: the arithmetic core of discreteness (GP1)

A rational number that is `p`-integral for every prime `p` is an integer
(`den_eq_one_of_padicNorm_le_one`); if moreover `|q| < 1` then `q = 0`
(`eq_zero_of_integral_of_abs_lt_one`). This is the arithmetic content of the discreteness of
`ℚ` in the adeles: the box `(-1/2, 1/2) × ∏ ℤ_p` meets the principal adeles only in `0`. It
is independent of the choice of adele carrier; the topological statement GP1, cocompactness
GP2, the fundamental domain GP3 and the covolume GP4 remain to be built on the carrier
agreed with Turbo (GPP-bridge PR #11, comment 6730423880).

Governing specification: Principal series's global Tate statement sheet (GPP-bridge branch
`principal-series/global-tate-statements` at `77d5b43`, §4), audited PASS by Turbo.
-/

namespace GlobalTate.Poisson

/-- A rational that is `p`-integral for every prime `p` is an integer. -/
theorem den_eq_one_of_padicNorm_le_one (q : ℚ)
    (h : ∀ p : ℕ, p.Prime → padicNorm p q ≤ 1) : q.den = 1 := by
  by_contra hden
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hden
  have : Fact p.Prime := ⟨hp⟩
  have hq : q ≠ 0 := by rintro rfl; simp at hden
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    exact hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left h1 q.reduced).eq_one_of_dvd hpd)
  have hv : padicValRat p q ≤ -1 := by
    have hden1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_ne_zero hpd
    rw [padicValRat, padicValInt.eq_zero_of_not_dvd hnum]
    omega
  have hn := padicNorm.eq_zpow_of_nonzero (p := p) hq
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have : (1 : ℚ) < padicNorm p q := by
    rw [hn]
    calc (1 : ℚ) < (p : ℚ) ^ (1 : ℤ) := by simpa using hp1
      _ ≤ (p : ℚ) ^ (-padicValRat p q) := zpow_le_zpow_right₀ hp1.le (by omega)
  exact absurd (h p hp) (not_le.mpr this)

/-- An integer of absolute value less than one is zero; with the previous lemma, the box
`(-1/2, 1/2) × ∏ ℤ_p` meets `ℚ` only in `0` (the arithmetic core of GP1). -/
theorem eq_zero_of_integral_of_abs_lt_one (q : ℚ)
    (h : ∀ p : ℕ, p.Prime → padicNorm p q ≤ 1) (hq : |q| < 1) : q = 0 := by
  have hd := den_eq_one_of_padicNorm_le_one q h
  have hint : q = (q.num : ℚ) := by
    rw [← Rat.num_div_den q]; simp [hd]
  rw [hint] at hq ⊢
  have : |q.num| < 1 := by exact_mod_cast hq
  have : q.num = 0 := by have := abs_lt.mp this; omega
  simp [this]

end GlobalTate.Poisson
