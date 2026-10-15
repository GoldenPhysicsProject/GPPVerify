import Mathlib.Tactic

/-!
# Positive-pole completion: exact two-coordinate square certificate

Daniel Toupin / Golden Physics Project, with Astra's even-sector pole-completion
construction and Codex's explicit algebraic slack decomposition (2026-10-15).

These are abstract real algebra lemmas. The two-real-component version allows
complex-valued tests, provided the Fourier-energy estimate has been established
on their real and imaginary components. Neither the multiplier bound nor a
continuum Weil certificate is proved by this module. RH and GRH remain open.
-/

namespace GppEvenPoleCompletion

/-- An exact polynomial sum-of-squares identity for direct-sum Cauchy-Schwarz.
The first term measures Fourier-energy slack; the second is an alignment square. -/
theorem direct_sum_slack_identity (A β λ r w : ℝ) :
    (2 * β) * ((β + λ ^ 2 / 2) * (A + 2 * w ^ 2) - (r + λ * w) ^ 2) =
      (2 * β + λ ^ 2) * (β * A - r ^ 2) + (λ * r - 2 * β * w) ^ 2 := by
  ring

/-- Real two-coordinate weighted Cauchy-Schwarz, including β = 0. -/
theorem direct_sum_bound (A β λ r w : ℝ)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (hr : r ^ 2 ≤ β * A) :
    (r + λ * w) ^ 2 ≤ (β + λ ^ 2 / 2) * (A + 2 * w ^ 2) := by
  rcases eq_or_lt_of_le hβ with hzero | hpos
  · subst β
    have hrsq : r ^ 2 = 0 := by nlinarith [sq_nonneg r]
    have hrzero : r = 0 := pow_eq_zero hrsq
    subst r
    nlinarith [mul_nonneg (sq_nonneg λ) hA]
  · have hcoeff : 0 ≤ 2 * β + λ ^ 2 := by positivity
    have hslack : 0 ≤ β * A - r ^ 2 := sub_nonneg.mpr hr
    have hsquare : 0 ≤ (λ * r - 2 * β * w) ^ 2 := sq_nonneg _
    have hsum : 0 ≤
        (2 * β + λ ^ 2) * (β * A - r ^ 2) +
          (λ * r - 2 * β * w) ^ 2 :=
      add_nonneg (mul_nonneg hcoeff hslack) hsquare
    have hprod : 0 ≤ (2 * β) *
        ((β + λ ^ 2 / 2) * (A + 2 * w ^ 2) - (r + λ * w) ^ 2) := by
      rw [direct_sum_slack_identity]
      exact hsum
    have htwopos : 0 < 2 * β := by linarith
    have hdiff : 0 ≤
        (β + λ ^ 2 / 2) * (A + 2 * w ^ 2) - (r + λ * w) ^ 2 := by
      by_contra hn
      have hneg :
          (β + λ ^ 2 / 2) * (A + 2 * w ^ 2) - (r + λ * w) ^ 2 < 0 :=
        lt_of_not_ge hn
      have hcontr : (2 * β) *
          ((β + λ ^ 2 / 2) * (A + 2 * w ^ 2) - (r + λ * w) ^ 2) < 0 :=
        mul_neg_of_pos_of_neg htwopos hneg
      exact (not_lt_of_ge hprod) hcontr
    exact sub_nonneg.mp hdiff

/-- Keep the favorable positive cosh pole instead of bounding the bare form. -/
theorem positive_pole_completion (A β C λ r w : ℝ)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hr : r ^ 2 ≤ β * A) :
    (1 - C * (β + λ ^ 2 / 2)) * (A + 2 * w ^ 2) ≤
      A + 2 * w ^ 2 - C * (r + λ * w) ^ 2 := by
  have hb := direct_sum_bound A β λ r w hA hβ hr
  have hc := mul_le_mul_of_nonneg_left hb hC
  nlinarith

/-- Coercivity transfer with externally established Fourier and multiplier bounds. -/
theorem positive_pole_coercivity (A β C c η λ r w N : ℝ)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hc : 0 ≤ c) (hη : 0 ≤ η) (hN : 0 ≤ N)
    (hr : r ^ 2 ≤ β * A) (henergy : c * N ≤ A)
    (hmargin : η ≤ 1 - C * (β + λ ^ 2 / 2)) :
    η * c * N ≤ A + 2 * w ^ 2 - C * (r + λ * w) ^ 2 := by
  have hcomp := positive_pole_completion A β C λ r w hA hβ hC hr
  have henergy' : c * N ≤ A + 2 * w ^ 2 := by
    nlinarith [sq_nonneg w]
  have hmargin0 : 0 ≤ 1 - C * (β + λ ^ 2 / 2) := le_trans hη hmargin
  have hstep1 := mul_le_mul_of_nonneg_left henergy' hmargin0
  have hcn : 0 ≤ c * N := mul_nonneg hc hN
  have hstep2 := mul_le_mul_of_nonneg_right hmargin hcn
  nlinarith

/-- Real and imaginary components of a complex test are both retained. -/
theorem complex_component_bound (Ar Ai β λ rr ri wr wi : ℝ)
    (hAr : 0 ≤ Ar) (hAi : 0 ≤ Ai) (hβ : 0 ≤ β)
    (hrr : rr ^ 2 ≤ β * Ar) (hri : ri ^ 2 ≤ β * Ai) :
    (rr + λ * wr) ^ 2 + (ri + λ * wi) ^ 2 ≤
      (β + λ ^ 2 / 2) * (Ar + Ai + 2 * (wr ^ 2 + wi ^ 2)) := by
  have hr := direct_sum_bound Ar β λ rr wr hAr hβ hrr
  have hi := direct_sum_bound Ai β λ ri wi hAi hβ hri
  nlinarith

end GppEvenPoleCompletion
