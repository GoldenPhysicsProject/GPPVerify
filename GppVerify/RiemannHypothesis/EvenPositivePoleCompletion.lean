import Mathlib.Tactic

/-!
# Positive-pole completion: a direct-sum quadratic certificate

Source: Astra's 2026-10-15 even-sector lemma in private GPP-bridge,
independently audited by Grok S26. Codex formalization workbench.

The theorem below is real finite algebra for the two-channel weighted
Cauchy--Schwarz inequality. The componentwise theorem covers the
real/imaginary decomposition when the underlying energy splits.

It is **not** a formalization of the continuous Fourier multiplier, its
Arb interval bounds, the DC-lift integral identity, or RH/GRH.
-/

namespace GppEvenPositivePoleCompletion

/-- A two-coordinate Cauchy--Schwarz bound, with energy `E` and
pole coordinate `w`. If `x² ≤ β E`, then the squared combination
`x + lam w` is controlled by the sum of both positive energies.
The factor `lam²/2` is essential. -/
theorem two_channel_cauchy
    (E β lam x w : ℝ) (hE : 0 ≤ E) (hβ : 0 ≤ β)
    (hx : x ^ 2 ≤ β * E) :
    (x + lam * w) ^ 2 ≤ (β + lam ^ 2 / 2) * (E + 2 * w ^ 2) := by
  by_cases hzero : E = 0
  · have hxzero : x = 0 := by
      have hsq : x ^ 2 ≤ 0 := by simpa [hzero] using hx
      nlinarith [sq_nonneg x]
    subst x
    rw [hzero]
    have hprod : 0 ≤ β * w ^ 2 := mul_nonneg hβ (sq_nonneg w)
    nlinarith
  · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    have hgap : 0 ≤ β * E - x ^ 2 := sub_nonneg.mpr hx
    have heplus : 0 ≤ E + 2 * w ^ 2 := by nlinarith [sq_nonneg w]
    have hprod : 0 ≤ (β * E - x ^ 2) * (E + 2 * w ^ 2) :=
      mul_nonneg hgap heplus
    have hsquare : 0 ≤ (lam * E - 2 * x * w) ^ 2 := sq_nonneg _
    have hid :
        2 * E * ((β + lam ^ 2 / 2) * (E + 2 * w ^ 2) - (x + lam * w) ^ 2) =
          (lam * E - 2 * x * w) ^ 2 +
            2 * (β * E - x ^ 2) * (E + 2 * w ^ 2) := by ring
    have hnonneg :
        0 ≤ 2 * E *
          ((β + lam ^ 2 / 2) * (E + 2 * w ^ 2) - (x + lam * w) ^ 2) := by
      rw [hid]
      nlinarith [hprod, hsquare]
    have htarget :
        0 ≤ (β + lam ^ 2 / 2) * (E + 2 * w ^ 2) - (x + lam * w) ^ 2 := by
      by_contra hn
      have hneg :
          (β + lam ^ 2 / 2) * (E + 2 * w ^ 2) - (x + lam * w) ^ 2 < 0 :=
        lt_of_not_ge hn
      have hcontr :
          2 * E *
            ((β + lam ^ 2 / 2) * (E + 2 * w ^ 2) - (x + lam * w) ^ 2) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hneg
      exact (not_lt_of_ge hnonneg) hcontr
    exact sub_nonneg.mp htarget

/-- The direct-sum positive-pole estimate before inserting the
Fourier-multiplier coercive floor. In Astra's notation,
`E=A(g)`, `w=⟨cosh(x/2),g⟩`, `x=⟨r,g⟩`,
and `C` is the DC-lift coefficient. -/
theorem positive_pole_completion
    (E β lam x w C : ℝ)
    (hE : 0 ≤ E) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hx : x ^ 2 ≤ β * E) :
    (1 - C * (β + lam ^ 2 / 2)) * (E + 2 * w ^ 2) ≤
      E + 2 * w ^ 2 - C * (x + lam * w) ^ 2 := by
  have hcs := two_channel_cauchy E β lam x w hE hβ hx
  have hm := mul_le_mul_of_nonneg_left hcs hC
  calc
    (1 - C * (β + lam ^ 2 / 2)) * (E + 2 * w ^ 2) =
        E + 2 * w ^ 2 - C * ((β + lam ^ 2 / 2) * (E + 2 * w ^ 2)) := by ring
    _ ≤ E + 2 * w ^ 2 - C * (x + lam * w) ^ 2 := by linarith

/-- The coercive gap follows once `E ≥ c N` and the residual
criterion `1 - C(β+lam²/2) ≥ 0` have both been independently checked. -/
theorem positive_pole_coercivity
    (E β lam x w C c N : ℝ)
    (hE : 0 ≤ E) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hx : x ^ 2 ≤ β * E) (hfloor : c * N ≤ E)
    (hmargin : 0 ≤ 1 - C * (β + lam ^ 2 / 2)) :
    (1 - C * (β + lam ^ 2 / 2)) * (c * N) ≤
      E + 2 * w ^ 2 - C * (x + lam * w) ^ 2 := by
  have hfloor' : c * N ≤ E + 2 * w ^ 2 := by nlinarith [sq_nonneg w]
  have hmult := mul_le_mul_of_nonneg_left hfloor' hmargin
  exact le_trans hmult (positive_pole_completion E β lam x w C hE hβ hC hx)

/-- Componentwise extension to the real and imaginary channels.
It records the complex-test algebra when an even real kernel gives
`E=E_re+E_im` and separate residual Cauchy bounds. -/
theorem two_component_positive_pole
    (Ere Eim β lam xr xi wr wi C : ℝ)
    (hre : 0 ≤ Ere) (him : 0 ≤ Eim) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hxr : xr ^ 2 ≤ β * Ere) (hxi : xi ^ 2 ≤ β * Eim) :
    (1 - C * (β + lam ^ 2 / 2)) *
        (Ere + Eim + 2 * (wr ^ 2 + wi ^ 2)) ≤
      Ere + Eim + 2 * (wr ^ 2 + wi ^ 2) -
        C * ((xr + lam * wr) ^ 2 + (xi + lam * wi) ^ 2) := by
  have h1 := positive_pole_completion Ere β lam xr wr C hre hβ hC hxr
  have h2 := positive_pole_completion Eim β lam xi wi C him hβ hC hxi
  linarith [h1, h2]


theorem pole_lambda_square_identity (a b d lam : ℝ) :
    (d + 1 / 2) * (a - 2 * b * lam + (d + 1 / 2) * lam ^ 2) =
      (d + 1 / 2) * a - b ^ 2 + ((d + 1 / 2) * lam - b) ^ 2 := by
  ring

theorem pole_lambda_lower_bound (a b d lam : ℝ) :
    (d + 1 / 2) * a - b ^ 2 ≤
      (d + 1 / 2) * (a - 2 * b * lam + (d + 1 / 2) * lam ^ 2) := by
  rw [pole_lambda_square_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem necessary_pole_lambda_budget
    (C β lam : ℝ) (hC : 0 < C) (hβ : 0 ≤ β)
    (hmargin : C * (β + lam ^ 2 / 2) < 1) :
    C * lam ^ 2 < 2 := by
  have hprod : 0 ≤ C * β := mul_nonneg (le_of_lt hC) hβ
  nlinarith

end GppEvenPositivePoleCompletion
