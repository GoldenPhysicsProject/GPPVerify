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
`x + λ w` is controlled by the sum of both positive energies.
The factor `λ²/2` is essential. -/
theorem two_channel_cauchy
    (E β λ x w : ℝ) (hE : 0 ≤ E) (hβ : 0 ≤ β)
    (hx : x ^ 2 ≤ β * E) :
    (x + λ * w) ^ 2 ≤ (β + λ ^ 2 / 2) * (E + 2 * w ^ 2) := by
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
    have hsquare : 0 ≤ (λ * E - 2 * x * w) ^ 2 := sq_nonneg _
    have hid :
        2 * E * ((β + λ ^ 2 / 2) * (E + 2 * w ^ 2) - (x + λ * w) ^ 2) =
          (λ * E - 2 * x * w) ^ 2 +
            2 * (β * E - x ^ 2) * (E + 2 * w ^ 2) := by ring
    have hnonneg :
        0 ≤ 2 * E *
          ((β + λ ^ 2 / 2) * (E + 2 * w ^ 2) - (x + λ * w) ^ 2) := by
      rw [hid]
      nlinarith [hprod, hsquare]
    have htarget :
        0 ≤ (β + λ ^ 2 / 2) * (E + 2 * w ^ 2) - (x + λ * w) ^ 2 := by
      by_contra hn
      have hneg :
          (β + λ ^ 2 / 2) * (E + 2 * w ^ 2) - (x + λ * w) ^ 2 < 0 :=
        lt_of_not_ge hn
      have hcontr :
          2 * E *
            ((β + λ ^ 2 / 2) * (E + 2 * w ^ 2) - (x + λ * w) ^ 2) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hneg
      exact (not_lt_of_ge hnonneg) hcontr
    exact sub_nonneg.mp htarget

/-- The direct-sum positive-pole estimate before inserting the
Fourier-multiplier coercive floor. In Astra's notation,
`E=A(g)`, `w=⟨cosh(x/2),g⟩`, `x=⟨r,g⟩`,
and `C` is the DC-lift coefficient. -/
theorem positive_pole_completion
    (E β λ x w C : ℝ)
    (hE : 0 ≤ E) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hx : x ^ 2 ≤ β * E) :
    (1 - C * (β + λ ^ 2 / 2)) * (E + 2 * w ^ 2) ≤
      E + 2 * w ^ 2 - C * (x + λ * w) ^ 2 := by
  have hcs := two_channel_cauchy E β λ x w hE hβ hx
  have hm := mul_le_mul_of_nonneg_left hcs hC
  calc
    (1 - C * (β + λ ^ 2 / 2)) * (E + 2 * w ^ 2) =
        E + 2 * w ^ 2 - C * ((β + λ ^ 2 / 2) * (E + 2 * w ^ 2)) := by ring
    _ ≤ E + 2 * w ^ 2 - C * (x + λ * w) ^ 2 := by linarith

/-- The coercive gap follows once `E ≥ c N` and the residual
criterion `1 - C(β+λ²/2) ≥ 0` have both been independently checked. -/
theorem positive_pole_coercivity
    (E β λ x w C c N : ℝ)
    (hE : 0 ≤ E) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hx : x ^ 2 ≤ β * E) (hfloor : c * N ≤ E)
    (hmargin : 0 ≤ 1 - C * (β + λ ^ 2 / 2)) :
    (1 - C * (β + λ ^ 2 / 2)) * (c * N) ≤
      E + 2 * w ^ 2 - C * (x + λ * w) ^ 2 := by
  have hfloor' : c * N ≤ E + 2 * w ^ 2 := by nlinarith [sq_nonneg w]
  have hmult := mul_le_mul_of_nonneg_left hfloor' hmargin
  exact le_trans hmult (positive_pole_completion E β λ x w C hE hβ hC hx)

/-- Componentwise extension to the real and imaginary channels.
It records the complex-test algebra when an even real kernel gives
`E=E_re+E_im` and separate residual Cauchy bounds. -/
theorem two_component_positive_pole
    (Ere Eim β λ xr xi wr wi C : ℝ)
    (hre : 0 ≤ Ere) (him : 0 ≤ Eim) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hxr : xr ^ 2 ≤ β * Ere) (hxi : xi ^ 2 ≤ β * Eim) :
    (1 - C * (β + λ ^ 2 / 2)) *
        (Ere + Eim + 2 * (wr ^ 2 + wi ^ 2)) ≤
      Ere + Eim + 2 * (wr ^ 2 + wi ^ 2) -
        C * ((xr + λ * wr) ^ 2 + (xi + λ * wi) ^ 2) := by
  have h1 := positive_pole_completion Ere β λ xr wr C hre hβ hC hxr
  have h2 := positive_pole_completion Eim β λ xi wi C him hβ hC hxi
  linarith [h1, h2]

end GppEvenPositivePoleCompletion
