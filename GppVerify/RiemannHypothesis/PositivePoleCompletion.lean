import Mathlib.Tactic

/-!
# Positive-pole completion: algebraic direct-sum certificate

Daniel Toupin / Golden Physics Project, October 15, 2026.
Based on Astra's even Weil-form completion and Grok's S26 audit.

The finite real-coordinate argument proves the sharp weighted Cauchy
bound by an explicit square identity. The complex quadratic follows
by applying the same estimates to real and imaginary coordinates.

This file does NOT formalize the Fourier/Plancherel bound, the Arb
certificate for any support window, or global Weil positivity.
RH and Dirichlet GRH are not claimed.
-/

namespace GppPositivePoleCompletion

/-- Exact polynomial square certificate behind the direct-sum
Cauchy--Schwarz estimate. No division by the energy is needed. -/
theorem cauchy_square_identity (A beta R W lambda : ℝ) :
    2 * beta *
      ((beta + lambda^2 / 2) * (A + 2 * W^2) -
       (R + lambda * W)^2)
      =
      (2 * beta + lambda^2) * (beta * A - R^2) +
      (2 * beta * W - lambda * R)^2 := by
  ring

/-- Energy-controlled residual R and an independent pole coordinate W
give a direct-sum Cauchy--Schwarz estimate with the essential lambda²/2
penalty. -/
theorem direct_sum_cauchy (A beta R W lambda : ℝ)
    (hbeta : 0 < beta) (hR : R^2 ≤ beta * A) :
    (R + lambda * W)^2 ≤
      (beta + lambda^2 / 2) * (A + 2 * W^2) := by
  have hcoeff : 0 ≤ 2 * beta + lambda^2 := by positivity
  have hterm : 0 ≤ (2 * beta + lambda^2) * (beta * A - R^2) :=
    mul_nonneg hcoeff (sub_nonneg.mpr hR)
  have hsquare : 0 ≤ (2 * beta * W - lambda * R)^2 := sq_nonneg _
  have heq := cauchy_square_identity A beta R W lambda
  have hprod : 0 ≤ 2 * beta *
      ((beta + lambda^2 / 2) * (A + 2 * W^2) -
       (R + lambda * W)^2) := by
    rw [heq]
    linarith
  by_contra hnot
  have hnegative : (beta + lambda^2 / 2) * (A + 2 * W^2) -
      (R + lambda * W)^2 < 0 := sub_neg.mpr (lt_of_not_ge hnot)
  have hfactor : 0 < 2 * beta := by positivity
  have : 2 * beta *
      ((beta + lambda^2 / 2) * (A + 2 * W^2) -
       (R + lambda * W)^2) < 0 :=
    mul_neg_of_pos_of_neg hfactor hnegative
  linarith

/-- Positive-pole completion, with quantitative coercivity retained.
The hypotheses are the independently provable Fourier residual bound
and a positive lifted multiplier. In the application,
u = r + lambda*w and Q = A + 2|w|² - C|u|². -/
theorem positive_pole_coercivity
    (A beta R W lambda C c eta N : ℝ)
    (hbeta : 0 < beta)
    (hC : 0 ≤ C)
    (hcoercive : c * N ≤ A)
    (hR : R^2 ≤ beta * A)
    (heta : eta = 1 - C * (beta + lambda^2 / 2))
    (heta_nonneg : 0 ≤ eta) :
    eta * c * N ≤
      A + 2 * W^2 - C * (R + lambda * W)^2 := by
  have hcauchy := direct_sum_cauchy A beta R W lambda hbeta hR
  have hpenalty : C * (R + lambda * W)^2 ≤
      C * ((beta + lambda^2 / 2) * (A + 2 * W^2)) :=
    mul_le_mul_of_nonneg_left hcauchy hC
  have hbase : c * N ≤ A + 2 * W^2 := by
    nlinarith [sq_nonneg W]
  have hscaled : eta * (c * N) ≤ eta * (A + 2 * W^2) :=
    mul_le_mul_of_nonneg_left hbase heta_nonneg
  calc
    eta * c * N = eta * (c * N) := by ring
    _ ≤ eta * (A + 2 * W^2) := hscaled
    _ = A + 2 * W^2 -
        C * ((beta + lambda^2 / 2) * (A + 2 * W^2)) := by
          rw [heta]
          ring
    _ ≤ A + 2 * W^2 - C * (R + lambda * W)^2 := by
      linarith

/-- Independent real and imaginary energy coordinates certify arbitrary
complex tests once the real kernel/Plancherel reduction is established.
The theorem is an exact algebraic sum, not an identification with Weil's
infinite-dimensional quadratic form. -/
theorem two_coordinate_coercivity
    (A₁ A₂ beta R₁ R₂ W₁ W₂ lambda C c eta N₁ N₂ : ℝ)
    (hbeta : 0 < beta) (hC : 0 ≤ C)
    (hA₁ : c * N₁ ≤ A₁) (hA₂ : c * N₂ ≤ A₂)
    (hR₁ : R₁^2 ≤ beta * A₁) (hR₂ : R₂^2 ≤ beta * A₂)
    (heta : eta = 1 - C * (beta + lambda^2 / 2))
    (heta_nonneg : 0 ≤ eta) :
    eta * c * (N₁ + N₂) ≤
      (A₁ + 2 * W₁^2 - C * (R₁ + lambda * W₁)^2) +
      (A₂ + 2 * W₂^2 - C * (R₂ + lambda * W₂)^2) := by
  have h₁ := positive_pole_coercivity A₁ beta R₁ W₁ lambda C c eta N₁
    hbeta hC hA₁ hR₁ heta heta_nonneg
  have h₂ := positive_pole_coercivity A₂ beta R₂ W₂ lambda C c eta N₂
    hbeta hC hA₂ hR₂ heta heta_nonneg
  calc
    eta * c * (N₁ + N₂) = eta * c * N₁ + eta * c * N₂ := by ring
    _ ≤ _ := add_le_add h₁ h₂

end GppPositivePoleCompletion
