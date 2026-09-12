/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Order of growth of an entire function

An entire function `f` has *order of growth at most `ρ`* when for every `ε > 0` there is a
constant `C` with

  `‖f z‖ ≤ C * exp (‖z‖ ^ (ρ + ε))`

for all `z`. The order itself is the infimum of such `ρ`, but essentially every theorem in the
subject — Hadamard's factorisation theorem above all — is stated and used in terms of the
predicate, so the predicate is what this file develops. Mathlib has no notion of order of
growth.

## Main definitions

* `Complex.HasOrderLE f ρ` : `f` has order of growth at most `ρ`.

## Main results

* `Complex.HasOrderLE.mono` : the predicate is monotone in `ρ`.
* `Complex.HasOrderLE.add`, `Complex.HasOrderLE.mul` : closure under sums and products.
* `Complex.hasOrderLE_exp` : `exp` has order at most `1`.

## Implementation notes

Everything rests on one real inequality, `Real.two_rpow_le_add_rpow`: for `0 < a < b` there is
a constant `K` with `2 * x ^ a ≤ K + x ^ b` for all `x ≥ 0`. Its proof is the only place where
the two regimes of `rpow` have to be separated — inside the unit disc the exponent makes the
value smaller, outside it makes it larger — and once it is available every closure property
below is a two-line calculation: a slack of `ε / 2` in the exponent buys both the doubling
needed for products and the room needed for monotonicity, and the constant absorbs `exp K`.
-/

open Real

namespace Real

/-- For `0 < a < b` the function `x ^ b` eventually dominates `2 * x ^ a` by a constant: past
`X = 2 ^ (1 / (b - a))` the factor `x ^ (b - a)` is at least `2`, and below `X` the whole left
side is bounded by `2 * X ^ a`. -/
theorem two_rpow_le_add_rpow {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → 2 * x ^ a ≤ K + x ^ b := by
  have hba : 0 < b - a := sub_pos.2 hab
  set X : ℝ := (2 : ℝ) ^ (1 / (b - a)) with hXdef
  have hXpos : 0 < X := rpow_pos_of_pos (by norm_num) _
  have hX1 : 1 ≤ X := one_le_rpow (by norm_num) (by positivity)
  have hXval : X ^ (b - a) = 2 := by
    rw [hXdef, ← rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      one_div_mul_cancel (ne_of_gt hba), rpow_one]
  refine ⟨2 * X ^ a, by positivity, fun x hx => ?_⟩
  rcases le_or_gt x X with h | h
  · have h1 : x ^ a ≤ X ^ a := rpow_le_rpow hx h ha.le
    have h2 : (0 : ℝ) ≤ x ^ b := rpow_nonneg hx b
    linarith
  · have hxpos : 0 < x := lt_of_lt_of_le hXpos h.le
    have h2 : (2 : ℝ) ≤ x ^ (b - a) := by
      rw [← hXval]
      exact rpow_le_rpow hXpos.le h.le hba.le
    have hsplit : x ^ (b - a) * x ^ a = x ^ b := by
      rw [← rpow_add hxpos]
      ring_nf
    have hxa : (0 : ℝ) < x ^ a := rpow_pos_of_pos hxpos a
    have : 2 * x ^ a ≤ x ^ (b - a) * x ^ a := by nlinarith
    have hK : (0 : ℝ) ≤ 2 * X ^ a := by positivity
    linarith [hsplit ▸ this]

end Real

namespace Complex

/-- `f` has order of growth at most `ρ`: for every `ε > 0` there is `C > 0` with
`‖f z‖ ≤ C * exp (‖z‖ ^ (ρ + ε))` for all `z`. -/
def HasOrderLE (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ C * rexp (‖z‖ ^ (ρ + ε))

variable {f g : ℂ → ℂ} {ρ ρ' : ℝ}

/-- The workhorse: a bound with exponent `a` upgrades to one with any larger exponent `b`,
doubling allowed, at the cost of a constant. -/
private theorem exp_bound_upgrade {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ x → rexp (x ^ a) * rexp (x ^ a) ≤ K * rexp (x ^ b) := by
  obtain ⟨K, hK0, hK⟩ := Real.two_rpow_le_add_rpow ha hab
  refine ⟨rexp K, Real.exp_pos K, fun x hx => ?_⟩
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith [hK x hx])

/-- The predicate is monotone in the order. -/
theorem HasOrderLE.mono (hρ : 0 ≤ ρ) (hle : ρ ≤ ρ') (h : HasOrderLE f ρ) : HasOrderLE f ρ' := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h (ε / 2) (by linarith)
  obtain ⟨K, hK, hKle⟩ := exp_bound_upgrade (a := ρ + ε / 2) (b := ρ' + ε)
    (by linarith) (by linarith)
  refine ⟨C * K, by positivity, fun z => ?_⟩
  have hx := hKle ‖z‖ (norm_nonneg z)
  have hpos : (1 : ℝ) ≤ rexp (‖z‖ ^ (ρ + ε / 2)) :=
    Real.one_le_exp (rpow_nonneg (norm_nonneg z) _)
  have h1 : rexp (‖z‖ ^ (ρ + ε / 2)) ≤ K * rexp (‖z‖ ^ (ρ' + ε)) := by nlinarith
  calc ‖f z‖ ≤ C * rexp (‖z‖ ^ (ρ + ε / 2)) := hbound z
    _ ≤ C * (K * rexp (‖z‖ ^ (ρ' + ε))) := by gcongr
    _ = C * K * rexp (‖z‖ ^ (ρ' + ε)) := by ring

theorem hasOrderLE_const (c : ℂ) (ρ : ℝ) : HasOrderLE (fun _ => c) ρ := by
  intro ε _
  refine ⟨‖c‖ + 1, by positivity, fun z => ?_⟩
  have h1 : (1 : ℝ) ≤ rexp (‖z‖ ^ (ρ + ε)) :=
    Real.one_le_exp (rpow_nonneg (norm_nonneg z) _)
  nlinarith [norm_nonneg c]

theorem HasOrderLE.add (hf : HasOrderLE f ρ) (hg : HasOrderLE g ρ) :
    HasOrderLE (fun z => f z + g z) ρ := by
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hf ε hε
  obtain ⟨C₂, hC₂, h₂⟩ := hg ε hε
  refine ⟨C₁ + C₂, by positivity, fun z => ?_⟩
  refine (norm_add_le _ _).trans ?_
  have a₁ := h₁ z
  have a₂ := h₂ z
  nlinarith [Real.exp_pos (‖z‖ ^ (ρ + ε))]

/-- A product of two functions of order at most `ρ` again has order at most `ρ`. The two
exponentials multiply, and the `ε / 2` of slack in the exponent pays for the doubling. -/
theorem HasOrderLE.mul (hρ : 0 ≤ ρ) (hf : HasOrderLE f ρ) (hg : HasOrderLE g ρ) :
    HasOrderLE (fun z => f z * g z) ρ := by
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hf (ε / 2) (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := hg (ε / 2) (by linarith)
  obtain ⟨K, hK, hKle⟩ := exp_bound_upgrade (a := ρ + ε / 2) (b := ρ + ε)
    (by linarith) (by linarith)
  refine ⟨C₁ * C₂ * K, by positivity, fun z => ?_⟩
  rw [norm_mul]
  have a₁ := h₁ z
  have a₂ := h₂ z
  have hx := hKle ‖z‖ (norm_nonneg z)
  have hp₁ : (0 : ℝ) ≤ ‖f z‖ := norm_nonneg _
  have hp₂ : (0 : ℝ) ≤ ‖g z‖ := norm_nonneg _
  have hstep : ‖f z‖ * ‖g z‖
      ≤ (C₁ * rexp (‖z‖ ^ (ρ + ε / 2))) * (C₂ * rexp (‖z‖ ^ (ρ + ε / 2))) := by
    apply mul_le_mul a₁ a₂ hp₂
    positivity
  calc ‖f z‖ * ‖g z‖
      ≤ (C₁ * rexp (‖z‖ ^ (ρ + ε / 2))) * (C₂ * rexp (‖z‖ ^ (ρ + ε / 2))) := hstep
    _ = C₁ * C₂ * (rexp (‖z‖ ^ (ρ + ε / 2)) * rexp (‖z‖ ^ (ρ + ε / 2))) := by ring
    _ ≤ C₁ * C₂ * (K * rexp (‖z‖ ^ (ρ + ε))) := by gcongr
    _ = C₁ * C₂ * K * rexp (‖z‖ ^ (ρ + ε)) := by ring

/-- `exp` has order at most `1`. -/
theorem hasOrderLE_exp : HasOrderLE exp 1 := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := Real.two_rpow_le_add_rpow (a := 1) (b := 1 + ε) one_pos (by linarith)
  refine ⟨rexp K, Real.exp_pos K, fun z => ?_⟩
  have hre : z.re ≤ ‖z‖ := re_le_norm z
  have h1 : ‖z‖ ^ (1 : ℝ) = ‖z‖ := rpow_one _
  have h2 := hK ‖z‖ (norm_nonneg z)
  rw [h1] at h2
  rw [Complex.norm_exp, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith [norm_nonneg z]

end Complex
