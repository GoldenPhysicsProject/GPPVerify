import GppVerify.RiemannHypothesis.HeatTraceCriterion
import GppVerify.RiemannHypothesis.GammaPlancherelDefect
import GppVerify.RiemannHypothesis.WeilSupportLadder

/-!
# Arithmetic Weil pairing of the heat Gaussian

`𝒲 = ν_∞ − ν_p` is defined here as a pairing on test functions, with no zeros in
the definition.

* `ν_p` is Thread L's `GppWeilLadder.primeSide` (von Mangoldt on `± log n`).
* `ν_∞` is the real-place Plancherel density of `GammaPlancherelDefect` at the
  critical tilt `q = 1/2`, paired against the even part of the test function.

The heat object is then the paper's kernel with those two sides filled in:

  `𝒦(t) = (4πt)^{-1/2} ⟨𝒲, exp(−x²/(4t))⟩`.

What this file proves: the pairing is exactly arch minus primes; on the heat
Gaussian the prime side is a nonnegative von Mangoldt sum (already identified
with Thread L by `primeSide_heatGaussian`); below `log 2` the primes drop out
and the pairing is the archimedean side on the nose.

What this file does not prove: complete monotonicity of `𝒦`, RH, or exact
truncation of the heat Gaussian (it is not compactly supported).
-/

namespace GppArithmeticWeil

open MeasureTheory Set ArithmeticFunction GppHeatTrace GppWeilLadder GppGammaPlancherel

/-- Archimedean pairing: real-place density at `q = 1/2` against the even part. -/
noncomputable def archSide (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Ioi (0 : ℝ), density (1 / 2) x * (f x + f (-x))

/-- Signed Weil pairing. No zeros enter the definition. -/
noncomputable def weilPairing (f : ℝ → ℝ) : ℝ :=
  archSide f - primeSide f

/-- Gaussian prefactor of the heat kernel. -/
noncomputable def heatPreFactor (t : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t)

/-- The arithmetic heat trace. -/
noncomputable def heatTrace (t : ℝ) : ℝ :=
  heatPreFactor t * weilPairing (heatGaussian t)

/-- Prefactor is positive for `t > 0`. -/
theorem heatPreFactor_pos {t : ℝ} (ht : 0 < t) : 0 < heatPreFactor t := by
  unfold heatPreFactor
  positivity

/-- Even test functions pair as twice the density times `f`. -/
theorem archSide_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) :
    archSide f = ∫ x : ℝ in Ioi (0 : ℝ), density (1 / 2) x * (2 * f x) := by
  unfold archSide
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _
  rw [hf x]
  ring

/-- Heat Gaussian is even, so the archimedean side collapses to twice `f`. -/
theorem archSide_heatGaussian (t : ℝ) :
    archSide (heatGaussian t) =
      ∫ x : ℝ in Ioi (0 : ℝ), density (1 / 2) x * (2 * heatGaussian t x) :=
  archSide_even (fun x => heatGaussian_even t x)

/-- By definition. -/
theorem heatTrace_def (t : ℝ) :
    heatTrace t = heatPreFactor t * (archSide (heatGaussian t) - primeSide (heatGaussian t)) :=
  rfl

/-- The prime side of the heat pairing is a nonnegative von Mangoldt sum. -/
theorem primeSide_heatGaussian_nonneg (t : ℝ) :
    0 ≤ primeSide (heatGaussian t) := by
  have hterm : ∀ n : ℕ,
      0 ≤ (Λ n / Real.sqrt n) * (heatGaussian t (Real.log n) + heatGaussian t (-Real.log n)) := by
    intro n
    have hΛ : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg n
    have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hden : 0 ≤ Λ n / Real.sqrt n := div_nonneg hΛ hs
    have hpos : 0 ≤ heatGaussian t (Real.log n) + heatGaussian t (-Real.log n) := by
      have h1 : 0 ≤ heatGaussian t (Real.log n) := Real.exp_nonneg _
      have h2 : 0 ≤ heatGaussian t (-Real.log n) := Real.exp_nonneg _
      linarith
    exact mul_nonneg hden hpos
  exact tsum_nonneg hterm

/-- Below the first prime rung the pairing is the archimedean side. -/
theorem weilPairing_rung_zero {f : ℝ → ℝ} {L : ℝ}
    (hf : HasSupportIn f L) (hL : L < Real.log 2) :
    weilPairing f = archSide f := by
  unfold weilPairing
  rw [primeSide_eq_zero_of_support_lt_log_two hf hL, sub_zero]

/-- Heat-trace positivity is archimedean dominance of the prime pairing. -/
theorem heatTrace_nonneg_iff {t : ℝ} (ht : 0 < t) :
    0 ≤ heatTrace t ↔ primeSide (heatGaussian t) ≤ archSide (heatGaussian t) := by
  unfold heatTrace weilPairing
  constructor
  · intro h
    have hp := heatPreFactor_pos ht
    have : 0 ≤ archSide (heatGaussian t) - primeSide (heatGaussian t) := by
      exact (mul_nonneg_iff_of_pos_left hp).mp h
    linarith
  · intro h
    exact mul_nonneg (heatPreFactor_pos ht).le (sub_nonneg.mpr h)

end GppArithmeticWeil
