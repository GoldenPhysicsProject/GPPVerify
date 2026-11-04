import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# Golden cross-ratio conjugacy and the natural prime dilations as Möbius maps

Source: Codex/Discovery2, `work/codex/2026-11-04_golden_unitary_crossratio_no_go.md` and
`work/codex/2026-11-04_natural_prime_golden_noncommuting_addendum.md` (GPP-bridge). Daniel Toupin /
Golden Physics Project, with AI assistance from Codex (statements) and Claude Code (formalization).

Real-variable algebra only:

* `cross_ratio_conj`: for `ρ² = aρ + 1`, `F_a(x) = a + 1/x` and `C(x) = (x − ρ)/(x + 1/ρ)` satisfy
  `C(F_a(x)) = −ρ⁻² · C(x)`; `golden_cross_ratio_conj` is the case `a = 1`, `ρ = φ`.
* `prime_mobius_conj`: the dilation `x ↦ p x` transported by `C` is the Möbius map
  `P_p(y) = (A + B y)/(C + D y)` with `A = φ(p−1)`, `B = φ + p/φ`, `C = pφ + 1/φ`, `D = (p−1)/φ`.
* `prime_det`: `B·C − A·D = 5p` (for `φ² = φ + 1`); `hasDerivAt_P`: `P_p' = 5p/(C + D y)²`.
* `prime_golden_noncommute`: for `p > 1` the golden map `G(y) = −φ⁻² y` and `P_p` do not commute at
  `y = 0`.

**Scope.** The unitarity of `W_h f(y) = √|y h'(y)/h(y)| f(h(y))` on `L²(ℝ^×, dy/|y|)`, the two-sheet
`L²(ℝ)` shift, the no-point-spectrum theorem, the identification with Hecke/completed primes and
every numerical regression are NOT formalized. Non-commutation does not produce a discrete spectrum
and nothing here selects zeta zeros. No claim about RH.
-/

set_option autoImplicit false

namespace GppGoldenPrimeAction

/-- The cross-ratio coordinate `C(x) = (x − ρ)/(x + 1/ρ)`. -/
noncomputable def crossRatio (ρ x : ℝ) : ℝ := (x - ρ) / (x + 1 / ρ)

theorem cross_ratio_conj {a ρ x : ℝ} (hρ : ρ ≠ 0) (hq : ρ ^ 2 = a * ρ + 1)
    (hx : x ≠ 0) (hxψ : x + 1 / ρ ≠ 0) :
    crossRatio ρ (a + 1 / x) = -(1 / ρ ^ 2) * crossRatio ρ x := by
  have ha : a = (ρ ^ 2 - 1) / ρ := eq_div_of_mul_eq hρ (by linarith)
  have h1 : ρ * x + 1 ≠ 0 := by
    intro h; apply hxψ
    have : x + 1 / ρ = (ρ * x + 1) / ρ := by field_simp
    rw [this, h, zero_div]
  have e1 : a + 1 / x - ρ = (ρ - x) / (x * ρ) := by rw [ha]; field_simp; ring
  have e2 : a + 1 / x + 1 / ρ = (ρ * x + 1) / x := by rw [ha]; field_simp; ring
  have h3 : x + 1 / ρ = (ρ * x + 1) / ρ := by field_simp
  unfold crossRatio
  rw [e1, e2, h3]
  field_simp
  ring

theorem golden_cross_ratio_conj {φ x : ℝ} (hφ : φ ≠ 0) (hsq : φ ^ 2 = φ + 1)
    (hx : x ≠ 0) (hxψ : x + 1 / φ ≠ 0) :
    crossRatio φ (1 + 1 / x) = -(1 / φ ^ 2) * crossRatio φ x :=
  cross_ratio_conj (a := 1) hφ (by linarith) hx hxψ

/-- The transported prime dilation as a Möbius map. -/
noncomputable def primeMobius (φ p y : ℝ) : ℝ :=
  (φ * (p - 1) + (φ + p / φ) * y) / (p * φ + 1 / φ + ((p - 1) / φ) * y)

theorem prime_mobius_conj {φ p x : ℝ} (hφ : φ ≠ 0)
    (hx : x + 1 / φ ≠ 0) (hpx : p * x + 1 / φ ≠ 0) :
    primeMobius φ p (crossRatio φ x) = crossRatio φ (p * x) := by
  have hx' : φ * x + 1 ≠ 0 := by
    intro h; apply hx
    have : x + 1 / φ = (φ * x + 1) / φ := by field_simp
    rw [this, h, zero_div]
  have hpx' : φ * (p * x) + 1 ≠ 0 := by
    intro h; apply hpx
    have : p * x + 1 / φ = (φ * (p * x) + 1) / φ := by field_simp
    rw [this, h, zero_div]
  have eD : p * φ + 1 / φ + ((p - 1) / φ) * ((x - φ) / (x + 1 / φ))
      = (φ + 1 / φ) * (p * x + 1 / φ) / (x + 1 / φ) := by
    field_simp; ring
  have eN : φ * (p - 1) + (φ + p / φ) * ((x - φ) / (x + 1 / φ))
      = (φ + 1 / φ) * (p * x - φ) / (x + 1 / φ) := by
    field_simp; ring
  unfold primeMobius crossRatio
  rw [eN, eD]
  field_simp

theorem prime_det {φ p : ℝ} (hφ : φ ≠ 0) (hsq : φ ^ 2 = φ + 1) :
    (φ + p / φ) * (p * φ + 1 / φ) - φ * (p - 1) * ((p - 1) / φ) = 5 * p := by
  have h : 1 / φ = φ - 1 := by
    rw [div_eq_iff hφ]; nlinarith
  have h1 : p / φ = p * (φ - 1) := by rw [div_eq_mul_one_div, h]
  have h2 : (p - 1) / φ = (p - 1) * (φ - 1) := by rw [div_eq_mul_one_div, h]
  rw [h1, h2, h]
  linear_combination (4 * p) * hsq

theorem hasDerivAt_P {φ p y : ℝ} (hφ : φ ≠ 0) (hsq : φ ^ 2 = φ + 1)
    (hy : p * φ + 1 / φ + ((p - 1) / φ) * y ≠ 0) :
    HasDerivAt (primeMobius φ p) (5 * p / (p * φ + 1 / φ + ((p - 1) / φ) * y) ^ 2) y := by
  have hnum : HasDerivAt (fun y : ℝ => φ * (p - 1) + (φ + p / φ) * y) (φ + p / φ) y := by
    simpa using ((hasDerivAt_id y).const_mul (φ + p / φ)).const_add (φ * (p - 1))
  have hden : HasDerivAt (fun y : ℝ => p * φ + 1 / φ + ((p - 1) / φ) * y) ((p - 1) / φ) y := by
    simpa using ((hasDerivAt_id y).const_mul ((p - 1) / φ)).const_add (p * φ + 1 / φ)
  have h := hnum.div hden hy
  have hd := prime_det (p := p) hφ hsq
  unfold primeMobius
  refine h.congr_deriv ?_
  congr 1
  linear_combination hd

noncomputable def goldenG (φ y : ℝ) : ℝ := -(1 / φ ^ 2) * y

theorem prime_golden_noncommute {φ p : ℝ} (hφ : 0 < φ) (hp : 1 < p) :
    goldenG φ (primeMobius φ p 0) ≠ primeMobius φ p (goldenG φ 0) := by
  have hpos : 0 < primeMobius φ p 0 := by
    unfold primeMobius
    have h1 : 0 < φ * (p - 1) := mul_pos hφ (by linarith)
    have h2 : 0 < p * φ + 1 / φ := by
      have : 0 < p := by linarith
      positivity
    simpa using div_pos h1 h2
  have h0 : goldenG φ 0 = 0 := by simp [goldenG]
  rw [h0]
  intro h
  have hneg : goldenG φ (primeMobius φ p 0) < 0 := by
    unfold goldenG
    have : 0 < 1 / φ ^ 2 := by positivity
    nlinarith
  linarith

end GppGoldenPrimeAction
