/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity
import Mathlib.Data.Nat.Prime.Int


/-!
# The Weil form, place by place (GW1, GW5)

The tree's Weil form `weilForm g = poleTerm g + archimedeanTerm g - primeSide g`
(`GppArithmeticReflection`) splits as a global pole term plus one term per place of `ℚ`:

  `weilForm g = W_pole g + W_inf g + ∑' p, W_fin p g`   (`weilForm_eq_pole_add_places`),

where `W_fin p` collects the prime powers `p^(k+1)` of `primeSide`. The pole term is kept
global, not folded into a place. The only input is summability of the prime side; the
regrouping uses injectivity of `(p, k) ↦ p^(k+1)` (`Nat.Prime.pow_inj`) and the fact that
`Λ` is supported on prime powers. `weilForm_add_smul` is linearity on `WeilAdmissible`
test functions (integrable pole and archimedean integrands, summable prime side).

**Scope.** These statements concern the arithmetic-side functional `weilForm` of
`ArithmeticReflectionPositivity` only. They are not quoted against
`GppWeilCriterion.rh_iff_weil_pairedForm_nonneg`, whose object is a finite form on sets of
zeros: the link between the two is the explicit formula (GW-EF), which is open.

Governing specification: Principal series's global Tate statement sheet (GPP-bridge branch
`principal-series/global-tate-statements` at `77d5b43`, §6.3, GW1 and GW5), audited PASS by
Turbo (GPP-bridge PR #11, comment 6725245671).
-/

open ArithmeticFunction GppArithmeticReflection GppArchimedeanFloor GppWeilLadder
open MeasureTheory Set

namespace GlobalTate.Weil

/-- The prime-power index map `(p, k) ↦ p^(k+1)`. -/
def primePow (pk : Nat.Primes × ℕ) : ℕ := (pk.1 : ℕ) ^ (pk.2 + 1)

theorem primePow_injective : Function.Injective primePow := by
  rintro ⟨p, k⟩ ⟨q, l⟩ h
  obtain ⟨hpq, hkl⟩ := Nat.Prime.pow_inj p.2 q.2 h
  simp only [Prod.mk.injEq]
  exact ⟨Subtype.ext hpq, hkl⟩

/-- A sequence vanishing wherever `Λ` does is supported on prime powers. -/
theorem support_subset_primePow {b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0 → Λ n ≠ 0) :
    Function.support b ⊆ Set.range primePow := by
  intro n hn
  have hΛ : Λ n ≠ 0 := hb n hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  exact ⟨(⟨p, hp⟩, j), rfl⟩

/-- The `n`-th summand of `primeSide`. -/
noncomputable def primeTerm (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  (Λ n / Real.sqrt n) * (g (Real.log n) + g (-(Real.log n)))

/-- Global boundary (pole) term: not a place. -/
noncomputable def W_pole (g : ℝ → ℝ) : ℝ := poleTerm g

/-- Archimedean place, trivial character. -/
noncomputable def W_inf (g : ℝ → ℝ) : ℝ := archimedeanTerm g

/-- Finite place `p`: the prime-power part of `primeSide` at `p`, with the tree's sign. -/
noncomputable def W_fin (p : Nat.Primes) (g : ℝ → ℝ) : ℝ :=
  -∑' k : ℕ, primeTerm g ((p : ℕ) ^ (k + 1))

/-- **GW1.** The Weil form splits as the global pole term plus one term per place. -/
theorem weilForm_eq_pole_add_places (g : ℝ → ℝ) (hsum : Summable (primeTerm g)) :
    weilForm g = W_pole g + W_inf g + ∑' p : Nat.Primes, W_fin p g := by
  have hsupp : Function.support (primeTerm g) ⊆ Set.range primePow :=
    support_subset_primePow fun n hn hΛ => hn (by simp [primeTerm, hΛ])
  have hprime : primeSide g = ∑' p : Nat.Primes, ∑' k : ℕ, primeTerm g ((p : ℕ) ^ (k + 1)) := by
    have h1 : primeSide g = ∑' n, primeTerm g n := rfl
    rw [h1, ← primePow_injective.tsum_eq hsupp]
    exact (hsum.comp_injective primePow_injective).tsum_prod
  simp only [weilForm, W_pole, W_inf, W_fin, tsum_neg, hprime]
  ring

/-- Integrability and summability making every term of `weilForm g` a genuine integral or
sum. -/
structure WeilAdmissible (g : ℝ → ℝ) : Prop where
  pole : Integrable (fun u => g u * (2 * Real.cosh (u / 2)))
  arch : IntegrableOn (archimedeanIntegrand g) (Ioi 0)
  prime : Summable (primeTerm g)

/-- **GW5.** Linearity of the Weil form on admissible test functions. -/
theorem weilForm_add_smul (a : ℝ) {g₁ g₂ : ℝ → ℝ} (h₁ : WeilAdmissible g₁)
    (h₂ : WeilAdmissible g₂) :
    weilForm (a • g₁ + g₂) = a * weilForm g₁ + weilForm g₂ := by
  have hpole : poleTerm (a • g₁ + g₂) = a * poleTerm g₁ + poleTerm g₂ := by
    have hf : (fun u => (a • g₁ + g₂) u * (2 * Real.cosh (u / 2))) =
        fun u => a * (g₁ u * (2 * Real.cosh (u / 2))) + g₂ u * (2 * Real.cosh (u / 2)) := by
      funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    unfold poleTerm
    rw [hf, integral_add (h₁.pole.const_mul a) h₂.pole, integral_const_mul]
  have harch : archimedeanTerm (a • g₁ + g₂) = a * archimedeanTerm g₁ + archimedeanTerm g₂ := by
    have hf : archimedeanIntegrand (a • g₁ + g₂) =
        fun u => a * archimedeanIntegrand g₁ u + archimedeanIntegrand g₂ u := by
      funext u
      simp only [archimedeanIntegrand, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    unfold archimedeanTerm
    rw [hf, integral_add (h₁.arch.const_mul a) h₂.arch, integral_const_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hprime : primeSide (a • g₁ + g₂) = a * primeSide g₁ + primeSide g₂ := by
    have e : ∀ g, primeSide g = ∑' n, primeTerm g n := fun _ => rfl
    have hf : primeTerm (a • g₁ + g₂) = fun n => a * primeTerm g₁ n + primeTerm g₂ n := by
      funext n; simp only [primeTerm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, e, e, hf, (h₁.prime.mul_left a).tsum_add h₂.prime, tsum_mul_left]
  simp only [weilForm, hpole, harch, hprime]
  ring

end GlobalTate.Weil
