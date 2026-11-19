/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Elementary identities from GPPDiscovery5 Rounds 15–22 (batch 1)

Formalization of the elementary claims sent by Heart of the Cosmos (Grok, GPPDiscovery5) on
2026-11-19 (bridge `CONVERSATION-week-025`, "Formalization requests from Heart (Rounds 15–22)").
Claim numbers and the `HR<round>_` names follow that entry. Each statement is stated in Lean
exactly as filed, except where a hypothesis had to be made explicit; such places are marked
**(hypothesis made explicit)**.

* #1  `HR15_hasse_form_identity`, `HR15_hasse_sign_iff`, `HR15_hasse_roots_unit_iff`
* #2  `HR15_toeplitz_gram_psd`
* #4  `HR15_pole_shift`
* #16 `HR16_dh_not_multiplicative` (the Davenport–Heilbronn-type coefficient table)
* #17 `HR20_P0_eq`, `HR20_P1_eq`, `HR20_pick_psd` (the two Pick/Gram identities with their diagonals, and PSD)
* #27 `HR22_euler_factor_density_pos_at_zero`, `HR22_euler_factor_density_neg_at_pi`
* #32 `HR22_hb_multiset`, `HR22_hermite_biehler_finite` (**hypothesis made explicit: nonconstant** — for a
  constant polynomial the two sides of the inequality are equal)

Nothing here concerns zeta zeros or RH; all statements are unconditional finite algebra or
elementary calculus. No `sorry`, no `axiom`.
-/

namespace GppHeartElementary

open Matrix Complex
open scoped ComplexConjugate ComplexOrder

/-! ## #1 Hasse form -/

/-- **#1 (identity).** For `q > 0`, `v = (m, −n√q)` and `T = [[2, a/√q],[a/√q, 2]]`,
`vᵀ T v = 2 (m² − a m n + q n²)`. -/
theorem HR15_hasse_form_identity (a q m n : ℝ) (hq : 0 < q) :
    (![m, -n * Real.sqrt q] : Fin 2 → ℝ) ⬝ᵥ
      ((!![2, a / Real.sqrt q; a / Real.sqrt q, 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
        ![m, -n * Real.sqrt q]) = 2 * (m ^ 2 - a * m * n + q * n ^ 2) := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  nlinarith [hsq]

/-- **#1 (sign).** `m² − a m n + q n² ≥ 0` for all real `m n` iff `a² ≤ 4 q`. -/
theorem HR15_hasse_sign_iff (a q : ℝ) :
    (∀ m n : ℝ, 0 ≤ m ^ 2 - a * m * n + q * n ^ 2) ↔ a ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have := h a 2
    nlinarith
  · intro h m n
    nlinarith [sq_nonneg (m - a * n / 2), sq_nonneg n, mul_nonneg (sub_nonneg.mpr h) (sq_nonneg n)]

/-- **#1 (roots).** For `q > 0`: `a² ≤ 4 q` iff every complex root `α` of `X² − a X + q` has
`|α| = √q`. -/
theorem HR15_hasse_roots_unit_iff (a q : ℝ) (hq : 0 < q) :
    a ^ 2 ≤ 4 * q ↔ ∀ α : ℂ, α ^ 2 - (a : ℂ) * α + (q : ℂ) = 0 → ‖α‖ = Real.sqrt q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  constructor
  · intro h α hα
    have hre := congrArg Complex.re hα
    have him := congrArg Complex.im hα
    simp [pow_two] at hre him
    -- him : 2 * α.re * α.im - a * α.im = 0
    have hnorm : ‖α‖ ^ 2 = q := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      by_cases hy : α.im = 0
      · rw [hy] at hre ⊢
        nlinarith [sq_nonneg (α.re - a / 2)]
      · have hx : 2 * α.re - a = 0 := by
          have : α.im * (2 * α.re - a) = 0 := by linarith
          rcases mul_eq_zero.mp this with h0 | h0
          · exact absurd h0 hy
          · exact h0
        have hx' : α.re = a / 2 := by linarith
        rw [hx'] at hre ⊢
        nlinarith
    have : ‖α‖ = Real.sqrt q := by
      rw [← hnorm]; exact (Real.sqrt_sq (norm_nonneg α)).symm
    exact this
  · intro h
    by_contra hlt
    have hlt := not_le.mp hlt
    -- real roots r, s with r s = q, r ≠ s, both of modulus √q: contradiction
    set d := Real.sqrt (a ^ 2 - 4 * q) with hd
    have hdpos : 0 < d := Real.sqrt_pos.mpr (by linarith)
    have hd2 : d ^ 2 = a ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
    have hr := h (((a + d) / 2 : ℝ) : ℂ) (by
      push_cast
      have : ((a : ℂ) + (d : ℂ)) ^ 2 / 4 - (a : ℂ) * ((a + d) / 2) + (q : ℂ) = 0 := by
        have h2 : ((d : ℝ) : ℂ) ^ 2 = (a : ℂ) ^ 2 - 4 * (q : ℂ) := by
          exact_mod_cast hd2
        linear_combination (1 / 4 : ℂ) * h2
      linear_combination this)
    have hs' := h (((a - d) / 2 : ℝ) : ℂ) (by
      push_cast
      have : ((a : ℂ) - (d : ℂ)) ^ 2 / 4 - (a : ℂ) * ((a - d) / 2) + (q : ℂ) = 0 := by
        have h2 : ((d : ℝ) : ℂ) ^ 2 = (a : ℂ) ^ 2 - 4 * (q : ℂ) := by
          exact_mod_cast hd2
        linear_combination (1 / 4 : ℂ) * h2
      linear_combination this)
    rw [Complex.norm_real, Real.norm_eq_abs] at hr hs'
    have habs : |(a + d) / 2| ^ 2 = |(a - d) / 2| ^ 2 := by rw [hr, hs']
    rw [sq_abs, sq_abs] at habs
    nlinarith [habs, hdpos]

/-! ## #2 Toeplitz Gram -/

/-- **#2.** For `ω₁,…,ω_m ∈ ℂ` of modulus one, the Toeplitz matrix
`T[j,k] = Σᵢ ωᵢ^{k−j}` is Hermitian positive semidefinite (the Gram matrix of `(ωᵢ^k)_k`). -/
theorem HR15_toeplitz_gram_psd {ι : Type*} [Fintype ι] (ω : ι → ℂ) (hω : ∀ i, ‖ω i‖ = 1)
    (N : ℕ) :
    (Matrix.of fun j k : Fin N => ∑ i, (ω i) ^ ((k : ℤ) - (j : ℤ))).PosSemidef := by
  let V : Matrix ι (Fin N) ℂ := Matrix.of fun i k => (ω i) ^ (k : ℕ)
  have key : (Matrix.of fun j k : Fin N => ∑ i, (ω i) ^ ((k : ℤ) - (j : ℤ))) = Vᴴ * V := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, V]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : ω i ≠ 0 := by
      intro h0; have := hω i; rw [h0] at this; simp at this
    have hconj : conj (ω i) = (ω i)⁻¹ := by
      have h1 : ω i * conj (ω i) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω i]; simp
      exact (eq_inv_of_mul_eq_one_right h1)
    have hz : (ω i) ^ ((k : ℤ) - (j : ℤ)) = ω i ^ (k : ℕ) * ((ω i) ^ (j : ℕ))⁻¹ := by
      rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    rw [hz, star_pow, Complex.star_def, hconj, inv_pow]
    ring
  rw [key]
  exact Matrix.posSemidef_conjTranspose_mul_self V

/-! ## #4 Pole shift -/

/-- **#4 (general exponent).** `∫ g(u − s) e^{c u} du = e^{c s} ∫ g(u) e^{c u} du`; this is the
substitution `u ↦ u + s`, valid for every `g` (no integrability needed: both sides are the same
integral under a measure-preserving translation). -/
theorem HR15_shift_exp (g : ℝ → ℂ) (s c : ℝ) :
    ∫ u : ℝ, g (u - s) * Complex.exp ((c : ℂ) * u)
      = Complex.exp ((c : ℂ) * s) * ∫ u : ℝ, g u * Complex.exp ((c : ℂ) * u) := by
  have h : ∫ u : ℝ, g (u - s) * Complex.exp ((c : ℂ) * u)
      = ∫ u : ℝ, g u * Complex.exp ((c : ℂ) * (u + s)) := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun u : ℝ => g (u - s) * Complex.exp ((c : ℂ) * u)) s]
    simp
  rw [h, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_add, Complex.exp_add]
  ring

/-- **#4.** The two pole moments `c_±(g) = ∫ g(u) e^{±u/2} du` of the translate `τ_s g`:
`c_±(τ_s g) = e^{±s/2} c_±(g)`. -/
theorem HR15_pole_shift (g : ℝ → ℂ) (s : ℝ) :
    (∫ u : ℝ, g (u - s) * Complex.exp (((1 / 2 : ℝ) : ℂ) * u)
        = Complex.exp (((1 / 2 : ℝ) : ℂ) * s) * ∫ u : ℝ, g u * Complex.exp (((1 / 2 : ℝ) : ℂ) * u))
    ∧ (∫ u : ℝ, g (u - s) * Complex.exp (((-1 / 2 : ℝ) : ℂ) * u)
        = Complex.exp (((-1 / 2 : ℝ) : ℂ) * s) *
            ∫ u : ℝ, g u * Complex.exp (((-1 / 2 : ℝ) : ℂ) * u)) :=
  ⟨HR15_shift_exp g s (1 / 2), HR15_shift_exp g s (-1 / 2)⟩

/-! ## #16 The coefficient table is not multiplicative -/

/-- `κ = (√(10 − 2√5) − 2)/(√5 − 1)`. -/
noncomputable def HR16_kappa : ℝ :=
  (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)

/-- The 5-periodic coefficient `a(n) = (0, 1, κ, −κ, −1)[n mod 5]`. -/
noncomputable def HR16_a (n : ℕ) : ℝ :=
  (![0, 1, HR16_kappa, -HR16_kappa, -1] : Fin 5 → ℝ) ⟨n % 5, Nat.mod_lt _ (by norm_num)⟩

theorem HR16_a_periodic (n : ℕ) : HR16_a (n + 5) = HR16_a n := by
  unfold HR16_a
  congr 1
  ext
  simp [Nat.add_mod_right]

/-- Oddness: `a(5 − r) = −a(r)` for `1 ≤ r ≤ 4`. -/
theorem HR16_a_odd (r : ℕ) (h1 : 1 ≤ r) (h4 : r ≤ 4) : HR16_a (5 - r) = -HR16_a r := by
  interval_cases r <;> simp [HR16_a]

/-- **#16.** `a(6) = 1` but `a(2) a(3) = −κ² ≤ 0`, so `a` is not multiplicative. -/
theorem HR16_dh_not_multiplicative : HR16_a 6 ≠ HR16_a 2 * HR16_a 3 := by
  have h6 : HR16_a 6 = 1 := by simp [HR16_a]
  have h2 : HR16_a 2 = HR16_kappa := by simp [HR16_a]
  have h3 : HR16_a 3 = -HR16_kappa := by simp [HR16_a]
  rw [h6, h2, h3]
  nlinarith [sq_nonneg HR16_kappa]

/-! ## #27 Euler-factor density signs -/

/-- `R(φ) = Re [ q e^{−iφ} / (1 − q e^{−iφ}) ]`. -/
noncomputable def HR22_eulerFactorDensity (q φ : ℝ) : ℝ :=
  (((q : ℂ) * Complex.exp (-(φ : ℂ) * Complex.I)) /
    (1 - (q : ℂ) * Complex.exp (-(φ : ℂ) * Complex.I))).re

/-- **#27.** `R(0) = q/(1 − q) > 0` for `q ∈ (0,1)`. -/
theorem HR22_euler_factor_density_pos_at_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HR22_eulerFactorDensity q 0 = q / (1 - q) ∧ 0 < HR22_eulerFactorDensity q 0 := by
  have h : HR22_eulerFactorDensity q 0 = q / (1 - q) := by
    unfold HR22_eulerFactorDensity
    have : (((q : ℂ) * Complex.exp (-((0 : ℝ) : ℂ) * Complex.I)) /
        (1 - (q : ℂ) * Complex.exp (-((0 : ℝ) : ℂ) * Complex.I))) = ((q / (1 - q) : ℝ) : ℂ) := by
      simp
    rw [this, Complex.ofReal_re]
  exact ⟨h, by rw [h]; exact div_pos hq0 (by linarith)⟩

/-- **#27.** `R(π) = −q/(1 + q) < 0` for `q ∈ (0,1)`. -/
theorem HR22_euler_factor_density_neg_at_pi {q : ℝ} (hq0 : 0 < q) :
    HR22_eulerFactorDensity q Real.pi = -q / (1 + q) ∧ HR22_eulerFactorDensity q Real.pi < 0 := by
  have h : HR22_eulerFactorDensity q Real.pi = -q / (1 + q) := by
    unfold HR22_eulerFactorDensity
    have he : Complex.exp (-(Real.pi : ℂ) * Complex.I) = -1 := by
      rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    have : (((q : ℂ) * Complex.exp (-(Real.pi : ℂ) * Complex.I)) /
        (1 - (q : ℂ) * Complex.exp (-(Real.pi : ℂ) * Complex.I))) = ((-q / (1 + q) : ℝ) : ℂ) := by
      rw [he]
      have h1 : (1 - (q : ℂ) * -1) = 1 + (q : ℂ) := by ring
      rw [h1]
      push_cast
      ring
    rw [this, Complex.ofReal_re]
  exact ⟨h, by rw [h]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)⟩

/-! ## #17 Pick Gram identities -/

section Pick

variable {k n : ℕ}

/-- `m(u) = Σᵣ wᵣ/(tᵣ + u)`. -/
noncomputable def HR20_m (w t : Fin k → ℝ) (u : ℝ) : ℝ := ∑ r, w r / (t r + u)

/-- The vectors `vᵣ(i) = 1/(tᵣ + uᵢ)`. -/
noncomputable def HR20_v (t : Fin k → ℝ) (u : Fin n → ℝ) (r : Fin k) : Fin n → ℝ :=
  fun i => 1 / (t r + u i)

/-- `P0ᵢⱼ = (m(uᵢ) − m(uⱼ))/(uⱼ − uᵢ)` off the diagonal, `−m′(uᵢ)` on it. -/
noncomputable def HR20_P0 (w t : Fin k → ℝ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then -deriv (HR20_m w t) (u i)
    else (HR20_m w t (u i) - HR20_m w t (u j)) / (u j - u i)

/-- `P1ᵢⱼ = (uᵢ m(uᵢ) − uⱼ m(uⱼ))/(uᵢ − uⱼ)` off the diagonal, `(u m)′(uᵢ)` on it. -/
noncomputable def HR20_P1 (w t : Fin k → ℝ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then deriv (fun x => x * HR20_m w t x) (u i)
    else (u i * HR20_m w t (u i) - u j * HR20_m w t (u j)) / (u i - u j)

private theorem hasDerivAt_m (w t : Fin k → ℝ) {x : ℝ} (hx : ∀ r, t r + x ≠ 0) :
    HasDerivAt (HR20_m w t) (-∑ r, w r / (t r + x) ^ 2) x := by
  have h : ∀ r ∈ (Finset.univ : Finset (Fin k)),
      HasDerivAt (fun y : ℝ => w r / (t r + y)) (-(w r / (t r + x) ^ 2)) x := by
    intro r _
    have h1 : HasDerivAt (fun y : ℝ => t r + y) 1 x := (hasDerivAt_id x).const_add (t r)
    exact ((hasDerivAt_const x (w r)).div h1 (hx r)).congr_deriv (by ring)
  have := HasDerivAt.fun_sum h
  exact this.congr_deriv (by simp [Finset.sum_neg_distrib])

/-- **#17 (P0).** `P0 = Σᵣ wᵣ vᵣ vᵣᵀ`. -/
theorem HR20_P0_eq (w t : Fin k → ℝ) (u : Fin n → ℝ) (hu : Function.Injective u)
    (hne : ∀ r i, t r + u i ≠ 0) :
    HR20_P0 w t u = ∑ r, w r • Matrix.vecMulVec (HR20_v t u r) (HR20_v t u r) := by
  ext i j
  simp only [HR20_P0, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, HR20_v,
    smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    rw [(hasDerivAt_m w t (hne · i)).deriv]
    rw [neg_neg]
    refine Finset.sum_congr rfl fun r _ => ?_
    have := hne r i
    field_simp
  · simp only [hij, if_false]
    have hji : u j - u i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hu h.symm))
    unfold HR20_m
    rw [← Finset.sum_sub_distrib, div_eq_iff hji, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 := hne r i
    have h2 := hne r j
    field_simp
    ring

/-- **#17 (P1).** `P1 = Σᵣ wᵣ tᵣ vᵣ vᵣᵀ`. -/
theorem HR20_P1_eq (w t : Fin k → ℝ) (u : Fin n → ℝ) (hu : Function.Injective u)
    (hne : ∀ r i, t r + u i ≠ 0) :
    HR20_P1 w t u = ∑ r, (w r * t r) • Matrix.vecMulVec (HR20_v t u r) (HR20_v t u r) := by
  ext i j
  simp only [HR20_P1, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, HR20_v,
    smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    have hd : HasDerivAt (fun x => x * HR20_m w t x)
        (HR20_m w t (u i) + u i * (-∑ r, w r / (t r + u i) ^ 2)) (u i) :=
      ((hasDerivAt_id' (u i)).mul (hasDerivAt_m w t (hne · i))).congr_deriv (by ring)
    rw [hd.deriv]
    unfold HR20_m
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have := hne r i
    field_simp
    ring
  · simp only [hij, if_false]
    have hij' : u i - u j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hu h))
    unfold HR20_m
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, div_eq_iff hij', Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 := hne r i
    have h2 := hne r j
    field_simp
    ring

private theorem posSemidef_weighted_vecMulVec (c : ℝ) (hc : 0 ≤ c) (v : Fin n → ℝ) :
    (c • Matrix.vecMulVec v v).PosSemidef := by
  have h := (Matrix.posSemidef_vecMulVec_self_star v)
  simpa using h.smul hc

/-- **#17 (PSD).** With nonnegative weights `wᵣ` and `tᵣ ≥ 0`, both `P0` and `P1` are PSD. -/
theorem HR20_pick_psd (w t : Fin k → ℝ) (u : Fin n → ℝ) (hu : Function.Injective u)
    (hne : ∀ r i, t r + u i ≠ 0) (hw : ∀ r, 0 ≤ w r) (ht : ∀ r, 0 ≤ t r) :
    (HR20_P0 w t u).PosSemidef ∧ (HR20_P1 w t u).PosSemidef := by
  refine ⟨?_, ?_⟩
  · rw [HR20_P0_eq w t u hu hne]
    exact Matrix.posSemidef_sum _ fun r _ => posSemidef_weighted_vecMulVec _ (hw r) _
  · rw [HR20_P1_eq w t u hu hne]
    exact Matrix.posSemidef_sum _ fun r _ =>
      posSemidef_weighted_vecMulVec _ (mul_nonneg (hw r) (ht r)) _

end Pick

/-! ## #32 Hermite–Biehler, finite core -/

private theorem norm_conj_sub_lt {z a : ℂ} (hz : 0 < z.im) (ha : a.im < 0) :
    ‖conj z - a‖ < ‖z - a‖ := by
  have h : ‖conj z - a‖ ^ 2 < ‖z - a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_pos hz (neg_pos.mpr ha)]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

private theorem sub_ne_zero_of_im {z a : ℂ} (hz : 0 < z.im) (ha : a.im < 0) : z - a ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The multiset form of the finite Hermite–Biehler inequality. -/
theorem HR22_hb_multiset {z : ℂ} (hz : 0 < z.im) :
    ∀ s : Multiset ℂ, (∀ a ∈ s, a.im < 0) →
      ‖(s.map fun a => conj z - a).prod‖ ≤ ‖(s.map fun a => z - a).prod‖ ∧
      (s ≠ 0 → ‖(s.map fun a => conj z - a).prod‖ < ‖(s.map fun a => z - a).prod‖) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    have ha : a.im < 0 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ b ∈ s, b.im < 0 := fun b hb => h b (Multiset.mem_cons_of_mem hb)
    obtain ⟨ih1, _⟩ := ih hs
    have hA := norm_conj_sub_lt hz ha
    have hP2 : (s.map fun b => z - b).prod ≠ 0 := by
      refine Multiset.prod_ne_zero ?_
      intro h0
      obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h0
      exact sub_ne_zero_of_im hz (hs b hb) hb0
    have hP2pos : 0 < ‖(s.map fun b => z - b).prod‖ := norm_pos_iff.mpr hP2
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    refine ⟨?_, fun _ => ?_⟩
    · exact mul_le_mul hA.le ih1 (norm_nonneg _) (norm_nonneg _)
    · calc ‖conj z - a‖ * ‖(s.map fun b => conj z - b).prod‖
          ≤ ‖conj z - a‖ * ‖(s.map fun b => z - b).prod‖ :=
            mul_le_mul_of_nonneg_left ih1 (norm_nonneg _)
        _ < ‖z - a‖ * ‖(s.map fun b => z - b).prod‖ := mul_lt_mul_of_pos_right hA hP2pos

/-- **#32 (hypothesis made explicit: nonconstant).** If `P ∈ ℂ[X]` is nonconstant and all its roots
have negative imaginary part, then `|P(z̄)| < |P(z)|` for every `z` with `Im z > 0`.
(For a constant polynomial the two sides are equal, so "nonconstant" is needed.) -/
theorem HR22_hermite_biehler_finite (P : Polynomial ℂ) (hdeg : 0 < P.natDegree)
    (hroots : ∀ a ∈ P.roots, a.im < 0) {z : ℂ} (hz : 0 < z.im) :
    ‖P.eval (conj z)‖ < ‖P.eval z‖ := by
  have hP0 : P ≠ 0 := by
    rintro rfl; simp at hdeg
  have hcard : Multiset.card P.roots = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hsplit := (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
  have hroots0 : P.roots ≠ 0 := by
    intro h0; rw [h0] at hcard; simp at hcard; omega
  have heval : ∀ w : ℂ, P.eval w = P.leadingCoeff * (P.roots.map fun a => w - a).prod := by
    intro w
    have := congrArg (Polynomial.eval w) hsplit
    rw [this]
    simp [Polynomial.eval_multiset_prod, Multiset.map_map]
  have hlead : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP0)
  rw [heval (conj z), heval z, norm_mul, norm_mul]
  exact mul_lt_mul_of_pos_left ((HR22_hb_multiset hz P.roots hroots).2 hroots0) hlead


end GppHeartElementary

#print axioms GppHeartElementary.HR15_hasse_form_identity
#print axioms GppHeartElementary.HR15_hasse_sign_iff
#print axioms GppHeartElementary.HR15_hasse_roots_unit_iff
#print axioms GppHeartElementary.HR15_toeplitz_gram_psd
#print axioms GppHeartElementary.HR15_shift_exp
#print axioms GppHeartElementary.HR15_pole_shift
#print axioms GppHeartElementary.HR16_a_periodic
#print axioms GppHeartElementary.HR16_a_odd
#print axioms GppHeartElementary.HR16_dh_not_multiplicative
#print axioms GppHeartElementary.HR22_euler_factor_density_pos_at_zero
#print axioms GppHeartElementary.HR22_euler_factor_density_neg_at_pi
#print axioms GppHeartElementary.HR20_P0_eq
#print axioms GppHeartElementary.HR20_P1_eq
#print axioms GppHeartElementary.HR20_pick_psd
#print axioms GppHeartElementary.HR22_hb_multiset
#print axioms GppHeartElementary.HR22_hermite_biehler_finite
