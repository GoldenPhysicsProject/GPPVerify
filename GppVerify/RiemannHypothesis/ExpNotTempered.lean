import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Exponential growth is not a tempered distribution

## Golden Physics Project — shadow framework formalization

This file retires the last remaining custom axiom of the repository,
`GppRH.exp_growth_not_tempered`. It is now `ExpNotTempered.exp_growth_not_tempered`,
proved, depending on nothing beyond `propext`, `Classical.choice` and `Quot.sound`.

## The statement

For `a ≠ 0` there is no continuous linear functional `T : 𝓢(ℝ, ℂ) →L[ℝ] ℂ` with
`T φ = ∫ u, e^{au} · φ(u)` for every Schwartz `φ`.

## The proof

Fix a bump `b`: smooth, supported in the unit ball, nonnegative, with `∫ e^{av} b(v) dv ≠ 0`.
For each `n` set

  `ψₙ := e^{-|a|n} · b(· − tₙ)`,   `tₙ = sign(a)·n`,

so that `a · tₙ = |a|·n` whatever the sign of `a`. Two facts collide:

* **`ψₙ → 0` in `𝓢`.** Every Schwartz seminorm of `ψₙ` is bounded by
  `e^{-|a|n} · (n+1)^k · Cₘ` — the shift costs only polynomial growth, while the scalar
  decays exponentially. Continuity of `T` then forces `T ψₙ → T 0 = 0`.
* **`T ψₙ` does not depend on `n`.** Translating the bump multiplies the weighted integral
  by exactly `e^{a tₙ} = e^{|a|n}`, which is what the scalar was chosen to cancel. So
  `T ψₙ = ∫ e^{av} b(v) dv` for every `n`.

A constant sequence converging to `0` is `0`, so `∫ e^{av} b(v) dv = 0` — contradicting the
positivity of that integral.

## Why this was only possible after the Mathlib 4.33 upgrade

`HasCompactSupport.toSchwartzMap` is the entry point for every construction below, and it
does not exist in Mathlib 4.19.0. Before the upgrade the Schwartz space was available with
no way to build a concrete nonzero element of it, which is exactly what this argument needs.
-/

open MeasureTheory SchwartzMap Filter Function
open scoped Topology

noncomputable section

namespace ExpNotTempered

def B : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
def b (u : ℝ) : ℂ := (B u : ℂ)
lemma b_contDiff : ContDiff ℝ (⊤ : ℕ∞) b := Complex.ofRealCLM.contDiff.comp B.contDiff
lemma b_compact : HasCompactSupport b := by
  apply B.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)); simp
lemma b_tsupport : tsupport b ⊆ Metric.closedBall (0:ℝ) 1 := by
  have hs : Function.support b = Metric.ball (0:ℝ) 1 := by
    have h2 : Function.support b = Function.support (B : ℝ → ℝ) := by
      ext x; simp [b, Complex.ofReal_eq_zero]
    rw [h2, B.support_eq]; rfl
  calc tsupport b = closure (Function.support b) := rfl
    _ = closure (Metric.ball (0:ℝ) 1) := by rw [hs]
    _ ⊆ Metric.closedBall (0:ℝ) 1 := Metric.closure_ball_subset_closedBall
def bS : 𝓢(ℝ, ℂ) := b_compact.toSchwartzMap (by exact_mod_cast b_contDiff)
lemma bS_coe : (bS : ℝ → ℂ) = b := rfl
lemma b_deriv_bound (m : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ m b x‖ ≤ SchwartzMap.seminorm ℝ 0 m bS := by
  simpa [bS_coe] using bS.le_seminorm ℝ 0 m x
lemma b_deriv_zero {x : ℝ} (hx : 1 < ‖x‖) (m : ℕ) : iteratedFDeriv ℝ m b x = 0 := by
  by_contra h
  have hx' : x ∈ tsupport b := support_iteratedFDeriv_subset m h
  have := b_tsupport hx'
  simp only [Metric.mem_closedBall, dist_zero_right] at this
  linarith

def bt (t : ℝ) : ℝ → ℂ := fun u => b (u - t)
lemma bt_contDiff (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (bt t) :=
  b_contDiff.comp (contDiff_id.sub contDiff_const)
lemma bt_compact (t : ℝ) : HasCompactSupport (bt t) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := (fun x : ℝ => x + t) '' (tsupport b)) (b_compact.image (by fun_prop)) ?_
  intro x hx
  exact ⟨x - t, subset_tsupport _ hx, by ring⟩

/-- The scaled translate `c · b(· − t)`. -/
def psi (c : ℂ) (t : ℝ) : ℝ → ℂ := c • bt t
lemma psi_contDiff (c : ℂ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psi c t) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun u => c • bt t u)
  exact (bt_contDiff t).const_smul _
lemma psi_compact (c : ℂ) (t : ℝ) : HasCompactSupport (psi c t) := by
  refine HasCompactSupport.of_support_subset_isCompact (bt_compact t) ?_
  intro x hx
  by_contra hn
  have h0 : bt t x = 0 := by
    by_contra h
    exact hn (subset_tsupport _ h)
  exact hx (show psi c t x = 0 by show c • bt t x = 0; rw [h0, smul_zero])

def psiS (c : ℂ) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  (psi_compact c t).toSchwartzMap (by exact_mod_cast psi_contDiff c t)
lemma psiS_coe (c : ℂ) (t : ℝ) : (psiS c t : ℝ → ℂ) = psi c t := rfl
lemma psiS_apply (c : ℂ) (t : ℝ) (u : ℝ) : psiS c t u = c * b (u - t) := rfl

lemma psi_norm_iteratedFDeriv (c : ℂ) (t : ℝ) (m : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ m (psi c t) u‖ = ‖c‖ * ‖iteratedFDeriv ℝ m b (u - t)‖ := by
  have hcd : ContDiffAt ℝ (m : ℕ∞) (bt t) u :=
    ((bt_contDiff t).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [psi, iteratedFDeriv_const_smul_apply hcd, norm_smul]
  congr 2
  exact iteratedFDeriv_comp_sub m t u

/-- **The seminorm bound.** Every Schwartz seminorm of the scaled translate is
controlled by `‖c‖` times a polynomial in the shift. -/
lemma psiS_seminorm_le (c : ℂ) (t : ℝ) (k m : ℕ) :
    SchwartzMap.seminorm ℝ k m (psiS c t)
      ≤ ‖c‖ * ((|t| + 1) ^ k * SchwartzMap.seminorm ℝ 0 m bS) := by
  refine SchwartzMap.seminorm_le_bound ℝ k m _ ?_ ?_
  · have h1 : (0:ℝ) ≤ (|t| + 1) ^ k := by positivity
    have h2 : (0:ℝ) ≤ SchwartzMap.seminorm ℝ 0 m bS := apply_nonneg _ _
    positivity
  · intro u
    rw [show ((psiS c t : ℝ → ℂ)) = psi c t from rfl, psi_norm_iteratedFDeriv]
    rcases lt_or_ge 1 ‖u - t‖ with hfar | hnear
    · rw [b_deriv_zero hfar m]
      simp only [norm_zero, mul_zero]
      have h1 : (0:ℝ) ≤ (|t| + 1) ^ k := by positivity
      have h2 : (0:ℝ) ≤ SchwartzMap.seminorm ℝ 0 m bS := apply_nonneg _ _
      positivity
    · have hu : ‖u‖ ≤ |t| + 1 := by
        calc ‖u‖ = ‖(u - t) + t‖ := by ring_nf
          _ ≤ ‖u - t‖ + ‖t‖ := norm_add_le _ _
          _ ≤ 1 + |t| := by simpa [Real.norm_eq_abs] using add_le_add hnear (le_refl |t|)
          _ = |t| + 1 := by ring
      have hk : ‖u‖ ^ k ≤ (|t| + 1) ^ k := pow_le_pow_left₀ (norm_nonneg u) hu k
      have hb := b_deriv_bound m (u - t)
      calc ‖u‖ ^ k * (‖c‖ * ‖iteratedFDeriv ℝ m b (u - t)‖)
          = ‖c‖ * (‖u‖ ^ k * ‖iteratedFDeriv ℝ m b (u - t)‖) := by ring
        _ ≤ ‖c‖ * ((|t| + 1) ^ k * SchwartzMap.seminorm ℝ 0 m bS) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
            exact mul_le_mul hk hb (norm_nonneg _) (by positivity)


/-- Exponential decay beats the polynomial growth of the shift. -/
lemma decay_beats_poly {r : ℝ} (hr : 0 < r) (k : ℕ) (C : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-r * n) * ((|(n:ℝ)| + 1) ^ k * C))
      atTop (nhds 0) := by
  have h0 := (Real.summable_pow_mul_exp_neg_nat_mul k hr).tendsto_atTop_zero
  have h1 := h0.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => Real.exp (-r * n) * ((n:ℝ) + 1) ^ k) atTop (nhds 0) := by
    have hEq : (fun n : ℕ => Real.exp (-r * n) * ((n:ℝ) + 1) ^ k)
        = fun n : ℕ => Real.exp r *
            ((((n + 1 : ℕ) : ℝ) ^ k) * Real.exp (-r * ((n + 1 : ℕ) : ℝ))) := by
      funext n
      push_cast
      rw [show -r * ((n:ℝ) + 1) = -r * n + -r by ring, Real.exp_add]
      have h : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
      -- `ring` treats `rexp e` as an atom, so `rexp (-r * n)` and `rexp (-(r * n))`
      -- are different atoms until the exponents are put in one form.
      simp only [neg_mul]
      linear_combination (-(Real.exp (-(r * (n:ℝ))) * (1 + (n:ℝ)) ^ k)) * h
    rw [hEq]
    simpa using (h1.const_mul (Real.exp r))
  have hEq2 : (fun n : ℕ => Real.exp (-r * n) * ((|(n:ℝ)| + 1) ^ k * C))
      = fun n : ℕ => (Real.exp (-r * n) * ((n:ℝ) + 1) ^ k) * C := by
    funext n; rw [abs_of_nonneg (Nat.cast_nonneg n)]; ring
  rw [hEq2]
  simpa using h2.mul_const C

/-- Seminorm bounds that tend to zero give convergence in the Schwartz space. -/
lemma tendsto_zero_of_seminorm_bounds (u : ℕ → 𝓢(ℝ, ℂ))
    (hb : ∀ (k m : ℕ), ∃ M : ℕ → ℝ,
      (∀ n, SchwartzMap.seminorm ℝ k m (u n) ≤ M n) ∧ Tendsto M atTop (nhds 0)) :
    Tendsto u atTop (nhds 0) := by
  rw [(schwartz_withSeminorms ℝ ℝ ℂ).tendsto_nhds_atTop]
  rintro ⟨k, m⟩ ε hε
  obtain ⟨M, hM, hMt⟩ := hb k m
  obtain ⟨N, hN⟩ := (hMt.eventually (eventually_lt_nhds hε)).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have h1 : (schwartzSeminormFamily ℝ ℝ ℂ (k, m)) (u n - 0)
      = SchwartzMap.seminorm ℝ k m (u n) := by
    simp [schwartzSeminormFamily_apply]
  rw [h1]
  exact lt_of_le_of_lt (hM n) (hN n hn)



/-- The constant the whole argument turns on: `∫ e^{av} b(v) dv`. -/
def cst (a : ℝ) : ℂ := ∫ v : ℝ, Complex.exp (a * v) * b v

/-- Shifting the bump multiplies the weighted integral by `e^{at}` — the exact factor the
scalar `e^{-|a|n}` is chosen to cancel. -/
lemma integral_shift (a : ℝ) (c : ℂ) (t : ℝ) :
    (∫ u : ℝ, Complex.exp (a * u) * (c * b (u - t)))
      = c * Complex.exp (a * t) * cst a := by
  have key : (fun u : ℝ => Complex.exp (a * u) * (c * b (u - t)))
      = fun u : ℝ => (fun v : ℝ => c * Complex.exp (a * t) * (Complex.exp (a * v) * b v)) (u - t) := by
    funext u
    have : ((a : ℂ) * (u - t)) + (a * t) = a * u := by push_cast; ring
    rw [show ((a:ℂ) * u) = ((a:ℂ) * ((u:ℝ) - t) + (a:ℂ) * t) by push_cast; ring,
      Complex.exp_add]
    push_cast
    ring
  rw [key,
    integral_sub_right_eq_self
      (fun v : ℝ => c * Complex.exp ((a:ℂ) * t) * (Complex.exp ((a:ℂ) * v) * b v)) t,
    MeasureTheory.integral_const_mul, cst]



/-- The real integrand behind `cst`. -/
def g (a : ℝ) (v : ℝ) : ℝ := Real.exp (a * v) * B v

lemma cst_eq_ofReal (a : ℝ) : cst a = ((∫ v : ℝ, g a v : ℝ) : ℂ) := by
  rw [cst, ← integral_complex_ofReal]
  congr 1
  funext v
  simp [g, b, Complex.ofReal_mul, Complex.ofReal_exp]

lemma g_nonneg (a : ℝ) : 0 ≤ g a := fun v => by
  have := B.nonneg (x := v)
  have h2 := (Real.exp_pos (a * v)).le
  exact mul_nonneg h2 this

lemma g_support (a : ℝ) : Function.support (g a) = Metric.ball (0:ℝ) 1 := by
  have : Function.support (g a) = Function.support (B : ℝ → ℝ) := by
    ext v
    simp [g, Function.mem_support, (Real.exp_pos (a*v)).ne']
  rw [this, B.support_eq]; rfl

lemma g_integrable (a : ℝ) : Integrable (g a) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul B.continuous
  · apply HasCompactSupport.of_support_subset_isCompact
      (K := Metric.closedBall (0:ℝ) 1) (isCompact_closedBall _ _)
    rw [g_support]
    exact Metric.ball_subset_closedBall

/-- **`cst a` is never zero.** -/
lemma cst_ne_zero (a : ℝ) : cst a ≠ 0 := by
  rw [cst_eq_ofReal]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  have hpos : 0 < ∫ v : ℝ, g a v := by
    rw [integral_pos_iff_support_of_nonneg (g_nonneg a) (g_integrable a), g_support]
    simp [Real.volume_ball]
  exact hpos.ne'



/-- The sign-aware shift: `t a n = n` when `a > 0`, `-n` when `a < 0`, so that
`a * t a n = |a| * n` in both cases. -/
def shift (a : ℝ) (n : ℕ) : ℝ := if 0 < a then (n : ℝ) else -(n : ℝ)

lemma abs_shift (a : ℝ) (n : ℕ) : |shift a n| = n := by
  unfold shift; split <;> simp

lemma mul_shift (a : ℝ) (ha : a ≠ 0) (n : ℕ) : a * shift a n = |a| * n := by
  unfold shift
  rcases lt_trichotomy a 0 with h | h | h
  · rw [if_neg (not_lt.mpr h.le), abs_of_neg h]; ring
  · exact absurd h ha
  · rw [if_pos h, abs_of_pos h]

/-- The witness sequence: `e^{-|a|n} · b(· − t_n)`. -/
def wit (a : ℝ) (n : ℕ) : 𝓢(ℝ, ℂ) :=
  psiS (Complex.exp (((-|a| * n : ℝ) : ℂ))) (shift a n)

lemma wit_norm_scalar (a : ℝ) (n : ℕ) :
    ‖Complex.exp (((-|a| * n : ℝ) : ℂ))‖ = Real.exp (-|a| * n) := by
  rw [Complex.norm_exp, Complex.ofReal_re]



/-- **The witness sequence tends to zero in the Schwartz space.** -/
lemma wit_tendsto_zero {a : ℝ} (ha : a ≠ 0) :
    Filter.Tendsto (wit a) Filter.atTop (nhds 0) := by
  refine tendsto_zero_of_seminorm_bounds _ (fun k m => ?_)
  refine ⟨fun n => Real.exp (-|a| * n) * ((|shift a n| + 1) ^ k *
      SchwartzMap.seminorm ℝ 0 m bS), fun n => ?_, ?_⟩
  · have := psiS_seminorm_le (Complex.exp (((-|a| * n : ℝ) : ℂ))) (shift a n) k m
    rwa [wit_norm_scalar] at this
  · have heq : (fun n : ℕ => Real.exp (-|a| * n) *
          ((|shift a n| + 1) ^ k * SchwartzMap.seminorm ℝ 0 m bS))
        = (fun n : ℕ => Real.exp (-|a| * n) *
          ((|(n : ℝ)| + 1) ^ k * SchwartzMap.seminorm ℝ 0 m bS)) := by
      funext n
      rw [abs_shift, Nat.abs_cast]
    rw [heq]
    exact decay_beats_poly (abs_pos.mpr ha) k _

/-- **The weighted integral of the witness does not depend on `n`.** The scalar
`e^{-|a|n}` cancels the `e^{a t_n} = e^{|a|n}` produced by the shift. -/
lemma integral_wit (a : ℝ) (ha : a ≠ 0) (n : ℕ) :
    (∫ u : ℝ, Complex.exp (a * u) * (wit a n u)) = cst a := by
  have h1 : ∀ u : ℝ, (wit a n u)
      = Complex.exp (((-|a| * n : ℝ) : ℂ)) * b (u - shift a n) := fun u => rfl
  simp only [h1]
  rw [integral_shift a (Complex.exp (((-|a| * n : ℝ) : ℂ))) (shift a n)]
  have hcancel : Complex.exp (((-|a| * n : ℝ) : ℂ)) * Complex.exp ((a : ℂ) * (shift a n)) = 1 := by
    rw [← Complex.exp_add]
    have : ((-|a| * n : ℝ) : ℂ) + (a : ℂ) * (shift a n) = 0 := by
      have hc : ((a * shift a n : ℝ) : ℂ) = ((|a| * n : ℝ) : ℂ) := by
        rw [mul_shift a ha n]
      push_cast at hc ⊢
      linear_combination hc
    rw [this, Complex.exp_zero]
  rw [mul_assoc, ← mul_assoc] at *
  rw [hcancel, one_mul]



/-- **Exponential growth is not a tempered distribution.**

For `a ≠ 0` there is no continuous linear functional on `𝓢(ℝ, ℂ)` that integrates
against `e^{au}`. Formerly an axiom of this repository. -/
theorem exp_growth_not_tempered (a : ℝ) (ha : a ≠ 0) :
    ¬∃ T : 𝓢(ℝ, ℂ) →L[ℝ] ℂ,
      ∀ φ : 𝓢(ℝ, ℂ), T φ = ∫ u : ℝ, Complex.exp (a * u) * (φ u) := by
  rintro ⟨T, hT⟩
  -- Along the witness sequence the functional is the constant `cst a` …
  have hconst : ∀ n : ℕ, T (wit a n) = cst a := fun n => by
    rw [hT]; exact integral_wit a ha n
  -- … yet the witness sequence tends to `0`, so `T` of it tends to `T 0 = 0`.
  have hzero : Filter.Tendsto (fun n => T (wit a n)) Filter.atTop (nhds 0) := by
    have h := (T.continuous.tendsto 0).comp (wit_tendsto_zero ha)
    -- 4.33: `Function.comp` no longer unfolds under plain `simp`.
    simpa [Function.comp_def] using h
  rw [show (fun n => T (wit a n)) = fun _ : ℕ => cst a from funext hconst] at hzero
  -- A constant sequence converging to `0` forces the constant to be `0`.
  have : cst a = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  exact cst_ne_zero a this

end ExpNotTempered
