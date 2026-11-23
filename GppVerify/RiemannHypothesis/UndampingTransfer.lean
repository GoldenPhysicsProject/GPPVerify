/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Convolution

/-!
# Undamping package, item (a): the transfer identity at quadratic-form level

Routed 2026-11-20 (D2's undamping correction, Turbo-audited): on a function `f` supported in
`[0, L]`,

`Q₀ − Q₂ = P − K_{1/2} − K_{3/2} − K_{5/2} − Σ_{log n < L} (1 − n⁻²) Λ(n) n^{−1/2} (S_{log n} + S_{log n}*)`

as quadratic forms.  Here `Q_a = W(e^{−a|h|} A_f)` with `A_f` the real autocorrelation, `P` has
kernel `2cosh((x−y)/2)` (rank ≤ 2), `K_b` has kernel `e^{−b|x−y|}`, and `S_h` is translation by `h`
compressed to `[0, L]`, so `⟨f,(S_h+S_h*)f⟩ = A_f(h) + A_f(−h)` (`shiftForm`).

**What is proved** (`undamping_transfer`): for bounded measurable `f` supported in `[0,L]` and
every cutoff `N`,
`W((1 − e^{−2|h|}) A_f) = P(f,f) − Σ_b K_b(f,f) − Σ_{n ≤ N} (1−n⁻²) Λ(n) n^{−1/2} shiftForm f (log n)`
where `W` is applied through its ordinary density and prime atoms.  The two real steps are
(i) the gamma-denominator cancellation `(1−e^{−2t})(2cosh(t/2) − e^{−t/2}/(1−e^{−2t})) =
e^{t/2} − e^{−3t/2} − e^{−5t/2}` (`damp_mul_density`) and (ii) the autocorrelation/double-integral
pairing (`corr_pairing`, Fubini + translation invariance), plus `e^{t/2} = 2cosh(t/2) − e^{−t/2}`.
`autoCorr_eq_zero_of_le` shows terms with `log n ≥ L` vanish, so the `n ≤ N` truncation is the sum
over `log n < L` once `N ≥ e^L`.

 The explicit-formula density of `W` (`weilDensity`, the
prime-atom signs `−Λ(n) n^{−1/2}`) is taken as given, exactly as in Turbo's audit (item 4's "one
input taken as known"). By linearity `Q₀ − Q₂ = W((1 − e^{−2|h|}) A_f)`, and on that test function
(first-order zero at `0`) no origin/pole constant appears; `Q₀` and `Q₂` individually (zero side,
constants) are **not** defined here, so the theorem is about the *difference* `diffForm`. It is
a transfer, not a lower bound: `Q₂` still contains a nontrivial operator.

No `sorry`, no `axiom`.
-/


open MeasureTheory Set

namespace GppUndampingTransfer

/-- Real autocorrelation `A_f(h) = ∫ f(x) f(x+h) dx`. -/
noncomputable def autoCorr (f : ℝ → ℝ) (h : ℝ) : ℝ := ∫ x, f x * f (x + h)

/-- Form of the translation `S_h` compressed to `[0,L]` plus its adjoint, on a function
supported in `[0,L]` (zero-extended): `⟨f,S_h f⟩ + ⟨S_h f,f⟩ = A_f(h) + A_f(−h)`. -/
noncomputable def shiftForm (f : ℝ → ℝ) (h : ℝ) : ℝ := autoCorr f h + autoCorr f (-h)

/-- Quadratic form of the integral operator with kernel `exp(−b|x−y|)`. -/
noncomputable def Kform (b : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-b * |p.1 - p.2|)

/-- Quadratic form of the rank-≤2 kernel `2cosh((x−y)/2)`. -/
noncomputable def Pform (f : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, f p.1 * f p.2 * (2 * Real.cosh ((p.1 - p.2) / 2))

/-- The ordinary density of the Weil functional for `h > 0`:
`2cosh(h/2) − e^{−h/2}/(1 − e^{−2h})`. -/
noncomputable def weilDensity (h : ℝ) : ℝ :=
  2 * Real.cosh (h / 2) - Real.exp (-h / 2) / (1 - Real.exp (-2 * h))

/-- The damping-difference factor `1 − e^{−2|h|}` (undamped minus `a = 2`). -/
noncomputable def dampDiff (h : ℝ) : ℝ := 1 - Real.exp (-2 * |h|)

/-- Regularised density of the difference: `e^{t/2} − e^{−3t/2} − e^{−5t/2}`. -/
noncomputable def kcomb (t : ℝ) : ℝ := Real.exp (t / 2) - Real.exp (-(3 * t / 2)) - Real.exp (-(5 * t / 2))

/-- **Gamma-denominator cancellation.** For `t > 0`:
`(1 − e^{−2t}) · (2cosh(t/2) − e^{−t/2}/(1−e^{−2t})) = e^{t/2} − e^{−3t/2} − e^{−5t/2}`. -/
theorem damp_mul_density {t : ℝ} (ht : 0 < t) :
    (1 - Real.exp (-2 * t)) * weilDensity t = kcomb t := by
  unfold weilDensity kcomb
  set q := Real.exp (-(t / 2)) with hq
  set p := Real.exp (t / 2) with hp
  have hpq : p * q = 1 := by rw [hp, hq, ← Real.exp_add]; simp
  have e2 : Real.exp (-2 * t) = q ^ 4 := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (-(3 * t / 2)) = q ^ 3 := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e5 : Real.exp (-(5 * t / 2)) = q ^ 5 := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e1 : Real.exp (-t / 2) = q := by rw [hq]; congr 1; ring
  have h1 : (1 - q ^ 4) ≠ 0 := by
    have : q ^ 4 < 1 := by
      have hq1 : q < 1 := by rw [hq]; have := Real.exp_lt_exp.mpr (show -(t / 2) < 0 by linarith); simpa using this
      have hq0 : 0 < q := Real.exp_pos _
      exact pow_lt_one₀ hq0.le hq1 (by norm_num)
    linarith
  rw [Real.cosh_eq, e2, e3, e5, e1]
  have h3 : Real.exp (-(t / 2)) = q := rfl
  have : 2 * ((p + Real.exp (-(t / 2))) / 2) = p + q := by ring
  rw [this]
  field_simp
  linear_combination (-(q^3)) * hpq

section Fubini

variable {f : ℝ → ℝ} {L B : ℝ}

theorem integrable_of_bound {F : ℝ × ℝ → ℝ} (hF : Measurable F) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤) {C : ℝ}
    (hC : ∀ p ∈ S, |F p| ≤ C) (h0 : ∀ p, p ∉ S → F p = 0) : Integrable F := by
  have hg : Integrable (S.indicator (fun _ : ℝ × ℝ => C)) := by
    rw [integrable_indicator_iff hS]; exact integrableOn_const hSfin
  refine hg.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ S
  · simp only [Set.indicator, hp, if_true]; exact hC p hp
  · simp [Set.indicator, hp, h0 p hp]

theorem vol_box (a b c d : ℝ) : volume (Icc a b ×ˢ Icc c d) ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem integrable_sq (hf : Measurable f) (hB : ∀ x, |f x| ≤ B)
    (hs : ∀ x, x ∉ Icc 0 L → f x = 0) {k : ℝ → ℝ} (hk : Continuous k) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f p.2 * k |p.1 - p.2|) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn hk.continuousOn
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  refine integrable_of_bound (S := Icc 0 L ×ˢ Icc 0 L) (C := B * B * M) ?_ ?_ (vol_box _ _ _ _) ?_ ?_
  · have : Measurable fun p : ℝ × ℝ => f p.1 * f p.2 * k |p.1 - p.2| := by
      have := hk.measurable
      fun_prop
    exact this
  · exact measurableSet_Icc.prod measurableSet_Icc
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only
    have hd : |x - y| ∈ Icc (0 : ℝ) L := ⟨abs_nonneg _, by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]⟩
    have h1 := hM _ hd
    rw [Real.norm_eq_abs] at h1
    rw [abs_mul, abs_mul]
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) h1
    exact mul_le_mul (mul_le_mul (hB x) (hB y) (abs_nonneg _) hB0) h1 (abs_nonneg _) (by positivity)
  · rintro ⟨x, y⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with h | h
    · simp [hs x h]
    · simp [hs y h]


theorem integrable_shift (hf : Measurable f) (hB : ∀ x, |f x| ≤ B)
    (hs : ∀ x, x ∉ Icc 0 L → f x = 0) {k : ℝ → ℝ} (hk : Continuous k) :
    Integrable (fun q : ℝ × ℝ => f q.2 * f (q.2 + q.1) * k |q.1|) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn hk.continuousOn
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  refine integrable_of_bound (S := Icc (-L) L ×ˢ Icc 0 L) (C := B * B * M) ?_ ?_ (vol_box _ _ _ _) ?_ ?_
  · have := hk.measurable
    fun_prop
  · exact measurableSet_Icc.prod measurableSet_Icc
  · rintro ⟨h, x⟩ ⟨hh, hx⟩
    simp only
    have hd : |h| ∈ Icc (0 : ℝ) L := ⟨abs_nonneg _, by rw [abs_le]; exact ⟨hh.1, hh.2⟩⟩
    have h1 := hM _ hd
    rw [Real.norm_eq_abs] at h1
    rw [abs_mul, abs_mul]
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) h1
    exact mul_le_mul (mul_le_mul (hB x) (hB (x + h)) (abs_nonneg _) hB0) h1 (abs_nonneg _) (by positivity)
  · rintro ⟨h, x⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with h' | h'
    · by_cases hx : x ∈ Icc 0 L
      · have : x + h ∉ Icc 0 L := by
          intro hxh
          apply h'
          constructor <;> linarith [hx.1, hx.2, hxh.1, hxh.2]
        simp [hs _ this]
      · simp [hs x hx]
    · simp [hs x h']

/-- The autocorrelation pairing is the symmetric double integral. -/
theorem corr_pairing (hf : Measurable f) (hB : ∀ x, |f x| ≤ B)
    (hs : ∀ x, x ∉ Icc 0 L → f x = 0) {k : ℝ → ℝ} (hk : Continuous k) :
    ∫ h, autoCorr f h * k |h| = ∫ p : ℝ × ℝ, f p.1 * f p.2 * k |p.1 - p.2| := by
  have hI := integrable_shift hf hB hs hk
  have e1 : ∀ h : ℝ, autoCorr f h * k |h| = ∫ x, f x * f (x + h) * k |h| := by
    intro h; unfold autoCorr; rw [integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun h x => f x * f (x + h) * k |h|) (by rw [← Measure.volume_eq_prod]; exact hI)]
  have e2 : ∀ x : ℝ, ∫ h, f x * f (x + h) * k |h| = ∫ y, f x * f y * k |x - y| := by
    intro x
    have : ∀ h : ℝ, f x * f (x + h) * k |h| = f x * ((fun y => f y * k |y - x|) (x + h)) := by
      intro h; simp only [add_sub_cancel_left]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_add_left_eq_self (fun y => f y * k |y - x|) x,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only; rw [abs_sub_comm]; ring
  simp_rw [e2]
  rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact integrable_sq hf hB hs hk)]

end Fubini


open ArithmeticFunction in
/-- The Weil functional applied to a test function `g` (vanishing to first order at `0`, so no
origin/pole constants appear): ordinary density plus the prime-power atoms with
`n ≤ N` (`−Λ(n) n^{−1/2} (g(log n) + g(−log n))`).  The explicit-formula density of `W` is the
**input** taken as known (audited by Turbo from D2's derivation); it is not re-derived here. -/
noncomputable def weilApply (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∫ h, g h * weilDensity |h|) -
    ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n / Real.sqrt n) * (g (Real.log n) + g (-Real.log n))

/-- `Q₀ − Q₂ = W((1 − e^{−2|h|}) A_f)`. -/
noncomputable def diffForm (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  weilApply (fun h => dampDiff h * autoCorr f h) N

theorem dampDiff_log {n : ℕ} (hn : 1 ≤ n) : dampDiff (Real.log n) = 1 - ((n : ℝ) ^ 2)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  unfold dampDiff
  rw [abs_of_nonneg hl]
  congr 1
  rw [show -2 * Real.log n = -(Real.log ((n : ℝ) ^ 2)) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_neg, Real.exp_log (by positivity)]

open ArithmeticFunction in
/--  For a bounded measurable `f` supported in `[0, L]`,
`Q₀(f) − Q₂(f) = P(f,f) − Σ_{b∈{½,3/2,5/2}} K_b(f,f)
   − Σ_{n} (1 − n⁻²) Λ(n) n^{−1/2} ⟨f, (S_{log n} + S_{log n}*) f⟩`. 
-/
theorem undamping_transfer (hf : Measurable f) (hB : ∀ x, |f x| ≤ B)
    (hs : ∀ x, x ∉ Icc 0 L → f x = 0) (N : ℕ) :
    diffForm f N = Pform f - Kform (1 / 2) f - Kform (3 / 2) f - Kform (5 / 2) f -
      ∑ n ∈ Finset.Icc 1 N, (1 - ((n : ℝ) ^ 2)⁻¹) * (vonMangoldt n / Real.sqrt n) *
        shiftForm f (Real.log n) := by
  unfold diffForm weilApply
  -- ordinary part
  have hae : ∀ᵐ h : ℝ, h ≠ 0 := by
    rw [ae_iff]; simp
  have hord : (∫ h, (dampDiff h * autoCorr f h) * weilDensity |h|)
      = ∫ h, autoCorr f h * kcomb |h| := by
    refine integral_congr_ae (hae.mono fun h hh => ?_)
    have hpos : 0 < |h| := abs_pos.mpr hh
    have := damp_mul_density hpos
    unfold dampDiff
    calc (1 - Real.exp (-2 * |h|)) * autoCorr f h * weilDensity |h|
        = autoCorr f h * ((1 - Real.exp (-2 * |h|)) * weilDensity |h|) := by ring
      _ = autoCorr f h * kcomb |h| := by rw [this]
  have hkc : Continuous kcomb := by unfold kcomb; fun_prop
  rw [hord, corr_pairing hf hB hs hkc]
  -- split the double integral
  have hP : Continuous fun t : ℝ => 2 * Real.cosh (t / 2) := by fun_prop
  have hK : ∀ b : ℝ, Continuous fun t : ℝ => Real.exp (-b * t) := fun b => by fun_prop
  have iP := integrable_sq hf hB hs hP
  have i1 := integrable_sq hf hB hs (hK (1 / 2))
  have i3 := integrable_sq hf hB hs (hK (3 / 2))
  have i5 := integrable_sq hf hB hs (hK (5 / 2))
  have hcosh : ∀ u : ℝ, Real.cosh (|u| / 2) = Real.cosh (u / 2) := fun u => by
    rw [← Real.cosh_abs (u / 2), abs_div, abs_two]
  have hPe : Pform f = ∫ p : ℝ × ℝ, f p.1 * f p.2 * (2 * Real.cosh (|p.1 - p.2| / 2)) := by
    unfold Pform; simp_rw [hcosh]
  have hsplit : ∫ p : ℝ × ℝ, f p.1 * f p.2 * kcomb |p.1 - p.2|
      = Pform f - Kform (1 / 2) f - Kform (3 / 2) f - Kform (5 / 2) f := by
    unfold Kform
    rw [hPe]
    have hpt : ∀ p : ℝ × ℝ, f p.1 * f p.2 * kcomb |p.1 - p.2|
        = f p.1 * f p.2 * (2 * Real.cosh (|p.1 - p.2| / 2))
          - f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)
          - f p.1 * f p.2 * Real.exp (-(3 / 2) * |p.1 - p.2|)
          - f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|) := by
      intro p
      set u := |p.1 - p.2| with hu
      have hu0 : 0 ≤ u := abs_nonneg _
      have hc : 2 * Real.cosh (u / 2) = Real.exp (u / 2) + Real.exp (-(u / 2)) := by
        rw [Real.cosh_eq]; ring
      unfold kcomb
      have e1 : Real.exp (-(1 / 2) * u) = Real.exp (-(u / 2)) := by congr 1; ring
      have e3 : Real.exp (-(3 / 2) * u) = Real.exp (-(3 * u / 2)) := by congr 1; ring
      have e5 : Real.exp (-(5 / 2) * u) = Real.exp (-(5 * u / 2)) := by congr 1; ring
      rw [hc, e1, e3, e5]; ring
    simp_rw [hpt]
    have j1 : Integrable (fun p : ℝ × ℝ => f p.1 * f p.2 * (2 * Real.cosh (|p.1 - p.2| / 2))
        - f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) := iP.sub i1
    have j2 : Integrable (fun p : ℝ × ℝ => f p.1 * f p.2 * (2 * Real.cosh (|p.1 - p.2| / 2))
        - f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)
        - f p.1 * f p.2 * Real.exp (-(3 / 2) * |p.1 - p.2|)) := j1.sub i3
    rw [integral_sub j2 i5, integral_sub j1 i3, integral_sub iP i1]
  rw [hsplit]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hd : dampDiff (-Real.log n) = dampDiff (Real.log n) := by unfold dampDiff; rw [abs_neg]
  simp only [shiftForm, hd, dampDiff_log hn1]
  ring


/-- Support: for `f` supported in `[0,L]` the autocorrelation vanishes at lags `|h| ≥ L`, so the
atoms with `log n ≥ L` contribute nothing and the `n ≤ N` truncation of the prime sum is exactly
the sum over `log n < L` once `N ≥ e^L`. -/
theorem autoCorr_eq_zero_of_le {h : ℝ} (hs : ∀ x, x ∉ Icc 0 L → f x = 0) (hh : L ≤ |h|) :
    autoCorr f h = 0 := by
  unfold autoCorr
  have hae : ∀ᵐ x : ℝ, x ≠ 0 ∧ x ≠ L := by
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by rw [ae_iff]; simp
    have hL : ∀ᵐ x : ℝ, x ≠ L := by rw [ae_iff]; simp
    filter_upwards [h0, hL] with x a b using ⟨a, b⟩
  refine integral_eq_zero_of_ae (hae.mono fun x ⟨hx0, hxL⟩ => ?_)
  simp only [Pi.zero_apply]
  by_cases hx : x ∈ Icc 0 L
  · have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hxl : x < L := lt_of_le_of_ne hx.2 hxL
    have : x + h ∉ Icc 0 L := by
      intro hm
      rcases le_abs'.mp hh with h1 | h1 <;> linarith [hm.1, hm.2]
    simp [hs _ this]
  · simp [hs x hx]

end GppUndampingTransfer

#print axioms GppUndampingTransfer.damp_mul_density
#print axioms GppUndampingTransfer.corr_pairing
#print axioms GppUndampingTransfer.undamping_transfer
#print axioms GppUndampingTransfer.autoCorr_eq_zero_of_le
