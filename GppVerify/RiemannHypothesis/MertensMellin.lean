import GppVerify.RiemannHypothesis.MoebiusBoundaryDatum
import GppVerify.RiemannHypothesis.OneSidedPsiRH
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.MellinTransform

/-!
# The reflection coefficient `M_N` and zero-freeness

`MoebiusBoundaryDatum` shows that the Möbius dilation orbit of `{1/x}` is, on `x ≥ 1/N`, the pole
state `x^0` plus `-M_N` times the shadow state `x^{-1}`, with `M_N = Σ_{k ≤ N} μ(k)/k`.  This
module proves that the decay of the shadow-state coefficient controls the zeros:

* `mertens_bound`: `|M_N| ≤ 2`.
* `lseries_mul_zeta`: for `0 < re s`, `L(μ/n, s) · ζ(1 + s) = 1`.
* `abel`: `L(μ/n, s) = s ∫_1^∞ M(t) t^{-s-1} dt`, with `M(t) = Σ_{k ≤ ⌊t⌋} μ(k)/k`.
* `mul_mertensInt_eq_one`: for `0 < re s`, `s · ζ(1+s) · I(s) = 1`, `I(s) = ∫_1^∞ M(t) t^{-s-1} dt`.
* `zeta_ne_zero_of_mertens_decay`: if `|M(t)| ≤ C t^{-σ}` for `t ≥ 1` with `0 < σ`, then
  `ζ(ρ) ≠ 0` for `1 - σ < re ρ`.
* `riemannHypothesis_of_mertens_decay`: if `M(t) = O(t^{-1/2+ε})` for every `ε > 0`, then the
  Riemann Hypothesis holds.

The hypothesis is a statement about the Möbius function only; no zero of `ζ` is used.
-/

open Complex MeasureTheory Filter Topology ArithmeticFunction
open Finset (Icc Ioc)
open scoped ArithmeticFunction.Moebius

namespace GppMertensMellin

/-- The coefficients `μ(n)/n`. -/
noncomputable def coef (n : ℕ) : ℂ := (μ n : ℂ) / n

/-- The partial sum `M(t) = Σ_{k ≤ ⌊t⌋} μ(k)/k`. -/
noncomputable def mert (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, coef k

theorem sum_coef_eq (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, coef k = ((GppMoebiusBoundary.mertens n : ℝ) : ℂ) := by
  unfold GppMoebiusBoundary.mertens coef
  have : Finset.Icc 1 n = Finset.Ioc 0 n := by ext k; simp [Nat.succ_le_iff]
  rw [this]
  push_cast
  rfl

theorem abs_orbit_le (N : ℕ) (x : ℝ) : |GppMoebiusBoundary.orbit N x| ≤ N := by
  unfold GppMoebiusBoundary.orbit
  rw [abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.Ioc 0 N, |(μ k : ℝ) * Int.fract (1 / ((k : ℝ) * x))|
      ≤ ∑ k ∈ Finset.Ioc 0 N, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [abs_mul]
        have h1 : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have h2 : |Int.fract (1 / ((k : ℝ) * x))| ≤ 1 := by
          rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
        calc |(μ k : ℝ)| * |Int.fract (1 / ((k : ℝ) * x))| ≤ 1 * 1 :=
              mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = N := by simp

theorem mertens_bound {n : ℕ} (hn : 1 ≤ n) : |GppMoebiusBoundary.mertens n| ≤ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact_mod_cast hn
  have hN : 1 / (1 / (n : ℝ)) ≤ n := by rw [one_div_one_div]
  have h := GppMoebiusBoundary.orbit_exact hx0 hx1 hN
  have hab := abs_orbit_le n (1 / (n : ℝ))
  rw [h] at hab
  have : GppMoebiusBoundary.mertens n / (1 / (n : ℝ)) = n * GppMoebiusBoundary.mertens n := by
    field_simp
  rw [this] at hab
  have h3 : |(n : ℝ) * GppMoebiusBoundary.mertens n| ≤ n + 1 := by
    have := abs_sub_abs_le_abs_sub (1 : ℝ) (1 - n * GppMoebiusBoundary.mertens n)
    have h4 : |(n : ℝ) * GppMoebiusBoundary.mertens n| = |1 - (1 - n * GppMoebiusBoundary.mertens n)| := by
      congr 1; ring
    rw [h4]
    calc |1 - (1 - (n : ℝ) * GppMoebiusBoundary.mertens n)| ≤ |(1 : ℝ)| + |1 - n * GppMoebiusBoundary.mertens n| := by
          have := abs_sub (1 : ℝ) (1 - n * GppMoebiusBoundary.mertens n)
          exact this
      _ ≤ n + 1 := by rw [abs_one]; linarith
  rw [abs_mul, Nat.abs_cast] at h3
  have h5 : (n : ℝ) * |GppMoebiusBoundary.mertens n| ≤ n + 1 := h3
  have h6 : (n : ℝ) * |GppMoebiusBoundary.mertens n| ≤ (n : ℝ) * 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact le_of_mul_le_mul_left h6 hn0

theorem term_coef_eq (s : ℂ) (n : ℕ) :
    LSeries.term (fun k => coef k) s n = LSeries.term (fun k => (μ k : ℂ)) (s + 1) n := by
  unfold LSeries.term
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    unfold coef
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [cpow_add _ _ hn0, cpow_one]
    field_simp

theorem lseries_coef_eq (s : ℂ) :
    LSeries (fun k => coef k) s = LSeries (fun k => (μ k : ℂ)) (s + 1) := by
  unfold LSeries
  exact tsum_congr (term_coef_eq s)

theorem summable_coef {s : ℂ} (hs : 0 < s.re) : LSeriesSummable (fun k => coef k) s := by
  have h : LSeriesSummable (fun k => (μ k : ℂ)) (s + 1) := by
    have := ArithmeticFunction.LSeriesSummable_moebius_iff (s := s + 1)
    exact this.2 (by simp; linarith)
  unfold LSeriesSummable at h ⊢
  exact h.congr (fun n => (term_coef_eq s n).symm)

/-- `L(μ/n, s) · ζ(1 + s) = 1` for `0 < re s`. -/
theorem lseries_mul_zeta {s : ℂ} (hs : 0 < s.re) :
    LSeries (fun k => coef k) s * riemannZeta (s + 1) = 1 := by
  have hs1 : 1 < (s + 1).re := by simp; linarith
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs1
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs1] at h
  rw [lseries_coef_eq, mul_comm]
  exact h

theorem partial_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, coef k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.rpow_zero, norm_one, mul_one, sum_coef_eq, Complex.norm_real, Real.norm_eq_abs]
  exact mertens_bound hn

/-- **Abel summation.** `L(μ/n, s) = s ∫_1^∞ M(t) t^{-s-1} dt` for `0 < re s`. -/
theorem abel {s : ℂ} (hs : 0 < s.re) :
    LSeries (fun k => coef k) s = s * ∫ t in Set.Ioi (1 : ℝ), mert t * (t : ℂ) ^ (-(s + 1)) :=
  LSeries_eq_mul_integral (fun k => coef k) le_rfl hs (summable_coef hs) partial_isBigO

/-- `M` on `(1, ∞)`, zero elsewhere. -/
noncomputable def mertTail (t : ℝ) : ℂ := (Set.Ioi (1 : ℝ)).indicator mert t

/-- `I(s) = ∫_1^∞ M(t) t^{-s-1} dt`, as a Mellin transform. -/
noncomputable def mertInt (s : ℂ) : ℂ := mellin mertTail (-s)

theorem mertInt_eq (s : ℂ) :
    mertInt s = ∫ t in Set.Ioi (1 : ℝ), mert t * (t : ℂ) ^ (-(s + 1)) := by
  unfold mertInt mellin mertTail
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : t ∈ Set.Ioi (1 : ℝ)
  · have ht0 : t ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.2 (lt_trans one_pos ht)
    simp only [Set.indicator_of_mem ht, Set.indicator_of_mem ht0, smul_eq_mul]
    ring_nf
  · simp only [Set.indicator_of_notMem ht, smul_eq_mul]
    by_cases ht0 : t ∈ Set.Ioi (0 : ℝ)
    · simp [Set.indicator_of_mem ht0, Set.indicator_of_notMem ht]
    · simp [Set.indicator_of_notMem ht0]

theorem measurable_mert : Measurable mert := by
  have : mert = fun t => (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, coef k) ⌊t⌋₊ := rfl
  rw [this]
  exact (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, coef k)).comp
    (Nat.measurable_floor (R := ℝ))

theorem norm_mert_le {t : ℝ} (ht : 1 ≤ t) : ‖mert t‖ ≤ 2 := by
  unfold mert
  rw [sum_coef_eq, Complex.norm_real, Real.norm_eq_abs]
  exact mertens_bound (Nat.le_floor (by simpa using ht))

theorem differentiableAt_mertInt {σ C : ℝ}
    (hC : ∀ t : ℝ, 1 ≤ t → ‖mert t‖ ≤ C * t ^ (-σ)) {s : ℂ} (hs : -σ < s.re) :
    DifferentiableAt ℂ mertInt s := by
  have hmeas : Measurable mertTail := measurable_mert.indicator measurableSet_Ioi
  have hb : ∀ t, ‖mertTail t‖ ≤ 2 := by
    intro t; unfold mertTail
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht]; exact norm_mert_le (Set.mem_Ioi.1 ht).le
    · rw [Set.indicator_of_notMem ht]; simp
  have hm : DifferentiableAt ℂ (mellin mertTail) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := σ) (b := -s.re - 1)
    · rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
      intro k _ hk
      exact IntegrableOn.of_bound hk.measure_lt_top hmeas.aestronglyMeasurable 2
        (Eventually.of_forall hb)
    · refine Asymptotics.IsBigO.of_bound C ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      have : mertTail t = mert t := by unfold mertTail; rw [Set.indicator_of_mem (Set.mem_Ioi.2 ht)]
      rw [this, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
      exact hC t ht.le
    · simp; linarith
    · refine Asymptotics.IsBigO.of_bound 0 ?_
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (one_pos : (0 : ℝ) < 1))] with t ht
      have : t ∉ Set.Ioi (1 : ℝ) := fun h => absurd (Set.mem_Ioi.1 h) (not_lt.2 (le_of_lt ht))
      unfold mertTail
      rw [Set.indicator_of_notMem this]; simp
    · simp
  have : mertInt = fun s => mellin mertTail (-s) := rfl
  rw [this]
  exact hm.comp s differentiableAt_id.neg

/-- `Z(s) = 1 + s ζ₀(s + 1)`, the entire function equal to `s ζ(1 + s)` for `s ≠ 0`. -/
noncomputable def Z (s : ℂ) : ℂ := 1 + s * riemannZeta₀ (s + 1)

theorem Z_eq {s : ℂ} (hs : s ≠ 0) : Z s = s * riemannZeta (s + 1) := by
  have hs1 : s + 1 ≠ 1 := by intro h; apply hs; linear_combination h
  rw [riemannZeta_eq_inv_sub_add hs1]
  unfold Z
  have : s + 1 - 1 = s := by ring
  rw [this]
  field_simp

theorem mul_mertInt_Z {s : ℂ} (hs : 0 < s.re) : mertInt s * Z s = 1 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have h1 := abel hs
  have h2 := lseries_mul_zeta hs
  rw [h1, ← mertInt_eq] at h2
  rw [Z_eq hs0]
  linear_combination h2

theorem differentiable_Z : Differentiable ℂ Z := by
  intro s
  unfold Z
  exact (differentiableAt_const _).add (differentiableAt_id.mul
    ((differentiable_riemannZeta₀ (s + 1)).comp s (differentiableAt_id.add_const 1)))

/-- **Continuation of `s ζ(1+s) I(s) = 1`.** If `|M(t)| ≤ C t^{-σ}` for `t ≥ 1`, then
`I(s) · Z(s) = 1` on all of `re s > -σ`. -/
theorem mertInt_mul_Z_eq_one {σ C : ℝ} (hσ : 0 < σ)
    (hC : ∀ t : ℝ, 1 ≤ t → ‖mert t‖ ≤ C * t ^ (-σ)) {s : ℂ} (hs : -σ < s.re) :
    mertInt s * Z s = 1 := by
  set V : Set ℂ := {z | -σ < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : IsPreconnected V := (convex_halfSpace_re_gt (-σ)).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun z => mertInt z * Z z) V :=
    DifferentiableOn.analyticOnNhd (fun z hz => ((differentiableAt_mertInt hC hz).mul
      (differentiable_Z z)).differentiableWithinAt) hVo
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) V := fun z _ => analyticAt_const
  have h1 : (1 : ℂ) ∈ V := by
    show -σ < (1 : ℂ).re
    simp
    linarith
  have hev : (fun z => mertInt z * Z z) =ᶠ[𝓝 (1 : ℂ)] fun _ => (1 : ℂ) := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re)] with z hz
    exact mul_mertInt_Z hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hVc h1 hev hs

/-- **Decay of the shadow-state coefficient excludes zeros.** If `|M(t)| ≤ C t^{-σ}` for `t ≥ 1`
with `0 < σ`, then `ζ(ρ) ≠ 0` whenever `1 - σ < re ρ`. -/
theorem zeta_ne_zero_of_mertens_decay {σ C : ℝ} (hσ : 0 < σ)
    (hC : ∀ t : ℝ, 1 ≤ t → ‖mert t‖ ≤ C * t ^ (-σ)) {ρ : ℂ} (hρ : 1 - σ < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  intro hz
  by_cases hρ1 : ρ = 1
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [hρ1]; simp) hz
  · set s : ℂ := ρ - 1 with hs
    have hs0 : s ≠ 0 := sub_ne_zero.2 hρ1
    have hre : -σ < s.re := by rw [hs, Complex.sub_re, Complex.one_re]; linarith
    have h := mertInt_mul_Z_eq_one hσ hC hre
    have hρs : s + 1 = ρ := by rw [hs]; ring
    rw [Z_eq hs0, hρs, hz, mul_zero, mul_zero] at h
    exact zero_ne_one h

/-- **The Riemann Hypothesis from decay of the shadow-state coefficient.** If for every
`ε > 0` there is `C` with `|M(t)| ≤ C t^{-(1/2 - ε)}` for `t ≥ 1`, where
`M(t) = Σ_{k ≤ t} μ(k)/k`, then the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_mertens_decay
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖mert t‖ ≤ C * t ^ (-(1 / 2 - ε))) : RiemannHypothesis := by
  apply GppOneSidedRH.riemannHypothesis_of_ne_zero
  intro ρ hρ
  by_cases h1 : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · have h1 := not_le.1 h1
    set ε : ℝ := (ρ.re - 1 / 2) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hε1 : ε < 1 / 2 := by rw [hε]; linarith
    obtain ⟨C, hC⟩ := h ε hε0 hε1
    exact zeta_ne_zero_of_mertens_decay (by linarith) hC (by rw [hε]; linarith)

end GppMertensMellin

#print axioms GppMertensMellin.mertInt_mul_Z_eq_one
#print axioms GppMertensMellin.zeta_ne_zero_of_mertens_decay
#print axioms GppMertensMellin.riemannHypothesis_of_mertens_decay
