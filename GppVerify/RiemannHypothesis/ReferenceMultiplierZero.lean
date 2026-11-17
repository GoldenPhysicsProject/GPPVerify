import GppVerify.RiemannHypothesis.DigammaVerticalMonotone
import Mathlib.NumberTheory.ZetaValues

/-!
# The reference multiplier `m_ref(λ) = Re ψ(5/4 + iλ/2) − log π` has exactly one zero

GPT's reference multiplier (Turbo relays `fe9d9b5`/`f7f6242`; cleared candidate (2), second half):
`m_ref(λ) = Re ψ(5/4 + iλ/2) − log π`, strictly increasing, negative at `0`, with a single zero
`λ* ≈ 6.1258715695…`. This file proves, **unconditionally**:

* `mref_strictMonoOn`: `m_ref` is strictly increasing on `[0, ∞)` (from `re_digamma_strictMonoOn`);
* `mref_zero_neg`: `m_ref(0) < 0` (series upper bound by `a·ζ(2) = (5/4)·π²/6`, `γ > ½`, `log π > 1`);
* `mref_twenty_pos`: `m_ref(20) > 0` (kernel-checked rational partial sum of the first 20 series terms,
  all nonnegative for `a ≥ 1`, against `γ < 0.57749` and `log π < 1.1448`);
* `exists_unique_zero`: there is exactly one `λ* ≥ 0` with `m_ref(λ*) = 0`, and `0 < λ* < 20`; `m_ref < 0` on
  `[0, λ*)` and `m_ref > 0` on `(λ*, ∞)`.

**Scope.** Existence and uniqueness of the crossing with the coarse bracket `(0, 20)`. The digits
`6.12587…` are **not** certified here, and `m_ref` is not identified with the reference multiplier of the
Weil form; nothing about positivity of the Weil form.

No `sorry`, no axiom.
-/

open Complex Set

noncomputable section

namespace GppDigammaVertical

/-- `y ↦ Re ψ(a + iy)` is continuous for `a > 0`. -/
theorem continuous_re_digamma_pt {a : ℝ} (ha : 0 < a) :
    Continuous fun y : ℝ => (Complex.digamma (pt a y)).re := by
  set U : Set ℂ := {s | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma U := by
    intro s hs
    have : ∀ m : ℕ, s ≠ -m := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hs' : 0 < s.re := hs
      linarith
    exact (Complex.differentiableAt_Gamma s this).differentiableWithinAt
  have hanal : AnalyticOnNhd ℂ Complex.Gamma U := hdiff.analyticOnNhd hUo
  have hderiv : ContinuousOn (deriv Complex.Gamma) U := (hanal.deriv).continuousOn
  have hGcont : ContinuousOn Complex.Gamma U := hdiff.continuousOn
  have hdig : ContinuousOn Complex.digamma U := by
    have : Complex.digamma = fun s => deriv Complex.Gamma s / Complex.Gamma s := by
      funext s; simp [Complex.digamma_def, logDeriv_apply]
    rw [this]
    exact hderiv.div hGcont (fun s hs => Complex.Gamma_ne_zero_of_re_pos hs)
  have hpt : Continuous fun y : ℝ => pt a y := by unfold pt; fun_prop
  have hmem : ∀ y : ℝ, pt a y ∈ U := fun y => by
    show 0 < (pt a y).re
    rw [pt_re]; exact ha
  exact Complex.continuous_re.comp (hdig.comp_continuous hpt hmem)

/-- The reference multiplier `m_ref(λ) = Re ψ(5/4 + iλ/2) − log π`. -/
def mref (l : ℝ) : ℝ := (Complex.digamma (pt (5 / 4) (l / 2))).re - Real.log Real.pi

theorem mref_continuous : Continuous mref := by
  unfold mref
  have := (continuous_re_digamma_pt (a := 5 / 4) (by norm_num)).comp (continuous_id.div_const 2)
  exact this.sub continuous_const

theorem mref_strictMonoOn : StrictMonoOn mref (Ici 0) := by
  intro s hs t ht hst
  have h := re_digamma_strictMonoOn (a := 5 / 4) (by norm_num)
    (Set.mem_Ici.mpr (by have : (0 : ℝ) ≤ s := hs; linarith))
    (Set.mem_Ici.mpr (by have : (0 : ℝ) ≤ t := ht; linarith)) (by linarith : s / 2 < t / 2)
  unfold mref
  linarith

/-- `Tn ≥ 0` for `a ≥ 1`. -/
theorem Tn_nonneg {a : ℝ} (ha : 1 ≤ a) (y : ℝ) (n : ℕ) : 0 ≤ Tn a y n := by
  unfold Tn
  have hn : (0 : ℝ) < (n : ℝ) + 1 + a := by positivity
  have h1 : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + y ^ 2) ≤ 1 / ((n : ℝ) + 1 + a) := by
    rw [div_le_div_iff₀ (by positivity) hn]
    nlinarith [sq_nonneg y]
  have h2 : 1 / ((n : ℝ) + 1 + a) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-! ### `m_ref(0) < 0` -/

theorem Tn_zero_le {a : ℝ} (ha : 0 < a) (n : ℕ) : Tn a 0 n ≤ a * (1 / ((n : ℝ) + 1) ^ 2) := by
  unfold Tn
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (n : ℝ) + 1 + a := by positivity
  have : 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + 0 ^ 2) =
      a / (((n : ℝ) + 1) * ((n : ℝ) + 1 + a)) := by
    field_simp; ring
  rw [this, mul_one_div]
  apply div_le_div_of_nonneg_left ha.le (by positivity)
  nlinarith

theorem mref_zero_neg : mref 0 < 0 := by
  unfold mref
  have ha : (0 : ℝ) < 5 / 4 := by norm_num
  have h0 : (0 : ℝ) / 2 = 0 := by norm_num
  rw [h0, re_digamma_series ha 0]
  have hsum : Summable fun n : ℕ => (5 / 4 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    have : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by simpa using h
    exact this.mul_left _
  have hle : ∑' n : ℕ, Tn (5 / 4) 0 n ≤ ∑' n : ℕ, (5 / 4 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) :=
    (summable_Tn ha 0).tsum_le_tsum (fun n => Tn_zero_le ha n) hsum
  have hz : ∑' n : ℕ, (1 / ((n : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two
    have h' := (hasSum_nat_add_iff' 1).2 h
    have hsum1 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
      simpa [Finset.sum_range_one] using h'
    exact hsum1.tsum_eq
  have hsc : ∑' n : ℕ, (5 / 4 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) = 5 / 4 * (Real.pi ^ 2 / 6) := by
    rw [tsum_mul_left, hz]
  rw [hsc] at hle
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 9.9225 := by nlinarith
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlog : 1 < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt hpi0]
    have := Real.exp_one_lt_d9
    have := Real.pi_gt_three
    linarith
  have hfrac : (5 / 4 : ℝ) / ((5 / 4) ^ 2 + 0 ^ 2) = 4 / 5 := by norm_num
  rw [hfrac]
  nlinarith

/-! ### `m_ref(20) > 0` -/

/-- Rational version of the series term at `a = 5/4`, `y = 10`. -/
def TnQ (n : ℕ) : ℚ :=
  1 / ((n : ℚ) + 1) - ((n : ℚ) + 1 + 5 / 4) / (((n : ℚ) + 1 + 5 / 4) ^ 2 + 10 ^ 2)

theorem TnQ_cast (n : ℕ) : ((TnQ n : ℚ) : ℝ) = Tn (5 / 4) 10 n := by
  unfold TnQ Tn; push_cast; ring

/-- **Kernel-checked:** the first 20 terms exceed `7/4`. -/
theorem partial_TnQ : (7 / 4 : ℚ) < ∑ n ∈ Finset.range 20, TnQ n := by decide +kernel

theorem mref_twenty_pos : 0 < mref 20 := by
  unfold mref
  have ha : (0 : ℝ) < 5 / 4 := by norm_num
  have h20 : (20 : ℝ) / 2 = 10 := by norm_num
  rw [h20, re_digamma_series ha 10]
  have hq : ((7 / 4 : ℚ) : ℝ) < ((∑ n ∈ Finset.range 20, TnQ n : ℚ) : ℝ) :=
    Rat.cast_lt.mpr partial_TnQ
  have hsum : ((∑ n ∈ Finset.range 20, TnQ n : ℚ) : ℝ) = ∑ n ∈ Finset.range 20, Tn (5 / 4) 10 n := by
    push_cast
    exact Finset.sum_congr rfl fun n _ => by simpa using TnQ_cast n
  rw [hsum] at hq
  have hle : ∑ n ∈ Finset.range 20, Tn (5 / 4) 10 n ≤ ∑' n : ℕ, Tn (5 / 4) 10 n :=
    (summable_Tn ha 10).sum_le_tsum _ fun n _ => Tn_nonneg (by norm_num) 10 n
  have hγ := GppFirstPrime.euler_lt
  have hlog := GppFirstPrime.log_pi_lt
  have hfrac : (5 / 4 : ℝ) / ((5 / 4) ^ 2 + 10 ^ 2) < 1 / 80 := by norm_num
  norm_num at hq hγ hlog hfrac ⊢
  linarith

/-- **Exactly one zero.** -/
theorem exists_unique_zero : ∃! l : ℝ, 0 ≤ l ∧ mref l = 0 := by
  have hcont : ContinuousOn mref (Icc 0 20) := mref_continuous.continuousOn
  obtain ⟨l, hl, hz⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 20) hcont
    (show (0 : ℝ) ∈ Ioo (mref 0) (mref 20) from ⟨mref_zero_neg, mref_twenty_pos⟩)
  refine ⟨l, ⟨hl.1.le, hz⟩, ?_⟩
  rintro u ⟨hu, hzu⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := mref_strictMonoOn (Set.mem_Ici.mpr hu) (Set.mem_Ici.mpr hl.1.le) h
    rw [hzu, hz] at this; exact lt_irrefl _ this
  · have := mref_strictMonoOn (Set.mem_Ici.mpr hl.1.le) (Set.mem_Ici.mpr hu) h
    rw [hzu, hz] at this; exact lt_irrefl _ this

/-- The zero `λ*` of the reference multiplier. -/
def lamStar : ℝ := Classical.choose exists_unique_zero.exists

theorem lamStar_nonneg : 0 ≤ lamStar := (Classical.choose_spec exists_unique_zero.exists).1
theorem mref_lamStar : mref lamStar = 0 := (Classical.choose_spec exists_unique_zero.exists).2

theorem lamStar_pos : 0 < lamStar := by
  rcases lamStar_nonneg.eq_or_lt with h | h
  · have h1 : mref lamStar < 0 := by rw [← h]; exact mref_zero_neg
    rw [mref_lamStar] at h1
    exact absurd h1 (lt_irrefl _)
  · exact h

theorem lamStar_lt_twenty : lamStar < 20 := by
  by_contra h
  rw [not_lt] at h
  have h20 : mref 20 ≤ mref lamStar :=
    mref_strictMonoOn.monotoneOn (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 20))
      (Set.mem_Ici.mpr lamStar_nonneg) h
  rw [mref_lamStar] at h20
  have := mref_twenty_pos
  linarith

/-- `m_ref < 0` on `[0, λ*)`. -/
theorem mref_neg_of_lt {l : ℝ} (h0 : 0 ≤ l) (h : l < lamStar) : mref l < 0 := by
  have := mref_strictMonoOn (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr lamStar_nonneg) h
  rwa [mref_lamStar] at this

/-- `m_ref > 0` on `(λ*, ∞)`. -/
theorem mref_pos_of_gt {l : ℝ} (h : lamStar < l) : 0 < mref l := by
  have := mref_strictMonoOn (Set.mem_Ici.mpr lamStar_nonneg)
    (Set.mem_Ici.mpr (lamStar_nonneg.trans h.le)) h
  rwa [mref_lamStar] at this

end GppDigammaVertical

#print axioms GppDigammaVertical.exists_unique_zero
#print axioms GppDigammaVertical.lamStar_lt_twenty
#print axioms GppDigammaVertical.mref_pos_of_gt
#print axioms GppDigammaVertical.mref_zero_neg
#print axioms GppDigammaVertical.mref_twenty_pos
