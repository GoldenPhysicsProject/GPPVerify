import GppVerify.RiemannHypothesis.RungZeroPositivity

/-!
# Unconditional Weil positivity on `[-1/16, 1/16]`

**Main theorem** (`reflectionPositiveOnRung_one_div_eight`): `ReflectionPositiveOnRung (1/8)`.
For every smooth compactly supported `f` vanishing outside `[-1/16, 1/16]`,

  `weilForm (autocorr f) ≥ (1/20) · ∫ f²`   (`weilForm_autocorr_ge_wide`).

This widens `GppRungZeroPositivity.reflectionPositiveOnRung_one_div_128` by a factor of 16. It
has no named premises. The window is below `log 2`, so no prime enters: the theorem says that
the pole and archimedean terms dominate there, and says nothing about the zeros.

## What is sharper than the `1/128` proof

Write `a = autocorr f`, `a₀ = a(0) = ∫ f²`, `S = ∫ f` and `L = 1/8`.

1. **Tail.** `1/(1 - e^{-2u}) ≥ (1 + u)/(2u)` on `(0, 1)`, from
   `log(1+u) - log(1-u) ≥ 2u`. `e^{-x} ≥ 1 - x + x²/2 - x³/6 - (5/96)x⁴` on `[0, 1]`, from
   `Real.exp_bound`. Integrated against an explicit antiderivative, this gives
   `2∫_{1/8}^∞ e^{-u/2}/(1-e^{-2u}) du ≥ 3 log 2 + (rational)`.
2. **Dirichlet gain inside the support.** On `(0, L]` the kernel is at least
   `w_L = (1 - L/2)/(2L)`. Also `∫_0^L (1 - a/a₀) = L - S²/(2a₀)`, because `a` is even and
   `∫ a = S²`.
3. **Pole.** `poleTerm a ≥ 2S² - L³ a₀`, using `cosh x - 1 ≤ x²` for `|x| ≤ 1`.
4. **Variance.** `S² ≤ L a₀` (`sq_integral_le`), from `0 ≤ ∫_{[-L/2, L/2]} (f - S/L)²`. It
   absorbs the `S²` terms, whose net coefficient `2 - w_L` is negative.
5. **Constants.** `γ < H₃₂ - 5 log 2` (`Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'`),
   `log π ≤ 2 log 2 + π/4 - 1`, `π < 3.141593`, and Mathlib's nine-digit `log 2` bounds.

The total margin is `≥ 0.066`, and the theorem claims `1/20`.

Unconditional. No `sorry`, no axioms beyond Lean's standard three.
-/

namespace GppRungZeroWide

open Real MeasureTheory Set Filter GppArchimedeanFloor GppArithmeticReflection GppWeilLadder
  GppMeyerSpectralWeil GppRungZeroPositivity
open scoped ContDiff

/-! ## Elementary inequalities -/

/-- `1/(1 - e^{-2u}) ≥ (1 + u)/(2u)` for `0 < u < 1`. -/
theorem inv_one_sub_exp_ge {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    (1 + u) / (2 * u) ≤ 1 / (1 - Real.exp (-2 * u)) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := u) (by rw [abs_of_pos h0]; exact h1)
  have h2u : 2 * u ≤ Real.log (1 + u) - Real.log (1 - u) := by
    have := le_hasSum hs 0 (fun k _ => by positivity)
    simpa using this
  rw [← Real.log_div (by linarith) (by linarith)] at h2u
  have hq : 0 < (1 + u) / (1 - u) := div_pos (by linarith) (by linarith)
  have hexp : Real.exp (2 * u) ≤ (1 + u) / (1 - u) := by
    calc Real.exp (2 * u) ≤ Real.exp (Real.log ((1 + u) / (1 - u))) := Real.exp_le_exp.mpr h2u
      _ = (1 + u) / (1 - u) := Real.exp_log hq
  have hneg : (1 - u) / (1 + u) ≤ Real.exp (-2 * u) := by
    have he : Real.exp (-2 * u) = (Real.exp (2 * u))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [he]
    have := inv_anti₀ (Real.exp_pos _) hexp
    rwa [inv_div] at this
  have hd := one_sub_exp_pos h0
  have hle : 1 - Real.exp (-2 * u) ≤ 2 * u / (1 + u) := by
    have : 2 * u / (1 + u) = 1 - (1 - u) / (1 + u) := by field_simp; ring
    rw [this]; linarith
  calc (1 + u) / (2 * u) = 1 / (2 * u / (1 + u)) := by field_simp
    _ ≤ 1 / (1 - Real.exp (-2 * u)) := one_div_le_one_div_of_le hd hle

/-- `e^{-x} ≥ 1 - x + x²/2 - x³/6 - (5/96) x⁴` for `0 ≤ x ≤ 1`. -/
theorem exp_neg_ge_poly {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 - 5 / 96 * x ^ 4 ≤ Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
    (n := 4) (by norm_num)
  rw [abs_le] at h
  obtain ⟨h, -⟩ := h
  rw [abs_neg, abs_of_nonneg h0] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [h]

/-- `cosh x - 1 ≤ x²` for `|x| ≤ 1`. -/
theorem cosh_sub_one_le {x : ℝ} (hx : |x| ≤ 1) : Real.cosh x - 1 ≤ x ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq x
  have hy : |x ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_abs x, abs_nonneg x]
  have h2 := Real.exp_bound hy (n := 1) (by norm_num)
  rw [abs_le] at h2
  obtain ⟨-, h2⟩ := h2
  rw [abs_of_nonneg (by positivity)] at h2
  norm_num [Finset.sum_range_succ] at h2
  linarith

/-! ## The tail of the Dirichlet kernel beyond `1/8` -/

/-- The integrand `q(u) ≤ e^{-u/2}/(1-e^{-2u})` on `(0, 1)`. -/
noncomputable def q (u : ℝ) : ℝ :=
  1 / 2 * u⁻¹ + 1 / 4 - 3 / 16 * u + 5 / 96 * u ^ 2 - 37 / 3072 * u ^ 3 - 5 / 3072 * u ^ 4

/-- Its antiderivative. -/
noncomputable def Q (u : ℝ) : ℝ :=
  1 / 2 * Real.log u + 1 / 4 * u - 3 / 32 * u ^ 2 + 5 / 288 * u ^ 3 - 37 / 12288 * u ^ 4
    - 1 / 3072 * u ^ 5

theorem q_le_kern {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : q u ≤ kern u := by
  have hA := inv_one_sub_exp_ge h0 h1
  have hB := exp_neg_ge_poly (x := u / 2) (by linarith) (by linarith)
  have hc : 0 ≤ (1 + u) / (2 * u) := by positivity
  have hq : q u = (1 - u / 2 + (u / 2) ^ 2 / 2 - (u / 2) ^ 3 / 6 - 5 / 96 * (u / 2) ^ 4) *
      ((1 + u) / (2 * u)) := by
    unfold q; field_simp; ring
  have he : Real.exp (-(u / 2)) = Real.exp (-u / 2) := by ring_nf
  rw [he] at hB
  unfold kern
  rw [hq, div_eq_mul_one_div (Real.exp (-u / 2))]
  calc _ ≤ Real.exp (-u / 2) * ((1 + u) / (2 * u)) := mul_le_mul_of_nonneg_right hB hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le

theorem hasDerivAt_Q {x : ℝ} (hx : 0 < x) : HasDerivAt Q (q x) x := by
  have h := ((((((Real.hasDerivAt_log hx.ne').const_mul (1 / 2 : ℝ)).add
    ((hasDerivAt_id x).const_mul (1 / 4 : ℝ))).sub
    ((hasDerivAt_pow 2 x).const_mul (3 / 32 : ℝ))).add
    ((hasDerivAt_pow 3 x).const_mul (5 / 288 : ℝ))).sub
    ((hasDerivAt_pow 4 x).const_mul (37 / 12288 : ℝ))).sub
    ((hasDerivAt_pow 5 x).const_mul (1 / 3072 : ℝ))
  have hfun : Q = ((((((fun y => 1 / 2 * Real.log y) + fun y => 1 / 4 * id y) -
      fun y => 3 / 32 * y ^ 2) + fun y => 5 / 288 * y ^ 3) - fun y => 37 / 12288 * y ^ 4) -
      fun y => 1 / 3072 * y ^ 5) := by
    funext y; simp only [Q, Pi.add_apply, Pi.sub_apply, id]
  rw [hfun]
  refine h.congr_deriv ?_
  unfold q; push_cast; field_simp; ring

theorem q_continuousOn : ContinuousOn q (Icc (1 / 8) 1) := by
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  unfold q
  exact (((((continuousAt_const.mul (continuousAt_inv₀ hx0)).add continuousAt_const).sub
    (continuousAt_const.mul continuousAt_id)).add
    (continuousAt_const.mul (continuousAt_id.pow 2))).sub
    (continuousAt_const.mul (continuousAt_id.pow 3))).sub
    (continuousAt_const.mul (continuousAt_id.pow 4)) |>.continuousWithinAt

theorem integral_q : ∫ u in Ioo (1 / 8 : ℝ) 1, q u = Q 1 - Q (1 / 8) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
  · rw [uIcc_of_le (by norm_num)] at hx
    exact hasDerivAt_Q (by linarith [hx.1])
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    exact q_continuousOn

/-- The rational part of the tail bound. -/
noncomputable def tailRat : ℝ :=
  2 * ((1 / 4 * 1 - 3 / 32 * 1 + 5 / 288 * 1 - 37 / 12288 * 1 - 1 / 3072 * 1) -
    (1 / 4 * (1 / 8) - 3 / 32 * (1 / 8) ^ 2 + 5 / 288 * (1 / 8) ^ 3 - 37 / 12288 * (1 / 8) ^ 4
      - 1 / 3072 * (1 / 8) ^ 5))
  + 4 * (1 - 1 / 2 + (1 / 2) ^ 2 / 2 - (1 / 2) ^ 3 / 6 - 5 / 96 * (1 / 2) ^ 4)

/-- **Tail bound.** `2∫_{1/8}^∞ e^{-u/2}/(1-e^{-2u}) du ≥ 3 log 2 + tailRat`. -/
theorem two_mul_integral_kern_ge_wide :
    3 * Real.log 2 + tailRat ≤ 2 * ∫ u in Ioi (1 / 8 : ℝ), kern u := by
  have hsplit : Ioi (1 / 8 : ℝ) = Ioo (1 / 8) 1 ∪ Ici 1 := (Ioo_union_Ici_eq_Ioi (by norm_num)).symm
  have hint := integrableOn_kern (L := 1 / 8) (by norm_num)
  have h1 : IntegrableOn kern (Ioo (1 / 8 : ℝ) 1) := hint.mono_set Ioo_subset_Ioi_self
  have h2 : IntegrableOn kern (Ici (1 : ℝ)) := hint.mono_set (Ici_subset_Ioi.mpr (by norm_num))
  have hU : ∫ u in Ioi (1 / 8 : ℝ), kern u =
      (∫ u in Ioo (1 / 8 : ℝ) 1, kern u) + ∫ u in Ici (1 : ℝ), kern u := by
    rw [hsplit]; exact setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
      simp only [mem_Ioo, mem_Ici] at hx hx'; linarith) measurableSet_Ici h1 h2
  have hqint : IntegrableOn q (Ioo (1 / 8 : ℝ) 1) :=
    q_continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnear : Q 1 - Q (1 / 8) ≤ ∫ u in Ioo (1 / 8 : ℝ) 1, kern u := by
    rw [← integral_q]
    exact setIntegral_mono_on hqint h1 measurableSet_Ioo
      (fun u hu => q_le_kern (by linarith [hu.1]) hu.2)
  have hfar : 4 * Real.exp (-(1 / 2)) ≤ 2 * ∫ u in Ici (1 : ℝ), kern u := by
    have hval : ∫ u in Ioi (1 : ℝ), Real.exp (-(1 / 2) * u) = 2 * Real.exp (-(1 / 2)) := by
      rw [integral_exp_mul_Ioi (by norm_num) 1]; ring_nf
    have hmono : ∫ u in Ioi (1 : ℝ), Real.exp (-(1 / 2) * u) ≤ ∫ u in Ici (1 : ℝ), kern u := by
      rw [integral_Ici_eq_integral_Ioi]
      exact setIntegral_mono_on (exp_neg_integrableOn_Ioi 1 (by norm_num))
        (h2.mono_set Ioi_subset_Ici_self) measurableSet_Ioi
        (fun u hu => kern_ge_exp (by simp at hu; linarith))
    linarith
  have hexp := exp_neg_ge_poly (x := 1 / 2) (by norm_num) (by norm_num)
  have hlog : Real.log (1 / 8 : ℝ) = -(3 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hQ : Q 1 - Q (1 / 8) = 3 / 2 * Real.log 2 +
      ((1 / 4 * 1 - 3 / 32 * 1 + 5 / 288 * 1 - 37 / 12288 * 1 - 1 / 3072 * 1) -
      (1 / 4 * (1 / 8) - 3 / 32 * (1 / 8) ^ 2 + 5 / 288 * (1 / 8) ^ 3 - 37 / 12288 * (1 / 8) ^ 4
        - 1 / 3072 * (1 / 8) ^ 5)) := by
    unfold Q; rw [Real.log_one, hlog]; ring
  rw [hU]
  unfold tailRat
  rw [hQ] at hnear
  linarith

/-! ## Autocorrelation: evenness, the integral over `(0, L]`, variance -/

theorem autocorr_neg (f : ℝ → ℝ) (u : ℝ) : autocorr f (-u) = autocorr f u := by
  unfold autocorr
  have h := integral_sub_right_eq_self (μ := volume) (fun y => f y * f (y + u)) u
  simp only [sub_add_cancel] at h
  simp only [sub_neg_eq_add]
  rw [← h]
  congr 1; funext y; ring

/-- `∫_{(0, L]} a = (∫ f)²/2` when `a` vanishes outside `[-L, L]`. -/
theorem integral_Ioc_autocorr {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {L : ℝ} (hL : 0 ≤ L) (hsupp : HasSupportIn (autocorr f) L) :
    ∫ u in Ioc 0 L, autocorr f u = (∫ y, f y) ^ 2 / 2 := by
  have hta : IsTestFunction (autocorr f) := GppAutocorrTransport.isTestFunction_autocorr ⟨hf, hc⟩
  have haint : Integrable (autocorr f) := hta.1.continuous.integrable_of_hasCompactSupport hta.2
  have htot := integral_autocorr hf hc
  have hsplit : ∫ u, autocorr f u = (∫ u in Iic 0, autocorr f u) + ∫ u in Ioi 0, autocorr f u := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi haint.integrableOn
      haint.integrableOn, Iic_union_Ioi, setIntegral_univ]
  have heven : ∫ u in Iic 0, autocorr f u = ∫ u in Ioi 0, autocorr f u := by
    have := integral_comp_neg_Ioi 0 (autocorr f)
    rw [neg_zero] at this
    rw [← this]
    congr 1; funext u; exact autocorr_neg f u
  have hIoi : ∫ u in Ioi 0, autocorr f u = ∫ u in Ioc 0 L, autocorr f u := by
    have hs : Ioi (0 : ℝ) = Ioc 0 L ∪ Ioi L := (Ioc_union_Ioi_eq_Ioi hL).symm
    rw [hs, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi haint.integrableOn
      haint.integrableOn]
    have hz : ∫ u in Ioi L, autocorr f u = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero (fun u hu => ?_)
      have hu : L < u := hu
      exact hsupp u (by rw [abs_of_pos (lt_of_le_of_lt hL hu)]; exact hu)
    rw [hz, add_zero]
  rw [← hIoi]
  linarith

/-- **Variance bound.** If `f` vanishes outside `[-L/2, L/2]`, `(∫ f)² ≤ L ∫ f²`. -/
theorem sq_integral_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ y : ℝ, L / 2 < |y| → f y = 0) :
    (∫ y, f y) ^ 2 ≤ L * ∫ y, f y ^ 2 := by
  set I := Icc (-(L / 2)) (L / 2) with hI
  have hout : ∀ y ∉ I, f y = 0 := by
    intro y hy
    apply hsupp
    rw [hI, mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  have hS : ∫ y in I, f y = ∫ y, f y := setIntegral_eq_integral_of_forall_compl_eq_zero hout
  have hA : ∫ y in I, f y ^ 2 = ∫ y, f y ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hout y hy]; ring)
  have hvol : volume.real I = L := by rw [hI, Real.volume_real_Icc_of_le (by linarith)]; ring
  have hfc : Continuous f := hf.continuous
  have i1 : IntegrableOn f I := hfc.continuousOn.integrableOn_Icc
  have i2 : IntegrableOn (fun y => f y ^ 2) I := (hfc.pow 2).continuousOn.integrableOn_Icc
  set S := ∫ y, f y
  set c := S / L
  have hnn : 0 ≤ ∫ y in I, (f y - c) ^ 2 := setIntegral_nonneg measurableSet_Icc
    (fun y _ => sq_nonneg _)
  have hexp : ∫ y in I, (f y - c) ^ 2 =
      (∫ y in I, f y ^ 2) - 2 * c * (∫ y in I, f y) + c ^ 2 * volume.real I := by
    have e : (fun y => (f y - c) ^ 2) = fun y => (f y ^ 2 - 2 * c * f y) + c ^ 2 := by
      funext y; ring
    have hi1 : IntegrableOn (fun y => f y ^ 2 - 2 * c * f y) I := i2.sub (i1.const_mul _)
    have hi2 : IntegrableOn (fun _ : ℝ => c ^ 2) I := integrableOn_const (by rw [hI]; simp)
    rw [e, integral_add hi1 hi2, integral_sub i2 (i1.const_mul _), integral_const_mul,
      setIntegral_const, smul_eq_mul]
    ring
  rw [hexp, hS, hA, hvol] at hnn
  have : 0 ≤ (∫ y, f y ^ 2) - S ^ 2 / L := by
    have e : (∫ y, f y ^ 2) - 2 * c * S + c ^ 2 * L = (∫ y, f y ^ 2) - S ^ 2 / L := by
      simp only [c]; field_simp; ring
    linarith
  have h2 : S ^ 2 / L ≤ ∫ y, f y ^ 2 := by linarith
  rw [div_le_iff₀ hL] at h2
  linarith

/-! ## The pole term with a quadratic penalty -/

theorem poleTerm_autocorr_ge_sharp {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {L : ℝ} (hL : 0 < L) (hL2 : L ≤ 2) (hsupp : HasSupportIn (autocorr f) L) :
    2 * (∫ y, f y) ^ 2 - L ^ 3 * autocorr f 0 ≤ poleTerm (autocorr f) := by
  set a := autocorr f with ha_def
  have hta : IsTestFunction a := GppAutocorrTransport.isTestFunction_autocorr ⟨hf, hc⟩
  have hac : Continuous a := hta.1.continuous
  have haint : Integrable a := hac.integrable_of_hasCompactSupport hta.2
  have hcosh : Integrable (fun u => a u * (2 * Real.cosh (u / 2) - 2)) :=
    (hac.mul (by fun_prop)).integrable_of_hasCompactSupport hta.2.mul_right
  set c : ℝ := a 0 * (L ^ 2 / 2) with hc_def
  have hbound : ∀ u, ‖a u * (2 * Real.cosh (u / 2) - 2)‖ ≤ (Icc (-L) L).indicator (fun _ => c) u := by
    intro u
    by_cases hu : u ∈ Icc (-L) L
    · rw [indicator_of_mem hu, Real.norm_eq_abs, abs_mul]
      have hu' : |u| ≤ L := abs_le.mpr hu
      have hx : |u / 2| ≤ 1 := by rw [abs_div, abs_two]; linarith
      have hch := cosh_sub_one_le hx
      have h1 := Real.one_le_cosh (u / 2)
      have hsq : (u / 2) ^ 2 ≤ L ^ 2 / 4 := by
        have : u ^ 2 ≤ L ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
        nlinarith
      have hk : |2 * Real.cosh (u / 2) - 2| ≤ L ^ 2 / 2 := by
        rw [abs_of_nonneg (by linarith)]; linarith
      exact mul_le_mul (abs_autocorr_le hf hc u) hk (abs_nonneg _) (autocorr_zero_nonneg f)
    · rw [indicator_of_notMem hu]
      have : L < |u| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hu
        rcases hu with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      simp [hsupp u this]
  have hind : Integrable ((Icc (-L) L).indicator (fun _ => c)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hnorm := norm_integral_le_of_norm_le hind (Filter.Eventually.of_forall hbound)
  rw [integral_indicator_const c measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul, Real.norm_eq_abs] at hnorm
  have hsplit : poleTerm a = 2 * (∫ u, a u) + ∫ u, a u * (2 * Real.cosh (u / 2) - 2) := by
    unfold poleTerm
    rw [← integral_const_mul, ← integral_add (haint.const_mul 2) hcosh]
    congr 1; funext u; ring
  have hsq : ∫ u, a u = (∫ y, f y) ^ 2 := by rw [ha_def, integral_autocorr hf hc]
  have := neg_abs_le (∫ u, a u * (2 * Real.cosh (u / 2) - 2))
  rw [hsplit, hsq]
  have e : (L - -L) * c = L ^ 3 * a 0 := by rw [hc_def]; ring
  rw [e] at hnorm
  linarith

/-! ## The archimedean term with the Dirichlet gain -/

/-- The weight `(1 - L/2)/(2L)`, a lower bound for the kernel on `(0, L]`. -/
noncomputable def wL (L : ℝ) : ℝ := (1 - L / 2) / (2 * L)

theorem kern_ge_wL {L u : ℝ} (hL : L ≤ 1) (hu0 : 0 < u) (huL : u ≤ L) : wL L ≤ kern u := by
  unfold wL kern
  have hd := one_sub_exp_pos hu0
  have hle : 1 - Real.exp (-2 * u) ≤ 2 * L := (one_sub_exp_le (u := u)).trans (by linarith)
  have he : 1 - L / 2 ≤ Real.exp (-u / 2) := by
    have := Real.add_one_le_exp (-u / 2); linarith
  have hnum : 0 ≤ 1 - L / 2 := by linarith
  calc (1 - L / 2) / (2 * L) ≤ (1 - L / 2) / (1 - Real.exp (-2 * u)) :=
        div_le_div_of_nonneg_left hnum hd hle
    _ ≤ Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) := div_le_div_of_nonneg_right he hd.le

/-- **Archimedean bound with the Dirichlet gain.** For `0 < L < 1` and `a = autocorr f`
vanishing outside `[-L, L]`, with `a(0) > 0`:
`A∞(a) ≥ a(0) (C∞ + 2∫_L^∞ kern + 2 w_L L) - w_L (∫ f)²`. -/
theorem archimedeanTerm_autocorr_ge_wide {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {L : ℝ} (hL : 0 < L) (hL1 : L < 1)
    (hsupp : HasSupportIn (autocorr f) L) (hpos : 0 < autocorr f 0) :
    autocorr f 0 * (archimedeanFloor + 2 * (∫ u in Ioi L, kern u) + 2 * wL L * L)
      - wL L * (∫ y, f y) ^ 2 ≤ archimedeanTerm (autocorr f) := by
  set a := autocorr f with ha_def
  have hta : IsTestFunction a := GppAutocorrTransport.isTestFunction_autocorr ⟨hf, hc⟩
  set r : ℝ → ℝ := fun u => a u / a 0 with hr
  have hr0 : r 0 = 1 := by simp only [hr]; exact div_self hpos.ne'
  have hrle : ∀ u, r u ≤ 1 := by
    intro u; simp only [hr]
    rw [div_le_one hpos]; exact (le_abs_self _).trans (abs_autocorr_le hf hc u)
  have hscale : ∀ u, archimedeanIntegrand a u = a 0 * archimedeanIntegrand r u := by
    intro u; unfold archimedeanIntegrand; simp only [hr]; field_simp
  have hintA := integrableOn_archimedeanIntegrand hta.1 hta.2
  have hintR : IntegrableOn (archimedeanIntegrand r) (Ioi 0) := by
    have h' : IntegrableOn (fun u => archimedeanIntegrand a u / a 0) (Ioi 0) :=
      hintA.div_const _
    refine h'.congr_fun (fun u _ => ?_) measurableSet_Ioi
    show archimedeanIntegrand a u / a 0 = archimedeanIntegrand r u
    rw [hscale, mul_div_cancel_left₀ _ hpos.ne']
  have harch : archimedeanTerm a = a 0 * archimedeanTerm r := by
    unfold archimedeanTerm
    simp only [hscale, integral_const_mul, hr0]
    simp only [hr]; field_simp
  have hdec := archimedean_decomposition r hr0 hintR
  have hdint : IntegrableOn (dirichletIntegrand r) (Ioi 0) := by
    refine (hintR.sub (integrableOn_constKernel.div_const 2)).congr_fun (fun u _ => ?_)
      measurableSet_Ioi
    simp only [Pi.sub_apply, archimedeanIntegrand_split r hr0 u]; ring
  -- split the Dirichlet form at L
  have hU : dirichletForm r = (∫ u in Ioc 0 L, dirichletIntegrand r u) +
      ∫ u in Ioi L, dirichletIntegrand r u := by
    unfold dirichletForm
    rw [← Ioc_union_Ioi_eq_Ioi hL.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hdint.mono_set Ioc_subset_Ioi_self) (hdint.mono_set (Ioi_subset_Ioi hL.le))
  have htail : ∫ u in Ioi L, dirichletIntegrand r u = ∫ u in Ioi L, kern u := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu : L < u := hu
    have hz : a u = 0 := hsupp u (by rw [abs_of_pos (hL.trans hu)]; exact hu)
    unfold dirichletIntegrand kern
    simp only [hr, hz, zero_div, sub_zero, mul_one]
  -- the gain on (0, L]
  have hrint : IntegrableOn r (Ioc 0 L) := by
    have : Continuous r := hta.1.continuous.div_const _
    exact (this.continuousOn.integrableOn_Icc (a := 0) (b := L)).mono_set Ioc_subset_Icc_self
  have hgain : wL L * (L - (∫ y, f y) ^ 2 / (2 * a 0)) ≤ ∫ u in Ioc 0 L, dirichletIntegrand r u := by
    have hlow : ∫ u in Ioc 0 L, wL L * (1 - r u) ≤ ∫ u in Ioc 0 L, dirichletIntegrand r u := by
      refine setIntegral_mono_on ((integrableOn_const (by simp)).sub hrint |>.const_mul _)
        (hdint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc (fun u hu => ?_)
      have hk := kern_ge_wL hL1.le hu.1 hu.2
      have h1 : 0 ≤ 1 - r u := by linarith [hrle u]
      have : dirichletIntegrand r u = kern u * (1 - r u) := by
        unfold dirichletIntegrand kern; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hk h1
    have hval : ∫ u in Ioc 0 L, wL L * (1 - r u) = wL L * (L - (∫ y, f y) ^ 2 / (2 * a 0)) := by
      have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 L) := integrableOn_const (by simp)
      rw [integral_const_mul, integral_sub (μ := volume.restrict (Ioc 0 L))
        (f := fun _ => (1 : ℝ)) (g := r) hone hrint,
        setIntegral_const, Real.volume_real_Ioc_of_le hL.le, smul_eq_mul, mul_one, sub_zero]
      have : ∫ u in Ioc 0 L, r u = (∫ y, f y) ^ 2 / (2 * a 0) := by
        simp only [hr]
        rw [integral_div, ha_def, integral_Ioc_autocorr hf hc hL.le hsupp]
        ring
      rw [this]
    linarith
  have hfloor : archimedeanTerm a = a 0 * (archimedeanFloor + 2 * dirichletForm r) := by
    rw [harch, hdec]
  rw [hfloor, hU, htail]
  have ha0 := hpos
  have e : a 0 * (2 * (wL L * (L - (∫ y, f y) ^ 2 / (2 * a 0)))) =
      a 0 * (2 * wL L * L) - wL L * (∫ y, f y) ^ 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hgain hpos.le, e]

/-! ## Numerics and the theorem -/

theorem numeric_margin_wide :
    1 / 20 ≤ archimedeanFloor + (3 * Real.log 2 + tailRat) + wL (1 / 8) * (1 / 8)
      + 2 * (1 / 8) - (1 / 8) ^ 3 := by
  have hγ := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 32
  have hseq : Real.eulerMascheroniSeq' 32 = (harmonic 32 : ℝ) - 5 * Real.log 2 := by
    rw [Real.eulerMascheroniSeq', if_neg (by norm_num),
      show ((32 : ℕ) : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hH : (harmonic 32 : ℝ) = (586061125622639 : ℝ) / 144403552893600 := by
    have : harmonic 32 = (586061125622639 : ℚ) / 144403552893600 := by
      simp [harmonic, Finset.sum_range_succ]; norm_num
    rw [this]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  have hlogpi : Real.log Real.pi ≤ 2 * Real.log 2 + (Real.pi / 4 - 1) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < Real.pi / 4)
    rw [Real.log_div hpi0.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow] at h
    push_cast at h
    linarith
  rw [hseq, hH] at hγ
  unfold archimedeanFloor tailRat wL
  norm_num at hγ ⊢
  linarith

/-- **Unconditional Weil positivity on `[-1/16, 1/16]`, quantitative.** -/
theorem weilForm_autocorr_ge_wide {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hsupp : ∀ y : ℝ, (1 / 8 : ℝ) / 2 < |y| → f y = 0) :
    (1 / 20) * ∫ y, f y ^ 2 ≤ weilForm (autocorr f) := by
  have hL : (1 / 8 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [weilForm_rung_zero hsupp hL, ← autocorr_zero_eq]
  have hs := autocorr_hasSupportIn hsupp
  have ha0 := autocorr_zero_nonneg f
  rcases ha0.lt_or_eq with hpos | hzero
  · have harch := archimedeanTerm_autocorr_ge_wide hf hc (by norm_num) (by norm_num) hs hpos
    have hpole := poleTerm_autocorr_ge_sharp hf hc (by norm_num) (by norm_num) hs
    have hvar := sq_integral_le hf (L := 1 / 8) (by norm_num) hsupp
    rw [← autocorr_zero_eq] at hvar
    have htail := two_mul_integral_kern_ge_wide
    have hm := numeric_margin_wide
    have hw : wL (1 / 8) = 15 / 4 := by unfold wL; norm_num
    rw [hw] at harch hm
    set S2 := (∫ y, f y) ^ 2
    set a0 := autocorr f 0
    -- total ≥ a0 (floor + tail + 2 wL L - L³) + S2 (2 - wL), and S2 ≤ L a0
    have hS2 : 0 ≤ S2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left htail hpos.le, mul_le_mul_of_nonneg_left hm hpos.le]
  · have hzero' : ∀ u, autocorr f u = 0 := fun u => by
      have := abs_autocorr_le hf hc u
      rw [← hzero] at this
      exact abs_nonpos_iff.mp this
    have hpz : poleTerm (autocorr f) = 0 := by unfold poleTerm; simp [hzero']
    have haz : archimedeanTerm (autocorr f) = 0 := by
      unfold archimedeanTerm archimedeanIntegrand; simp [hzero']
    rw [hpz, haz, ← hzero]; norm_num

/-- **`ReflectionPositiveOnRung (1/8)`.** -/
theorem reflectionPositiveOnRung_one_div_eight : ReflectionPositiveOnRung (1 / 8) := by
  intro f hf hc hsupp
  have h := weilForm_autocorr_ge_wide hf hc hsupp
  have : 0 ≤ (1 / 20) * ∫ y, f y ^ 2 :=
    mul_nonneg (by norm_num) (integral_nonneg fun y => sq_nonneg _)
  linarith

/-- Every smaller window follows. -/
theorem reflectionPositiveOnRung_of_le_one_div_eight {L : ℝ} (hL : L ≤ 1 / 8) :
    ReflectionPositiveOnRung L := by
  intro f hf hc hsupp
  exact reflectionPositiveOnRung_one_div_eight f hf hc
    (fun y hy => hsupp y (lt_of_le_of_lt (by linarith) hy))

end GppRungZeroWide
