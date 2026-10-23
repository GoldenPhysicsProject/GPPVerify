import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The sine-squared packet: its Laplace transform has no zeros off the imaginary axis

Sources: Codex, `work/codex/2026-10-22_single_packet_detecting_train_stationary_sewing_frontier.md`
§2, and Astra, `work/2026-10-22_astra_detector_kms_sewing_audit.md` §1 (GPP-bridge), about the
fixed window `g(x) = sin²(πx)` on `[0, 1]` that Turbo's S1 sectors use (Wave 234). Daniel Toupin /
Golden Physics Project, with AI assistance from Codex and Astra (statements) and Claude Code
(formalization).

With `S(z) = ∫₀¹ e^{zx} sin²(πx) dx`:

* `S_eq`: `S(z) = 2π²(e^z − 1)/(z(z² + 4π²))` whenever `z ≠ 0` and `z² + 4π² ≠ 0`.
* `S_eq_exp_mul_S_neg`: the reflection `S(z) = e^z S(−z)` for every `z`, because `g` is symmetric
  about `1/2`. This is the identity that turns the cross shift into `a_i + a_j + 1`.
* `S_mul_S_neg`: `S(z) S(−z) = 8π⁴(cosh z − 1)/(z²(z² + 4π²)²)`.
* `S_ne_zero` and `S_mul_S_neg_ne_zero`: if `Re z ≠ 0` then `S(z) ≠ 0` and `S(z) S(−z) ≠ 0`.
* `autocorr_eq` (Astra): the autocorrelation `G(r) = ∫₀^{1−r} sin²(πx) sin²(π(x+r)) dx` equals
  `(1 − r)/4 + (1 − r) cos(2πr)/8 + 3 sin(2πr)/(16π)`, and `autocorr_zero`: `G(0) = 3/8`.

The last item is the exact content of Codex's "no off-critical blind spot" claim. A zero
`ρ = 1/2 + λ` of ζ with `Re λ > 0` would give the filtered signal a pole whose residue is
`−m_ρ e^λ S(λ) S(−λ)`, and that factor never vanishes.

**Scope.** Not formalized here:
* the autocorrelation multiplier `H(z) = z(z + ½) S(z) S(−z)`;
* the filtered Laplace identity for `K_g`;
* the criterion `RH ⇔ K_g bounded`. Its forward direction needs the explicit formula, which is not
  in Mathlib.

These are statements about one test function. They prove nothing about the zeros of ζ.
-/

open Complex Real intervalIntegral

namespace GppSineSquarePacket

/-- The Laplace transform of the window, `S(z) = ∫₀¹ e^{zx} sin²(πx) dx`. -/
noncomputable def S (z : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, Complex.exp (z * x) * Complex.sin (π * x) ^ 2

private lemma sin_sq_eq (w : ℂ) : Complex.sin (π * w) ^ 2 = (1 - Complex.cos (2 * π * w)) / 2 := by
  rw [Complex.sin_sq, Complex.cos_sq, show 2 * (π : ℂ) * w = 2 * (π * w) by ring]
  ring

/-- An antiderivative of `e^{zw} sin²(πw)`. -/
private noncomputable def F (z w : ℂ) : ℂ :=
  Complex.exp (z * w) / (2 * z) -
    Complex.exp (z * w) * (z * Complex.cos (2 * π * w) + 2 * π * Complex.sin (2 * π * w)) /
      (2 * (z ^ 2 + 4 * π ^ 2))

private lemma hasDerivAt_F {z : ℂ} (hz : z ≠ 0) (hz' : z ^ 2 + 4 * (π : ℂ) ^ 2 ≠ 0) (w : ℂ) :
    HasDerivAt (F z) (Complex.exp (z * w) * Complex.sin (π * w) ^ 2) w := by
  have he : HasDerivAt (fun w => Complex.exp (z * w)) (Complex.exp (z * w) * z) w := by
    simpa using ((hasDerivAt_id w).const_mul z).cexp
  have hc : HasDerivAt (fun w => Complex.cos (2 * π * w))
      (-Complex.sin (2 * π * w) * (2 * π)) w := by
    simpa using ((hasDerivAt_id w).const_mul (2 * (π : ℂ))).ccos
  have hs : HasDerivAt (fun w => Complex.sin (2 * π * w))
      (Complex.cos (2 * π * w) * (2 * π)) w := by
    simpa using ((hasDerivAt_id w).const_mul (2 * (π : ℂ))).csin
  have h := (he.div_const (2 * z)).sub
    ((he.mul ((hc.const_mul z).add (hs.const_mul (2 * (π : ℂ))))).div_const
      (2 * (z ^ 2 + 4 * π ^ 2)))
  refine h.congr_deriv ?_
  simp only [Pi.add_apply]
  rw [sin_sq_eq]
  have h4 : z ^ 2 + (π : ℂ) ^ 2 * 4 ≠ 0 := by rwa [mul_comm] at hz'
  field_simp
  ring

/-- **Closed form.** `S(z) = 2π²(e^z − 1)/(z(z² + 4π²))` for `z ≠ 0`, `z² + 4π² ≠ 0`. -/
theorem S_eq {z : ℂ} (hz : z ≠ 0) (hz' : z ^ 2 + 4 * (π : ℂ) ^ 2 ≠ 0) :
    S z = 2 * π ^ 2 * (Complex.exp z - 1) / (z * (z ^ 2 + 4 * π ^ 2)) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => F z x)
      (Complex.exp (z * x) * Complex.sin (π * x) ^ 2) x :=
    fun x _ => (hasDerivAt_F hz hz' x).comp_ofReal
  have hint : IntervalIntegrable
      (fun x : ℝ => Complex.exp (z * x) * Complex.sin (π * x) ^ 2) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (z * x) * Complex.sin (π * x) ^ 2).intervalIntegrable 0 1
  rw [S, integral_eq_sub_of_hasDerivAt hderiv hint]
  have h2 : Complex.cos (2 * π) = 1 := by
    rw [show (2 : ℂ) * π = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Real.cos_two_pi]; simp
  have h3 : Complex.sin (2 * π) = 0 := by
    rw [show (2 : ℂ) * π = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin,
      Real.sin_two_pi]; simp
  simp only [F, Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero,
    Complex.cos_zero, Complex.sin_zero, h2, h3]
  field_simp
  ring

/-- **Reflection.** `S(z) = e^z S(−z)` for every `z`: the window is symmetric about `1/2`. -/
theorem S_eq_exp_mul_S_neg (z : ℂ) : S z = Complex.exp z * S (-z) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => Complex.exp (z * x) * Complex.sin (π * x) ^ 2) (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_zero, sub_self] at h
  rw [S, S, ← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hs : Complex.sin (π * ((1 - x : ℝ) : ℂ)) = Complex.sin (π * x) := by
    rw [show (π : ℂ) * ((1 - x : ℝ) : ℂ) = π - π * x by push_cast; ring, Complex.sin_pi_sub]
  simp only [hs]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **The autocorrelation multiplier in closed form.**
`S(z) S(−z) = 8π⁴(cosh z − 1)/(z²(z² + 4π²)²)` for `z ≠ 0`, `z² + 4π² ≠ 0`. -/
theorem S_mul_S_neg {z : ℂ} (hz : z ≠ 0) (hz' : z ^ 2 + 4 * (π : ℂ) ^ 2 ≠ 0) :
    S z * S (-z) = 8 * π ^ 4 * (Complex.cosh z - 1) / (z ^ 2 * (z ^ 2 + 4 * π ^ 2) ^ 2) := by
  have hz'' : (-z) ^ 2 + 4 * (π : ℂ) ^ 2 ≠ 0 := by rwa [neg_sq]
  rw [S_eq hz hz', S_eq (neg_ne_zero.mpr hz) hz'', Complex.cosh, Complex.exp_neg, neg_sq]
  have he : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  field_simp
  ring

private lemma ne_zero_of_re_ne_zero {z : ℂ} (h : z.re ≠ 0) :
    z ≠ 0 ∧ z ^ 2 + 4 * (π : ℂ) ^ 2 ≠ 0 ∧ Complex.exp z ≠ 1 := by
  refine ⟨fun h0 => h (by simp [h0]), fun h0 => ?_, fun h0 => ?_⟩
  · have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp only [sq, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat] at hre him
    have hzi : z.im = 0 := (mul_eq_zero.mp (show z.re * z.im = 0 by linarith)).resolve_left h
    rw [hzi] at hre
    nlinarith [sq_nonneg z.re, Real.pi_pos]
  · have := congrArg norm h0
    rw [Complex.norm_exp, norm_one, Real.exp_eq_one_iff] at this
    exact h this

/-- **No zeros off the imaginary axis.** If `Re z ≠ 0` then `S(z) ≠ 0`. -/
theorem S_ne_zero {z : ℂ} (h : z.re ≠ 0) : S z ≠ 0 := by
  obtain ⟨hz, hz', he⟩ := ne_zero_of_re_ne_zero h
  rw [S_eq hz hz']
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hpi))
    (sub_ne_zero.mpr he)) (mul_ne_zero hz hz')

/-- **The detector multiplier never vanishes off the imaginary axis.** If `Re z ≠ 0` then
`S(z) S(−z) ≠ 0`; in particular `e^λ S(λ) S(−λ) ≠ 0` for `Re λ > 0`. -/
theorem S_mul_S_neg_ne_zero {z : ℂ} (h : z.re ≠ 0) : S z * S (-z) ≠ 0 :=
  mul_ne_zero (S_ne_zero h) (S_ne_zero (by simpa using h))

/-! ### The autocorrelation of the window -/

private lemma sin_sq_mul_sin_sq (x r : ℝ) :
    Real.sin (π * x) ^ 2 * Real.sin (π * (x + r)) ^ 2 =
      (1 - Real.cos (2 * π * x) - Real.cos (2 * π * (x + r)) + Real.cos (2 * π * r) / 2 +
        Real.cos (2 * π * (2 * x + r)) / 2) / 4 := by
  have h1 := Real.sin_sq_add_cos_sq (π * x)
  have h2 := Real.sin_sq_add_cos_sq (π * r)
  rw [show π * (x + r) = π * x + π * r by ring, show 2 * π * x = 2 * (π * x) by ring,
    show 2 * π * (x + r) = 2 * (π * x) + 2 * (π * r) by ring,
    show 2 * π * r = 2 * (π * r) by ring,
    show 2 * π * (2 * x + r) = 2 * (π * x) + (2 * (π * x) + 2 * (π * r)) by ring]
  simp only [Real.sin_add, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
  set su := Real.sin (π * x)
  set cu := Real.cos (π * x)
  set sv := Real.sin (π * r)
  set cv := Real.cos (π * r)
  linear_combination (cu ^ 2 * sv ^ 2 - cu ^ 2 / 2 + 2 * cu * cv * su * sv + cv ^ 2 * su ^ 2 +
    cv ^ 2) * h1 + (-cu ^ 4 + cu ^ 2) * h2

/-- **Autocorrelation in closed form** (Astra). For every real `r`,
`∫₀^{1−r} sin²(πx) sin²(π(x + r)) dx = (1 − r)/4 + (1 − r) cos(2πr)/8 + 3 sin(2πr)/(16π)`.
For `0 ≤ r ≤ 1` the left side is the autocorrelation `G(r) = ∫ g(x) g(x + r) dx` of the window,
and `G` is even. -/
theorem autocorr_eq (r : ℝ) :
    ∫ x in (0 : ℝ)..(1 - r), Real.sin (π * x) ^ 2 * Real.sin (π * (x + r)) ^ 2 =
      (1 - r) / 4 + (1 - r) * Real.cos (2 * π * r) / 8 + 3 * Real.sin (2 * π * r) / (16 * π) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  let A : ℝ → ℝ := fun x => (x - Real.sin (2 * π * x) / (2 * π) -
    Real.sin (2 * π * (x + r)) / (2 * π) + x * Real.cos (2 * π * r) / 2 +
    Real.sin (2 * π * (2 * x + r)) / (8 * π)) / 4
  have hA : ∀ x ∈ Set.uIcc (0 : ℝ) (1 - r),
      HasDerivAt A (Real.sin (π * x) ^ 2 * Real.sin (π * (x + r)) ^ 2) x := by
    intro x _
    have d1 := ((hasDerivAt_id x).const_mul (2 * π)).sin
    have d2 := (((hasDerivAt_id x).add_const r).const_mul (2 * π)).sin
    have d3 := ((((hasDerivAt_id x).const_mul 2).add_const r).const_mul (2 * π)).sin
    have h := (((((hasDerivAt_id x).sub (d1.div_const (2 * π))).sub (d2.div_const (2 * π))).add
      ((hasDerivAt_id x).mul_const (Real.cos (2 * π * r)) |>.div_const 2)).add
      (d3.div_const (8 * π))).div_const 4
    refine h.congr_deriv ?_
    rw [sin_sq_mul_sin_sq]
    simp only [id]
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => Real.sin (π * x) ^ 2 * Real.sin (π * (x + r)) ^ 2)
      MeasureTheory.volume 0 (1 - r) := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt hA hint]
  have e1 : Real.sin (2 * π * (1 - r)) = -Real.sin (2 * π * r) := by
    rw [show 2 * π * (1 - r) = 2 * π - 2 * π * r by ring, Real.sin_two_pi_sub]
  have e2 : Real.sin (2 * π * (1 - r + r)) = 0 := by
    rw [show 2 * π * (1 - r + r) = 2 * π by ring, Real.sin_two_pi]
  have e3 : Real.sin (2 * π * (2 * (1 - r) + r)) = -Real.sin (2 * π * r) := by
    rw [show 2 * π * (2 * (1 - r) + r) = 2 * π - 2 * π * r + 2 * π by ring,
      Real.sin_add_two_pi, Real.sin_two_pi_sub]
  simp only [A, e1, e2, e3, mul_zero, zero_add, Real.sin_zero]
  field_simp
  ring

/-- **The window's energy.** `G(0) = ∫₀¹ sin⁴(πx) dx = 3/8`. -/
theorem autocorr_zero : ∫ x in (0 : ℝ)..1, Real.sin (π * x) ^ 4 = 3 / 8 := by
  have h := autocorr_eq 0
  simp only [sub_zero, mul_zero, Real.cos_zero, Real.sin_zero, zero_div, add_zero] at h
  simp_rw [show ∀ x : ℝ, Real.sin (π * x) ^ 4 = Real.sin (π * x) ^ 2 * Real.sin (π * x) ^ 2
    from fun x => by ring]
  rw [h]; norm_num

end GppSineSquarePacket
