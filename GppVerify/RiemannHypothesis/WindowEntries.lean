import GppVerify.RiemannHypothesis.WindowTail

/-!
# Entries of the window form from moments

For continuous `f, g` on `[-ℓ, ℓ]` with moments `μ_p(f) = ∫ f x^p`, the window form
`B(f, g)` (`GppWindowBilinear.B`) is, up to explicit Taylor tails, a finite expression in the
moments of `f`, `g` and of the minorant `m` (`M_s = ∫_{-T}^{T} m r^s`):

* `abs_lap_sub_moments_le`: `|G_c(f) - Σ_{k<N} c^k/k! μ_k(f)| ≤ (|c|ℓ)^N e^{|c|ℓ} ∫|f|`;
* `norm_hw_sub_moments_le`: `|h_f(r) - Σ_{p<N} (ir)^p/p! μ_p(f)| ≤ (|r|ℓ)^N/N! ∫|f|`;
* `abs_spec_sub_moments_le`:
  `|spec(f, g) - Σ_{p,q<N} ρ(p,q) μ_p(f) μ_q(g) M_{p+q}/(p! q!)| ≤ 2T M (e_f A_g + (A_f + e_f) e_g)`,
  with `ρ(p, q) = Re(i^p conj(i^q))`, `A = ∫|·|`, `e = (Tℓ)^N/N! · A`.

This is how a certificate evaluates the finite block of `B` in rational arithmetic. Unconditional;
no `sorry`, no axioms.
-/

namespace GppWindowEntries

open Complex Set MeasureTheory intervalIntegral Finset GppWindowBilinear GppWindowTail
open scoped ComplexConjugate

variable {ℓ T : ℝ} {m : ℝ → ℝ}

/-- The `p`-th moment `∫_{-ℓ}^{ℓ} f x^p`. -/
noncomputable def mom (ℓ : ℝ) (f : ℝ → ℝ) (p : ℕ) : ℝ := ∫ x in (-ℓ)..ℓ, f x * x ^ p

/-- The degree-`< N` moment polynomial of `h_f`. -/
noncomputable def hwApprox (ℓ : ℝ) (f : ℝ → ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ∑ p ∈ range N, (I * r) ^ p / (p.factorial : ℂ) * (mom ℓ f p : ℂ)

/-- `ρ(p, q) = Re(i^p conj(i^q))`. -/
noncomputable def rho (p q : ℕ) : ℝ := (I ^ p * conj (I ^ q)).re

theorem continuous_hwApprox (f : ℝ → ℝ) (N : ℕ) : Continuous (hwApprox ℓ f N) := by
  unfold hwApprox; fun_prop

theorem norm_hw_sub_moments_le (hℓ : 0 ≤ ℓ) {f : ℝ → ℝ} (hf : Continuous f) (N : ℕ) (r : ℝ) :
    ‖hw ℓ f r - hwApprox ℓ f N r‖ ≤ (|r| * ℓ) ^ N / N.factorial * ∫ x in (-ℓ)..ℓ, |f x| := by
  have h := Complex.norm_integral_mul_exp_I_sub_moments_le (f := fun x => (f x : ℂ)) hℓ
    ((continuous_ofReal.comp hf).intervalIntegrable _ _) N r
  have e1 : ∀ p, ∫ x in (-ℓ)..ℓ, (f x : ℂ) * (x : ℂ) ^ p = (mom ℓ f p : ℂ) := by
    intro p
    unfold mom
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext x; push_cast; rfl
  have e2 : ∫ x in (-ℓ)..ℓ, ‖(f x : ℂ)‖ = ∫ x in (-ℓ)..ℓ, |f x| := by
    congr 1; funext x; rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [e1, e2] at h
  exact h

theorem abs_lap_sub_moments_le (hℓ : 0 ≤ ℓ) {f : ℝ → ℝ} (hf : Continuous f) (N : ℕ) (c : ℝ) :
    |lap ℓ f c - ∑ k ∈ range N, c ^ k / k.factorial * mom ℓ f k| ≤
      (|c| * ℓ) ^ N * Real.exp (|c| * ℓ) * ∫ x in (-ℓ)..ℓ, |f x| := by
  have hle : -ℓ ≤ ℓ := by linarith
  have hsum : ∑ k ∈ range N, c ^ k / k.factorial * mom ℓ f k =
      ∫ x in (-ℓ)..ℓ, f x * ∑ k ∈ range N, (c * x) ^ k / k.factorial := by
    unfold mom
    simp_rw [mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun k _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext x; rw [mul_pow]; ring
    · intro k _
      exact (by fun_prop : Continuous fun x => f x * ((c * x) ^ k / k.factorial)).intervalIntegrable _ _
  unfold lap
  rw [hsum, ← intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun x => f x * Real.exp (c * x)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x =>
      f x * ∑ k ∈ range N, (c * x) ^ k / k.factorial).intervalIntegrable _ _)]
  rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
  refine norm_integral_le_of_norm_le hle (Filter.Eventually.of_forall fun x hx => ?_)
    ((by fun_prop : Continuous fun x =>
      (|c| * ℓ) ^ N * Real.exp (|c| * ℓ) * |f x|).intervalIntegrable _ _)
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  refine (abs_exp_sub_taylor_le (c * x) N).trans ?_
  have hx' : |x| ≤ ℓ := abs_le.mpr ⟨hx.1.le, hx.2⟩
  have hcx : |c * x| ≤ |c| * ℓ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx' (abs_nonneg c)
  gcongr

/-- `Re(hwApprox f · conj hwApprox g)` as a double sum of monomials in `r`. -/
theorem re_hwApprox_mul_conj (f g : ℝ → ℝ) (N : ℕ) (r : ℝ) :
    (hwApprox ℓ f N r * conj (hwApprox ℓ g N r)).re =
      ∑ p ∈ range N, ∑ q ∈ range N,
        rho p q * mom ℓ f p * mom ℓ g q / (p.factorial * q.factorial) * r ^ (p + q) := by
  unfold hwApprox
  rw [map_sum, sum_mul_sum, Complex.re_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [Complex.re_sum]
  refine sum_congr rfl fun q _ => ?_
  have e : (I * (r : ℂ)) ^ p / (p.factorial : ℂ) * (mom ℓ f p : ℂ) *
      conj ((I * (r : ℂ)) ^ q / (q.factorial : ℂ) * (mom ℓ g q : ℂ)) =
      ((mom ℓ f p * mom ℓ g q / (p.factorial * q.factorial) * r ^ (p + q) : ℝ) : ℂ) *
        (I ^ p * conj (I ^ q)) := by
    simp only [map_mul, map_div₀, map_pow, Complex.conj_ofReal, map_natCast]
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul]
  unfold rho
  ring

theorem norm_hwApprox_le (hℓ : 0 ≤ ℓ) {f : ℝ → ℝ} (hf : Continuous f) (N : ℕ) (r : ℝ) :
    ‖hwApprox ℓ f N r‖ ≤ (∫ x in (-ℓ)..ℓ, |f x|) + (|r| * ℓ) ^ N / N.factorial *
      ∫ x in (-ℓ)..ℓ, |f x| := by
  have h1 := norm_hw_sub_moments_le hℓ hf N r
  have h2 := norm_hw_le hℓ f r
  calc ‖hwApprox ℓ f N r‖ = ‖hw ℓ f r - (hw ℓ f r - hwApprox ℓ f N r)‖ := by ring_nf
    _ ≤ ‖hw ℓ f r‖ + ‖hw ℓ f r - hwApprox ℓ f N r‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add h2 h1

/-- **The spectral entry from moments.** -/
theorem abs_spec_sub_moments_le (hℓ : 0 ≤ ℓ) (hT : 0 ≤ T)
    (hm : IntervalIntegrable m volume (-T) T) {Mm : ℝ} (hMm : ∀ r ∈ Icc (-T) T, |m r| ≤ Mm)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (N : ℕ) :
    |spec ℓ T m f g - ∑ p ∈ range N, ∑ q ∈ range N,
        rho p q * mom ℓ f p * mom ℓ g q / (p.factorial * q.factorial) *
          ∫ r in (-T)..T, m r * r ^ (p + q)| ≤
      2 * T * Mm * ((T * ℓ) ^ N / N.factorial * (∫ x in (-ℓ)..ℓ, |f x|) *
          (∫ x in (-ℓ)..ℓ, |g x|) +
        ((∫ x in (-ℓ)..ℓ, |f x|) + (T * ℓ) ^ N / N.factorial * ∫ x in (-ℓ)..ℓ, |f x|) *
          ((T * ℓ) ^ N / N.factorial * ∫ x in (-ℓ)..ℓ, |g x|)) := by
  set Af := ∫ x in (-ℓ)..ℓ, |f x|
  set Ag := ∫ x in (-ℓ)..ℓ, |g x|
  set S := (T * ℓ) ^ N / N.factorial
  have hle : -T ≤ T := by linarith
  have hAf : 0 ≤ Af := integral_nonneg (by linarith) fun x _ => abs_nonneg _
  have hAg : 0 ≤ Ag := integral_nonneg (by linarith) fun x _ => abs_nonneg _
  have hS : 0 ≤ S := by positivity
  -- the main part integrates term by term
  have hmain : ∫ r in (-T)..T, m r * (hwApprox ℓ f N r * conj (hwApprox ℓ g N r)).re =
      ∑ p ∈ range N, ∑ q ∈ range N,
        rho p q * mom ℓ f p * mom ℓ g q / (p.factorial * q.factorial) *
          ∫ r in (-T)..T, m r * r ^ (p + q) := by
    simp_rw [re_hwApprox_mul_conj, mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun p _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine sum_congr rfl fun q _ => ?_
        rw [← intervalIntegral.integral_const_mul]
        congr 1; funext r; ring
      · intro q _
        exact hm.mul_continuousOn (by fun_prop)
    · intro p _
      simp_rw [← mul_sum]
      exact hm.mul_continuousOn (by fun_prop)
  have hcont : ∀ u v : ℝ → ℂ, Continuous u → Continuous v →
      IntervalIntegrable (fun r => m r * (u r * conj (v r)).re) volume (-T) T :=
    fun u v hu hv => hm.mul_continuousOn
      (Complex.continuous_re.comp (hu.mul (Complex.continuous_conj.comp hv))).continuousOn
  have hHf := continuous_hw (ℓ := ℓ) hf
  have hHg := continuous_hw (ℓ := ℓ) hg
  have hSf := continuous_hwApprox (ℓ := ℓ) f N
  have hSg := continuous_hwApprox (ℓ := ℓ) g N
  -- the error integrand
  set E : ℝ → ℝ := fun r => m r * (hw ℓ f r * conj (hw ℓ g r)).re -
    m r * (hwApprox ℓ f N r * conj (hwApprox ℓ g N r)).re with hE
  have hdiff : spec ℓ T m f g - ∑ p ∈ range N, ∑ q ∈ range N,
      rho p q * mom ℓ f p * mom ℓ g q / (p.factorial * q.factorial) *
        ∫ r in (-T)..T, m r * r ^ (p + q) = ∫ r in (-T)..T, E r := by
    rw [← hmain]
    unfold spec
    rw [← intervalIntegral.integral_sub (hcont _ _ hHf hHg) (hcont _ _ hSf hSg)]
  rw [hdiff, ← Real.norm_eq_abs]
  have hb : ∀ r ∈ Set.uIoc (-T) T, ‖E r‖ ≤ Mm * (S * Af * Ag + (Af + S * Af) * (S * Ag)) := by
    intro r hr
    rw [Set.uIoc_of_le hle] at hr
    have hr' : r ∈ Icc (-T) T := ⟨hr.1.le, hr.2⟩
    have hrT : |r| ≤ T := abs_le.mpr hr'
    have hpow : (|r| * ℓ) ^ N / N.factorial ≤ S := by
      unfold S; gcongr
    have eF : ‖hw ℓ f r - hwApprox ℓ f N r‖ ≤ S * Af :=
      (norm_hw_sub_moments_le hℓ hf N r).trans (mul_le_mul_of_nonneg_right hpow hAf)
    have eG : ‖hw ℓ g r - hwApprox ℓ g N r‖ ≤ S * Ag :=
      (norm_hw_sub_moments_le hℓ hg N r).trans (mul_le_mul_of_nonneg_right hpow hAg)
    have hG : ‖hw ℓ g r‖ ≤ Ag := norm_hw_le hℓ g r
    have hSF : ‖hwApprox ℓ f N r‖ ≤ Af + S * Af := by
      have := norm_hwApprox_le hℓ hf N r
      have h2 : (|r| * ℓ) ^ N / N.factorial * Af ≤ S * Af := mul_le_mul_of_nonneg_right hpow hAf
      linarith
    -- the complex identity behind the error
    have hid : hw ℓ f r * conj (hw ℓ g r) - hwApprox ℓ f N r * conj (hwApprox ℓ g N r) =
        (hw ℓ f r - hwApprox ℓ f N r) * conj (hw ℓ g r) +
          hwApprox ℓ f N r * conj (hw ℓ g r - hwApprox ℓ g N r) := by
      rw [map_sub]; ring
    have hEr : E r = m r * (hw ℓ f r * conj (hw ℓ g r) -
        hwApprox ℓ f N r * conj (hwApprox ℓ g N r)).re := by
      simp only [hE, Complex.sub_re]; ring
    rw [hEr, hid, Real.norm_eq_abs, abs_mul]
    have hre : |((hw ℓ f r - hwApprox ℓ f N r) * conj (hw ℓ g r) +
        hwApprox ℓ f N r * conj (hw ℓ g r - hwApprox ℓ g N r)).re| ≤
        S * Af * Ag + (Af + S * Af) * (S * Ag) := by
      refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      · rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul eF hG (norm_nonneg _) (by positivity)
      · rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul hSF eG (norm_nonneg _) (by positivity)
    exact mul_le_mul (hMm r hr') hre (abs_nonneg _) ((abs_nonneg _).trans (hMm r hr'))
  refine (norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)]]
  ring

end GppWindowEntries

#print axioms GppWindowEntries.abs_lap_sub_moments_le
#print axioms GppWindowEntries.abs_spec_sub_moments_le
