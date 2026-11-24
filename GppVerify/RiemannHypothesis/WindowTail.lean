import GppVerify.RiemannHypothesis.WindowBilinear

/-!
# Tail control for the window form, and the finite-section theorem

Let `φ_0, …, φ_{n-1}` be continuous, pairwise orthogonal on `[-ℓ, ℓ]` (`d_k = ⟨φ_k, φ_k⟩ > 0`),
spanning the monomials `x^k`, `k < D`. Write `g = Σ c_k φ_k + t` with `t ⊥ φ_k`, so `t` has vanishing
moments of order `< D`. Then, with `A = ∫|t| ≤ √(2ℓ) ‖t‖`:

* `|G_±(t)| ≤ (ℓ/2)^D e^{ℓ/2} A` (real exponential Taylor remainder),
* `|h_t(r)| ≤ (|r|ℓ)^D / D! · A` (`Complex.norm_integral_mul_exp_I_le_of_moments`),

and so `B(t, t) ≥ μ ‖t‖²`, `|B(φ_k, t)| ≤ 2ℓ κ √d_k ‖t‖`, with `μ` and `κ` explicit in
`ℓ, T, D, sup |m|`. `window_form_nonneg` combines these with `GramTail.nonneg_of_block_tail`:

  if `λ Σ d_k c_k² ≤ Σ c_j c_k B(φ_j, φ_k)` for all `c` (the matrix certificate) and
  `n (2ℓκ)² ≤ λ μ`, then `B(g, g) ≥ 0` for every continuous `g`.

Unconditional. No `sorry`, no axioms.
-/

namespace GppWindowTail

open Complex Set MeasureTheory intervalIntegral Finset GppWindowBilinear
open scoped ComplexConjugate

variable {ℓ : ℝ}

/-! ### Elementary bounds on `[-ℓ, ℓ]` -/

/-- **Cauchy–Schwarz on the window:** `(∫|t|)² ≤ 2ℓ ∫ t²`. -/
theorem sq_integral_abs_le (hℓ : 0 ≤ ℓ) {t : ℝ → ℝ} (ht : Continuous t) :
    (∫ x in (-ℓ)..ℓ, |t x|) ^ 2 ≤ 2 * ℓ * ∫ x in (-ℓ)..ℓ, t x ^ 2 := by
  set A := ∫ x in (-ℓ)..ℓ, |t x|
  set Q := ∫ x in (-ℓ)..ℓ, t x ^ 2
  have hle : -ℓ ≤ ℓ := by linarith
  have h0 : 0 ≤ ∫ x in (-ℓ)..ℓ, (2 * ℓ * |t x| - A) ^ 2 :=
    integral_nonneg hle fun x _ => sq_nonneg _
  have hexp : ∫ x in (-ℓ)..ℓ, (2 * ℓ * |t x| - A) ^ 2 =
      (2 * ℓ) ^ 2 * Q - 2 * (2 * ℓ) * A * A + A ^ 2 * (2 * ℓ) := by
    have e : (fun x => (2 * ℓ * |t x| - A) ^ 2) =
        fun x => ((2 * ℓ) ^ 2 * t x ^ 2 - (2 * (2 * ℓ) * A) * |t x|) + A ^ 2 := by
      funext x; rw [show t x ^ 2 = |t x| ^ 2 from (sq_abs _).symm]; ring
    have i1 : IntervalIntegrable (fun x => (2 * ℓ) ^ 2 * t x ^ 2) volume (-ℓ) ℓ :=
      (by fun_prop : Continuous fun x => (2 * ℓ) ^ 2 * t x ^ 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x => (2 * (2 * ℓ) * A) * |t x|) volume (-ℓ) ℓ :=
      (by fun_prop : Continuous fun x => (2 * (2 * ℓ) * A) * |t x|).intervalIntegrable _ _
    rw [e, integral_add (i1.sub i2) intervalIntegrable_const, integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_neg_eq_add]
    ring
  rw [hexp] at h0
  rcases hℓ.lt_or_eq with hpos | hzero
  · nlinarith
  · subst hzero
    have : A = 0 := by simp [A]
    rw [this]; simp

/-- **Moments kill polynomials.** If `t` has vanishing moments of order `< D` and `K` is within `E`
of a polynomial of degree `< D` on `[-ℓ, ℓ]`, then `|∫ t K| ≤ E ∫ |t|`. -/
theorem abs_integral_mul_le_of_moments (hℓ : 0 ≤ ℓ) {t K : ℝ → ℝ} (ht : Continuous t)
    (hK : Continuous K) {D : ℕ} (hmom : ∀ k < D, ∫ x in (-ℓ)..ℓ, t x * x ^ k = 0) (a : ℕ → ℝ)
    {E : ℝ} (hE : ∀ x ∈ Icc (-ℓ) ℓ, |K x - ∑ k ∈ range D, a k * x ^ k| ≤ E) :
    |∫ x in (-ℓ)..ℓ, t x * K x| ≤ E * ∫ x in (-ℓ)..ℓ, |t x| := by
  have hle : -ℓ ≤ ℓ := by linarith
  have hP : ∫ x in (-ℓ)..ℓ, t x * ∑ k ∈ range D, a k * x ^ k = 0 := by
    simp_rw [mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_eq_zero fun k hk => ?_
      have : (fun x => t x * (a k * x ^ k)) = fun x => a k * (t x * x ^ k) := by
        funext x; ring
      rw [this, intervalIntegral.integral_const_mul, hmom k (mem_range.mp hk), mul_zero]
    · intro k _
      exact (by fun_prop : Continuous fun x => t x * (a k * x ^ k)).intervalIntegrable _ _
  have hsplit : ∫ x in (-ℓ)..ℓ, t x * K x =
      ∫ x in (-ℓ)..ℓ, t x * (K x - ∑ k ∈ range D, a k * x ^ k) := by
    have i1 : IntervalIntegrable (fun x => t x * (K x - ∑ k ∈ range D, a k * x ^ k)) volume
        (-ℓ) ℓ := (by fun_prop : Continuous fun x =>
          t x * (K x - ∑ k ∈ range D, a k * x ^ k)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x => t x * ∑ k ∈ range D, a k * x ^ k) volume (-ℓ) ℓ :=
      (by fun_prop : Continuous fun x => t x * ∑ k ∈ range D, a k * x ^ k).intervalIntegrable _ _
    have := integral_add i1 i2
    rw [hP, add_zero] at this
    rw [← this]; congr 1; funext x; ring
  rw [hsplit, ← intervalIntegral.integral_const_mul]
  have hg : IntervalIntegrable (fun x => E * |t x|) volume (-ℓ) ℓ :=
    (by fun_prop : Continuous fun x => E * |t x|).intervalIntegrable _ _
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hle (Filter.Eventually.of_forall fun x hx => ?_) hg)
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hE x ⟨hx.1.le, hx.2⟩) (abs_nonneg _)

/-- The real exponential Taylor remainder: `|e^y - Σ_{m<D} y^m/m!| ≤ |y|^D e^{|y|}`. -/
theorem abs_exp_sub_taylor_le (y : ℝ) (D : ℕ) :
    |Real.exp y - ∑ m ∈ range D, y ^ m / m.factorial| ≤ |y| ^ D * Real.exp |y| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (y : ℂ) D
  have e : Complex.exp (y : ℂ) - ∑ m ∈ range D, (y : ℂ) ^ m / m.factorial =
      ((Real.exp y - ∑ m ∈ range D, y ^ m / m.factorial : ℝ) : ℂ) := by push_cast; rfl
  rw [e, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- **The Laplace transform of a function with vanishing moments.** -/
theorem abs_lap_le_of_moments (hℓ : 0 ≤ ℓ) {t : ℝ → ℝ} (ht : Continuous t) {D : ℕ}
    (hmom : ∀ k < D, ∫ x in (-ℓ)..ℓ, t x * x ^ k = 0) (c : ℝ) :
    |lap ℓ t c| ≤ (|c| * ℓ) ^ D * Real.exp (|c| * ℓ) * ∫ x in (-ℓ)..ℓ, |t x| := by
  unfold lap
  refine abs_integral_mul_le_of_moments hℓ ht (by fun_prop) hmom
    (fun k => c ^ k / k.factorial) fun x hx => ?_
  have hx' : |x| ≤ ℓ := abs_le.mpr hx
  have e : ∑ k ∈ range D, c ^ k / k.factorial * x ^ k =
      ∑ m ∈ range D, (c * x) ^ m / m.factorial := by
    refine sum_congr rfl fun k _ => by rw [mul_pow]; ring
  rw [e]
  refine (abs_exp_sub_taylor_le (c * x) D).trans ?_
  have hcx : |c * x| ≤ |c| * ℓ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx' (abs_nonneg c)
  gcongr

/-- **The Fourier transform of a function with vanishing moments.** -/
theorem norm_hw_le_of_moments (hℓ : 0 ≤ ℓ) {t : ℝ → ℝ} (ht : Continuous t) {D : ℕ}
    (hmom : ∀ k < D, ∫ x in (-ℓ)..ℓ, t x * x ^ k = 0) (r : ℝ) :
    ‖hw ℓ t r‖ ≤ (|r| * ℓ) ^ D / D.factorial * ∫ x in (-ℓ)..ℓ, |t x| := by
  have hcm : ∀ k < D, ∫ x in (-ℓ)..ℓ, (t x : ℂ) * (x : ℂ) ^ k = 0 := by
    intro k hk
    have : (fun x : ℝ => (t x : ℂ) * (x : ℂ) ^ k) = fun x => ((t x * x ^ k : ℝ) : ℂ) := by
      funext x; push_cast; rfl
    rw [this, intervalIntegral.integral_ofReal, hmom k hk, Complex.ofReal_zero]
  have h := Complex.norm_integral_mul_exp_I_le_of_moments (f := fun x => (t x : ℂ)) hℓ
    ((continuous_ofReal.comp ht).intervalIntegrable _ _) hcm r
  have e : ∫ x in (-ℓ)..ℓ, ‖(t x : ℂ)‖ = ∫ x in (-ℓ)..ℓ, |t x| := by
    congr 1; funext x; rw [Complex.norm_real, Real.norm_eq_abs]
  rw [e] at h
  exact h

/-- `|h_f(r)| ≤ ∫ |f|`. -/
theorem norm_hw_le (hℓ : 0 ≤ ℓ) (f : ℝ → ℝ) (r : ℝ) :
    ‖hw ℓ f r‖ ≤ ∫ x in (-ℓ)..ℓ, |f x| := by
  unfold hw
  refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
  congr 1; funext x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm (I : ℂ),
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `|G_c(f)| ≤ e^{|c|ℓ} ∫ |f|`. -/
theorem abs_lap_le (hℓ : 0 ≤ ℓ) {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    |lap ℓ f c| ≤ Real.exp (|c| * ℓ) * ∫ x in (-ℓ)..ℓ, |f x| := by
  have := abs_lap_le_of_moments (D := 0) hℓ hf (fun k hk => absurd hk (Nat.not_lt_zero k)) c
  simpa using this

/-! ### The form on the tail and the coupling -/

variable {T β : ℝ} {m : ℝ → ℝ}

theorem re_mul_conj_self (z : ℂ) : (z * conj z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

/-- On `[-T, T]`, a function with vanishing moments has `|h_t(r)| ≤ S A`, `S = (Tℓ)^D/D!`. -/
theorem norm_hw_le_tail (hℓ : 0 ≤ ℓ) {t : ℝ → ℝ} (ht : Continuous t) {D : ℕ}
    (hmom : ∀ k < D, ∫ x in (-ℓ)..ℓ, t x * x ^ k = 0) {r : ℝ} (hr : |r| ≤ T) :
    ‖hw ℓ t r‖ ≤ (T * ℓ) ^ D / D.factorial * ∫ x in (-ℓ)..ℓ, |t x| := by
  refine (norm_hw_le_of_moments hℓ ht hmom r).trans ?_
  have hA : 0 ≤ ∫ x in (-ℓ)..ℓ, |t x| := integral_nonneg (by linarith) fun x _ => abs_nonneg _
  gcongr

/-- **The spectral part on the tail:** `spec(t, t) ≥ -(2T M S²) A²`. -/
theorem spec_tail_ge (hℓ : 0 ≤ ℓ) (hT : 0 ≤ T) (hm : IntervalIntegrable m volume (-T) T)
    {Mm : ℝ} (hMm : ∀ r ∈ Icc (-T) T, |m r| ≤ Mm) {t : ℝ → ℝ} (ht : Continuous t) {D : ℕ}
    (hmom : ∀ k < D, ∫ x in (-ℓ)..ℓ, t x * x ^ k = 0) :
    -(2 * T * Mm * ((T * ℓ) ^ D / D.factorial) ^ 2) * (∫ x in (-ℓ)..ℓ, |t x|) ^ 2 ≤
      spec ℓ T m t t := by
  set A := ∫ x in (-ℓ)..ℓ, |t x|
  set S := (T * ℓ) ^ D / D.factorial
  have hle : -T ≤ T := by linarith
  have hconst : ∫ _ in (-T)..T, -(Mm * (S * A) ^ 2) = -(2 * T * Mm * S ^ 2) * A ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [← hconst]
  unfold spec
  refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
    (intervalIntegrable_spec_integrand hm ht ht) fun r hr => ?_
  rw [re_mul_conj_self]
  have hr' : |r| ≤ T := abs_le.mpr hr
  have h1 := norm_hw_le_tail hℓ ht hmom hr'
  have hSA : 0 ≤ S * A := mul_nonneg (by positivity)
    (integral_nonneg (by linarith) fun x _ => abs_nonneg _)
  have h2 : ‖hw ℓ t r‖ ^ 2 ≤ (S * A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 := abs_le.mp (hMm r hr)
  nlinarith [sq_nonneg ‖hw ℓ t r‖, abs_nonneg (m r)]

/-- **The spectral coupling:** `|spec(f, t)| ≤ 2T M (∫|f|) S A`. -/
theorem abs_spec_coupling_le (hℓ : 0 ≤ ℓ) (hT : 0 ≤ T)
    {Mm : ℝ} (hMm : ∀ r ∈ Icc (-T) T, |m r| ≤ Mm) (f : ℝ → ℝ) {t : ℝ → ℝ}
    (ht : Continuous t) {D : ℕ} (hmom : ∀ k < D, ∫ x in (-ℓ)..ℓ, t x * x ^ k = 0) :
    |spec ℓ T m f t| ≤
      2 * T * Mm * (∫ x in (-ℓ)..ℓ, |f x|) * ((T * ℓ) ^ D / D.factorial) *
        ∫ x in (-ℓ)..ℓ, |t x| := by
  set A := ∫ x in (-ℓ)..ℓ, |t x|
  set Af := ∫ x in (-ℓ)..ℓ, |f x|
  set S := (T * ℓ) ^ D / D.factorial
  unfold spec
  rw [← Real.norm_eq_abs]
  have hb : ∀ r ∈ Set.uIoc (-T) T, ‖m r * (hw ℓ f r * conj (hw ℓ t r)).re‖ ≤ Mm * (Af * (S * A)) := by
    intro r hr
    have hle : -T ≤ T := by linarith
    rw [Set.uIoc_of_le hle] at hr
    have hr' : r ∈ Icc (-T) T := ⟨hr.1.le, hr.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |(hw ℓ f r * conj (hw ℓ t r)).re| ≤ Af * (S * A) := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (norm_hw_le hℓ f r) (norm_hw_le_tail hℓ ht hmom (abs_le.mpr hr'))
        (norm_nonneg _) (integral_nonneg (by linarith) fun x _ => abs_nonneg _)
    exact mul_le_mul (hMm r hr') h1 (abs_nonneg _) ((abs_nonneg _).trans (hMm r hr'))
  refine (norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)]]
  ring

/-- `|G_{±1/2}(t)| ≤ P A` with `P = (ℓ/2)^D e^{ℓ/2}`. -/
theorem abs_lap_half_le (hℓ : 0 ≤ ℓ) {t : ℝ → ℝ} (ht : Continuous t) {D : ℕ}
    (hmom : ∀ k < D, ∫ x in (-ℓ)..ℓ, t x * x ^ k = 0) {c : ℝ} (hc : |c| = 1 / 2) :
    |lap ℓ t c| ≤ (ℓ / 2) ^ D * Real.exp (ℓ / 2) * ∫ x in (-ℓ)..ℓ, |t x| := by
  have := abs_lap_le_of_moments hℓ ht hmom c
  rwa [hc, show 1 / 2 * ℓ = ℓ / 2 by ring] at this

/-! ### The finite-section theorem -/

/-- **Finite section plus tail for the window form.** Let `φ_0, …, φ_{n-1}` be continuous, pairwise
orthogonal on `[-ℓ, ℓ]` with `d_k = ⟨φ_k, φ_k⟩ > 0`, spanning `x^k` for `k < D`. Let `|m| ≤ M` on
`[-T, T]`. Put `P = (ℓ/2)^D e^{ℓ/2}`, `S = (Tℓ)^D/D!`,

  `μ = β - 2ℓ (2P² + M T S²/π)`,   `κ = 2 e^{ℓ/2} P + M T S/π`.

If the finite block satisfies `λ Σ d_k c_k² ≤ Σ c_j c_k B(φ_j, φ_k)` for every `c`, and
`n (2ℓκ)² ≤ λ μ` with `λ, μ ≥ 0`, then `B(g, g) ≥ 0` for every continuous `g`. -/
theorem window_form_nonneg (hℓ : 0 ≤ ℓ) (hT : 0 ≤ T) (hm : IntervalIntegrable m volume (-T) T)
    {Mm : ℝ} (hMm : ∀ r ∈ Icc (-T) T, |m r| ≤ Mm)
    {n D : ℕ} (φ : Fin n → ℝ → ℝ) (hφ : ∀ k, Continuous (φ k))
    (horth : ∀ j k, j ≠ k → ip ℓ (φ j) (φ k) = 0) (hd : ∀ k, 0 < ip ℓ (φ k) (φ k))
    (hspan : ∀ k < D, ∃ α : Fin n → ℝ, ∀ x, x ^ k = ∑ j, α j * φ j x)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hM : ∀ c : Fin n → ℝ, lam * ∑ k, ip ℓ (φ k) (φ k) * c k ^ 2 ≤
      ∑ j, ∑ k, c j * c k * B ℓ T β m (φ j) (φ k))
    (hμ : 0 ≤ β - 2 * ℓ * (2 * ((ℓ / 2) ^ D * Real.exp (ℓ / 2)) ^ 2 +
      Mm * T * ((T * ℓ) ^ D / D.factorial) ^ 2 / Real.pi))
    (hcond : (n : ℝ) * (2 * ℓ * (2 * Real.exp (ℓ / 2) * ((ℓ / 2) ^ D * Real.exp (ℓ / 2)) +
      Mm * T * ((T * ℓ) ^ D / D.factorial) / Real.pi)) ^ 2 ≤
      lam * (β - 2 * ℓ * (2 * ((ℓ / 2) ^ D * Real.exp (ℓ / 2)) ^ 2 +
        Mm * T * ((T * ℓ) ^ D / D.factorial) ^ 2 / Real.pi)))
    {g : ℝ → ℝ} (hg : Continuous g) : 0 ≤ B ℓ T β m g g := by
  set P := (ℓ / 2) ^ D * Real.exp (ℓ / 2) with hPdef
  set S := (T * ℓ) ^ D / D.factorial with hSdef
  set μ := β - 2 * ℓ * (2 * P ^ 2 + Mm * T * S ^ 2 / Real.pi) with hμdef
  set κ := 2 * Real.exp (ℓ / 2) * P + Mm * T * S / Real.pi with hκdef
  set d : Fin n → ℝ := fun k => ip ℓ (φ k) (φ k) with hddef
  set c : Fin n → ℝ := fun k => ip ℓ g (φ k) / d k with hcdef
  have hMm0 : 0 ≤ Mm := (abs_nonneg _).trans (hMm 0 ⟨by linarith, hT⟩)
  have hP0 : 0 ≤ P := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hp : Continuous fun x => ∑ k, c k * φ k x :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (hφ k)
  set t : ℝ → ℝ := fun x => g x - ∑ k, c k * φ k x with htdef
  have ht : Continuous t := hg.sub hp
  -- the remainder is orthogonal to the basis
  have horth_t : ∀ j, ip ℓ t (φ j) = 0 := by
    intro j
    have h1 : ip ℓ t (φ j) = ip ℓ g (φ j) - ∑ k, c k * ip ℓ (φ k) (φ j) := by
      rw [← ip_sum_left _ c hφ (hφ j)]
      unfold ip
      have i1 : IntervalIntegrable (fun x => g x * φ j x) volume (-ℓ) ℓ :=
        (hg.mul (hφ j)).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun x => (∑ k, c k * φ k x) * φ j x) volume (-ℓ) ℓ :=
        (hp.mul (hφ j)).intervalIntegrable _ _
      rw [← intervalIntegral.integral_sub i1 i2]
      congr 1; funext x; simp only [htdef]; ring
    rw [h1, Finset.sum_eq_single j (fun k _ hk => by rw [horth k j hk, mul_zero]) (by simp)]
    simp only [hcdef, hddef]
    rw [div_mul_cancel₀ _ (hd j).ne']; ring
  -- hence it has vanishing moments of order < D
  have hmom : ∀ k < D, ∫ x in (-ℓ)..ℓ, t x * x ^ k = 0 := by
    intro k hk
    obtain ⟨α, hα⟩ := hspan k hk
    have e : (fun x => t x * x ^ k) = fun x => ∑ j, α j * (t x * φ j x) := by
      funext x; rw [hα x, mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [e, intervalIntegral.integral_finsetSum]
    · refine sum_eq_zero fun j _ => ?_
      rw [intervalIntegral.integral_const_mul]
      have := horth_t j
      unfold ip at this
      rw [this, mul_zero]
    · intro j _; exact (continuous_const.mul (ht.mul (hφ j))).intervalIntegrable _ _
  -- expand along the basis
  have hgeq : g = fun x => (∑ k, c k * φ k x) + t x := by funext x; simp only [htdef]; ring
  rw [hgeq, B_expand hm c hφ ht]
  -- sizes
  set A := ∫ x in (-ℓ)..ℓ, |t x| with hAdef
  set τ := Real.sqrt (ip ℓ t t) with hτdef
  have hip_t : ip ℓ t t = ∫ x in (-ℓ)..ℓ, t x ^ 2 := by unfold ip; congr 1; funext x; ring
  have hA0 : 0 ≤ A := integral_nonneg (by linarith) fun x _ => abs_nonneg _
  have hipt0 : 0 ≤ ip ℓ t t := by
    rw [hip_t]; exact integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
  have hτ2 : τ ^ 2 = ip ℓ t t := Real.sq_sqrt hipt0
  have hA2 : A ^ 2 ≤ 2 * ℓ * τ ^ 2 := by rw [hτ2, hip_t]; exact sq_integral_abs_le hℓ ht
  have hAτ : A ≤ Real.sqrt (2 * ℓ) * τ := by
    rw [hτdef, ← Real.sqrt_mul (by linarith)]
    exact (Real.le_sqrt hA0 (mul_nonneg (by linarith) hipt0)).mpr
      (by rw [hip_t]; exact sq_integral_abs_le hℓ ht)
  have hAk : ∀ k, ∫ x in (-ℓ)..ℓ, |φ k x| ≤ Real.sqrt (2 * ℓ) * Real.sqrt (d k) := by
    intro k
    rw [← Real.sqrt_mul (by linarith)]
    refine (Real.le_sqrt (integral_nonneg (by linarith) fun x _ => abs_nonneg _)
      (mul_nonneg (by linarith) (hd k).le)).mpr ?_
    have := sq_integral_abs_le hℓ (hφ k)
    have e : ip ℓ (φ k) (φ k) = ∫ x in (-ℓ)..ℓ, φ k x ^ 2 := by
      unfold ip; congr 1; funext x; ring
    rwa [e]
  have hAk0 : ∀ k, 0 ≤ ∫ x in (-ℓ)..ℓ, |φ k x| :=
    fun k => integral_nonneg (by linarith) fun x _ => abs_nonneg _
  -- the tail
  have hl1 := abs_lap_half_le hℓ ht hmom (c := 1 / 2) (by norm_num)
  have hl2 := abs_lap_half_le hℓ ht hmom (c := -1 / 2) (by norm_num)
  have hsp := spec_tail_ge hℓ hT hm hMm ht hmom
  have hpi : 0 < Real.pi := Real.pi_pos
  have hW : μ * τ ^ 2 ≤ B ℓ T β m t t := by
    unfold B
    have hprod : -(P * A) ^ 2 ≤ lap ℓ t (1 / 2) * lap ℓ t (-1 / 2) := by
      have := abs_mul (lap ℓ t (1 / 2)) (lap ℓ t (-1 / 2))
      have h := mul_le_mul hl1 hl2 (abs_nonneg _) (by positivity)
      have := neg_abs_le (lap ℓ t (1 / 2) * lap ℓ t (-1 / 2))
      nlinarith
    have hprod' : -(P * A) ^ 2 ≤ lap ℓ t (-1 / 2) * lap ℓ t (1 / 2) := by
      linarith [hprod, mul_comm (lap ℓ t (1 / 2)) (lap ℓ t (-1 / 2))]
    have hsp' : -(Mm * T * S ^ 2 / Real.pi) * A ^ 2 ≤ 1 / (2 * Real.pi) * spec ℓ T m t t := by
      have h := mul_le_mul_of_nonneg_left hsp (by positivity : 0 ≤ 1 / (2 * Real.pi))
      have e : 1 / (2 * Real.pi) * (-(2 * T * Mm * S ^ 2) * A ^ 2) =
          -(Mm * T * S ^ 2 / Real.pi) * A ^ 2 := by field_simp
      linarith
    have hcoef : 0 ≤ 2 * P ^ 2 + Mm * T * S ^ 2 / Real.pi := by positivity
    have hβ : β * ip ℓ t t = β * τ ^ 2 := by rw [hτ2]
    have key : (2 * P ^ 2 + Mm * T * S ^ 2 / Real.pi) * A ^ 2 ≤
        (2 * P ^ 2 + Mm * T * S ^ 2 / Real.pi) * (2 * ℓ * τ ^ 2) :=
      mul_le_mul_of_nonneg_left hA2 hcoef
    rw [hμdef]
    nlinarith
  -- the coupling
  set ε : Fin n → ℝ := fun k => 2 * ℓ * κ * Real.sqrt (d k) with hεdef
  have hb : ∀ k, |B ℓ T β m (φ k) t| ≤ ε k * τ := by
    intro k
    set Ak := ∫ x in (-ℓ)..ℓ, |φ k x|
    have hipk : ip ℓ (φ k) t = 0 := by rw [ip_symm]; exact horth_t k
    have hpk1 := abs_lap_le hℓ (hφ k) (1 / 2)
    have hpk2 := abs_lap_le hℓ (hφ k) (-1 / 2)
    rw [show |(1 / 2 : ℝ)| * ℓ = ℓ / 2 by norm_num; ring] at hpk1
    rw [show |(-1 / 2 : ℝ)| * ℓ = ℓ / 2 by norm_num; ring] at hpk2
    have hsc := abs_spec_coupling_le (m := m) hℓ hT hMm (φ k) ht hmom
    have hbound : |B ℓ T β m (φ k) t| ≤ κ * (Ak * A) := by
      unfold B
      rw [hipk, mul_zero, add_zero]
      have e1 : |lap ℓ (φ k) (1 / 2) * lap ℓ t (-1 / 2)| ≤ Real.exp (ℓ / 2) * Ak * (P * A) := by
        rw [abs_mul]
        exact mul_le_mul hpk1 hl2 (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le (hAk0 k))
      have e2 : |lap ℓ (φ k) (-1 / 2) * lap ℓ t (1 / 2)| ≤ Real.exp (ℓ / 2) * Ak * (P * A) := by
        rw [abs_mul]
        exact mul_le_mul hpk2 hl1 (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le (hAk0 k))
      have e3 : |1 / (2 * Real.pi) * spec ℓ T m (φ k) t| ≤ Mm * T * S / Real.pi * (Ak * A) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
        have h := mul_le_mul_of_nonneg_left hsc (by positivity : 0 ≤ 1 / (2 * Real.pi))
        have e : 1 / (2 * Real.pi) * (2 * T * Mm * Ak * S * A) =
            Mm * T * S / Real.pi * (Ak * A) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul]
          rw [div_eq_div_iff (by positivity) (by positivity)]
          ring
        linarith
      calc _ ≤ |lap ℓ (φ k) (1 / 2) * lap ℓ t (-1 / 2)| + |lap ℓ (φ k) (-1 / 2) * lap ℓ t (1 / 2)| +
            |1 / (2 * Real.pi) * spec ℓ T m (φ k) t| := abs_add_three _ _ _
        _ ≤ Real.exp (ℓ / 2) * Ak * (P * A) + Real.exp (ℓ / 2) * Ak * (P * A) +
            Mm * T * S / Real.pi * (Ak * A) := add_le_add (add_le_add e1 e2) e3
        _ = κ * (Ak * A) := by rw [hκdef]; ring
    have hκ0 : 0 ≤ κ := by positivity
    have hAkA : Ak * A ≤ (Real.sqrt (2 * ℓ) * Real.sqrt (d k)) * (Real.sqrt (2 * ℓ) * τ) := by
      have h1 : Ak ≤ Real.sqrt (2 * ℓ) * Real.sqrt (d k) := hAk k
      have h2 : 0 ≤ Real.sqrt (2 * ℓ) * Real.sqrt (d k) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      exact mul_le_mul h1 hAτ hA0 h2
    have hs2 : Real.sqrt (2 * ℓ) * Real.sqrt (2 * ℓ) = 2 * ℓ :=
      Real.mul_self_sqrt (mul_nonneg zero_le_two hℓ)
    calc |B ℓ T β m (φ k) t| ≤ κ * (Ak * A) := hbound
      _ ≤ κ * ((Real.sqrt (2 * ℓ) * Real.sqrt (d k)) * (Real.sqrt (2 * ℓ) * τ)) :=
          mul_le_mul_of_nonneg_left hAkA hκ0
      _ = ε k * τ := by
          simp only [hεdef]
          rw [show Real.sqrt (2 * ℓ) * Real.sqrt (d k) * (Real.sqrt (2 * ℓ) * τ) =
            (Real.sqrt (2 * ℓ) * Real.sqrt (2 * ℓ)) * Real.sqrt (d k) * τ by ring, hs2]
          ring
  have hε : ∑ k, ε k ^ 2 / d k ≤ lam * μ := by
    have e : ∀ k, ε k ^ 2 / d k = (2 * ℓ * κ) ^ 2 := by
      intro k
      simp only [hεdef]
      rw [mul_pow, Real.sq_sqrt (hd k).le, mul_div_assoc, div_self (hd k).ne', mul_one]
    simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hcond
  exact GramTail.nonneg_of_block_tail _ _ c (fun k => B ℓ T β m (φ k) t) ε d τ lam μ hd hlam hμ
    (hM c) hW hb hε

end GppWindowTail

#print axioms GppWindowTail.sq_integral_abs_le
#print axioms GppWindowTail.abs_lap_le_of_moments
#print axioms GppWindowTail.norm_hw_le_of_moments
#print axioms GppWindowTail.window_form_nonneg
