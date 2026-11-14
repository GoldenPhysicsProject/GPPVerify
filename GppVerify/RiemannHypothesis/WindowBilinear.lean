import GppVerify.RiemannHypothesis.WindowGramForm
import GppVerify.Upstream.ExpTaylorImaginary
import GppVerify.Upstream.GramTailBound

/-!
# The window minorant form as a symmetric bilinear form on `C([-ℓ, ℓ])`

For a window half-width `ℓ`, a frequency cut `T`, a constant `β` and a symbol minorant `m`, set

  `B(f, g) = G₊(f) G₋(g) + G₋(f) G₊(g) + β ⟨f, g⟩ + (1/2π) ∫_{-T}^{T} m(r) Re(h_f(r) conj h_g(r)) dr`

with every transform taken over `[-ℓ, ℓ]` (`G_±(f) = ∫ f e^{±x/2}`, `⟨f, g⟩ = ∫ f g`,
`h_f(r) = ∫ f(x) e^{irx}`). For continuous arguments `B` is symmetric and bilinear
(`B_symm`, `B_add_left`, `B_sum_left`), so it expands along a finite basis plus a remainder
(`B_expand`):

  `B(p + t, p + t) = Σ_{j,k} c_j c_k B(φ_j, φ_k) + 2 Σ_k c_k B(φ_k, t) + B(t, t)`,  `p = Σ c_k φ_k`.

This is the form a matrix certificate evaluates on the finite block. Unconditional; no `sorry`.
-/

namespace GppWindowBilinear

open Complex Set MeasureTheory intervalIntegral Finset
open scoped ComplexConjugate

/-- `h_f(r) = ∫_{-ℓ}^{ℓ} f(x) e^{irx} dx`. -/
noncomputable def hw (ℓ : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℂ :=
  ∫ x in (-ℓ)..ℓ, (f x : ℂ) * cexp (I * ((r * x : ℝ) : ℂ))

/-- `∫_{-ℓ}^{ℓ} f(x) e^{cx} dx`. -/
noncomputable def lap (ℓ : ℝ) (f : ℝ → ℝ) (c : ℝ) : ℝ := ∫ x in (-ℓ)..ℓ, f x * Real.exp (c * x)

/-- `⟨f, g⟩ = ∫_{-ℓ}^{ℓ} f g`. -/
noncomputable def ip (ℓ : ℝ) (f g : ℝ → ℝ) : ℝ := ∫ x in (-ℓ)..ℓ, f x * g x

/-- `∫_{-T}^{T} m(r) Re(h_f(r) conj h_g(r)) dr`. -/
noncomputable def spec (ℓ T : ℝ) (m : ℝ → ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ r in (-T)..T, m r * (hw ℓ f r * conj (hw ℓ g r)).re

/-- **The window form.** -/
noncomputable def B (ℓ T β : ℝ) (m : ℝ → ℝ) (f g : ℝ → ℝ) : ℝ :=
  lap ℓ f (1 / 2) * lap ℓ g (-1 / 2) + lap ℓ f (-1 / 2) * lap ℓ g (1 / 2) + β * ip ℓ f g +
    (1 / (2 * Real.pi)) * spec ℓ T m f g

variable {ℓ T β : ℝ} {m : ℝ → ℝ}

/-! ### Continuity and integrability -/

theorem continuous_hw {f : ℝ → ℝ} (hf : Continuous f) : Continuous (hw ℓ f) := by
  unfold hw
  exact continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _

theorem intervalIntegrable_spec_integrand (hm : IntervalIntegrable m volume (-T) T)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    IntervalIntegrable (fun r => m r * (hw ℓ f r * conj (hw ℓ g r)).re) volume (-T) T :=
  hm.mul_continuousOn
    (Complex.continuous_re.comp ((continuous_hw hf).mul
      (Complex.continuous_conj.comp (continuous_hw hg)))).continuousOn

/-! ### Linearity of the transforms -/

theorem hw_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    hw ℓ (fun x => f x + g x) r = hw ℓ f r + hw ℓ g r := by
  unfold hw
  rw [← integral_add ((by fun_prop : Continuous fun x : ℝ =>
      (f x : ℂ) * cexp (I * ((r * x : ℝ) : ℂ))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ =>
      (g x : ℂ) * cexp (I * ((r * x : ℝ) : ℂ))).intervalIntegrable _ _)]
  congr 1; funext x; push_cast; ring

theorem hw_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ k, Continuous (φ k)) (r : ℝ) :
    hw ℓ (fun x => ∑ k ∈ s, c k * φ k x) r = ∑ k ∈ s, (c k : ℂ) * hw ℓ (φ k) r := by
  unfold hw
  have : (fun x : ℝ => ((∑ k ∈ s, c k * φ k x : ℝ) : ℂ) * cexp (I * ((r * x : ℝ) : ℂ))) =
      fun x => ∑ k ∈ s, (c k : ℂ) * ((φ k x : ℂ) * cexp (I * ((r * x : ℝ) : ℂ))) := by
    funext x; push_cast; rw [sum_mul]; refine sum_congr rfl fun k _ => by ring
  rw [this, intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul]
  · intro k _
    exact ((by fun_prop : Continuous fun x : ℝ =>
      (c k : ℂ) * ((φ k x : ℂ) * cexp (I * ((r * x : ℝ) : ℂ))))).intervalIntegrable _ _

theorem lap_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (c : ℝ) :
    lap ℓ (fun x => f x + g x) c = lap ℓ f c + lap ℓ g c := by
  unfold lap
  rw [← integral_add ((by fun_prop : Continuous fun x => f x * Real.exp (c * x)).intervalIntegrable
    _ _) ((by fun_prop : Continuous fun x => g x * Real.exp (c * x)).intervalIntegrable _ _)]
  congr 1; funext x; ring

theorem lap_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ k, Continuous (φ k)) (c : ℝ) :
    lap ℓ (fun x => ∑ k ∈ s, a k * φ k x) c = ∑ k ∈ s, a k * lap ℓ (φ k) c := by
  unfold lap
  simp_rw [sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun k _ => ?_
    simp_rw [mul_assoc]; rw [intervalIntegral.integral_const_mul]
  · intro k _
    exact ((by fun_prop : Continuous fun x => a k * φ k x * Real.exp (c * x))).intervalIntegrable _ _

theorem ip_symm (f g : ℝ → ℝ) : ip ℓ f g = ip ℓ g f := by
  unfold ip; congr 1; funext x; ring

theorem ip_add_left {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    ip ℓ (fun x => f x + g x) h = ip ℓ f h + ip ℓ g h := by
  unfold ip
  rw [← integral_add ((by fun_prop : Continuous fun x => f x * h x).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x => g x * h x).intervalIntegrable _ _)]
  congr 1; funext x; ring

theorem ip_sum_left {ι : Type*} (s : Finset ι) (a : ι → ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ k, Continuous (φ k)) {h : ℝ → ℝ} (hh : Continuous h) :
    ip ℓ (fun x => ∑ k ∈ s, a k * φ k x) h = ∑ k ∈ s, a k * ip ℓ (φ k) h := by
  unfold ip
  simp_rw [sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun k _ => ?_
    simp_rw [mul_assoc]; rw [intervalIntegral.integral_const_mul]
  · intro k _
    exact ((continuous_const.mul (hφ k)).mul hh).intervalIntegrable _ _

theorem spec_symm (f g : ℝ → ℝ) : spec ℓ T m f g = spec ℓ T m g f := by
  unfold spec; congr 1; funext r
  congr 1
  rw [show hw ℓ g r * conj (hw ℓ f r) = conj (hw ℓ f r * conj (hw ℓ g r)) by
    rw [map_mul, Complex.conj_conj, mul_comm], Complex.conj_re]

theorem spec_add_left (hm : IntervalIntegrable m volume (-T) T) {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    spec ℓ T m (fun x => f x + g x) h = spec ℓ T m f h + spec ℓ T m g h := by
  unfold spec
  rw [← integral_add (intervalIntegrable_spec_integrand hm hf hh)
    (intervalIntegrable_spec_integrand hm hg hh)]
  congr 1; funext r
  rw [hw_add hf hg, add_mul, Complex.add_re]; ring

theorem spec_sum_left (hm : IntervalIntegrable m volume (-T) T) {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) {φ : ι → ℝ → ℝ} (hφ : ∀ k, Continuous (φ k)) {h : ℝ → ℝ} (hh : Continuous h) :
    spec ℓ T m (fun x => ∑ k ∈ s, a k * φ k x) h = ∑ k ∈ s, a k * spec ℓ T m (φ k) h := by
  unfold spec
  have e : (fun r => m r * (hw ℓ (fun x => ∑ k ∈ s, a k * φ k x) r * conj (hw ℓ h r)).re) =
      fun r => ∑ k ∈ s, a k * (m r * (hw ℓ (φ k) r * conj (hw ℓ h r)).re) := by
    funext r
    rw [hw_sum s a hφ, sum_mul, Complex.re_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.re_ofReal_mul]; ring
  rw [e, intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun k _ => by rw [intervalIntegral.integral_const_mul]
  · intro k _
    exact (intervalIntegrable_spec_integrand hm (hφ k) hh).const_mul _

/-! ### The form -/

theorem B_symm (f g : ℝ → ℝ) : B ℓ T β m f g = B ℓ T β m g f := by
  unfold B; rw [ip_symm, spec_symm]; ring

theorem B_add_left (hm : IntervalIntegrable m volume (-T) T) {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    B ℓ T β m (fun x => f x + g x) h = B ℓ T β m f h + B ℓ T β m g h := by
  unfold B
  rw [lap_add hf hg, lap_add hf hg, ip_add_left hf hg hh, spec_add_left hm hf hg hh]
  ring

theorem B_sum_left (hm : IntervalIntegrable m volume (-T) T) {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) {φ : ι → ℝ → ℝ} (hφ : ∀ k, Continuous (φ k)) {h : ℝ → ℝ} (hh : Continuous h) :
    B ℓ T β m (fun x => ∑ k ∈ s, a k * φ k x) h = ∑ k ∈ s, a k * B ℓ T β m (φ k) h := by
  unfold B
  rw [lap_sum s a hφ, lap_sum s a hφ, ip_sum_left s a hφ hh, spec_sum_left hm s a hφ hh]
  simp only [sum_mul, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => by ring

/-- **Expansion along a finite basis plus a remainder.** -/
theorem B_expand (hm : IntervalIntegrable m volume (-T) T) {n : ℕ} (c : Fin n → ℝ)
    {φ : Fin n → ℝ → ℝ} (hφ : ∀ k, Continuous (φ k)) {t : ℝ → ℝ} (ht : Continuous t) :
    B ℓ T β m (fun x => (∑ k, c k * φ k x) + t x) (fun x => (∑ k, c k * φ k x) + t x) =
      ∑ j, ∑ k, c j * c k * B ℓ T β m (φ j) (φ k) + 2 * ∑ k, c k * B ℓ T β m (φ k) t +
        B ℓ T β m t t := by
  have hp : Continuous fun x => ∑ k, c k * φ k x :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (hφ k)
  have hpt : Continuous fun x => (∑ k, c k * φ k x) + t x := hp.add ht
  rw [B_add_left hm hp ht hpt, B_sum_left hm _ c hφ hpt, B_symm t, B_add_left hm hp ht ht,
    B_sum_left hm _ c hφ ht]
  have hk : ∀ k, B ℓ T β m (φ k) (fun x => (∑ j, c j * φ j x) + t x) =
      ∑ j, c j * B ℓ T β m (φ j) (φ k) + B ℓ T β m (φ k) t := by
    intro k
    rw [B_symm, B_add_left hm hp ht (hφ k), B_sum_left hm _ c hφ (hφ k), B_symm t]
  simp only [hk, mul_add, sum_add_distrib, mul_sum]
  have h1 : ∑ x, ∑ i, c x * (c i * B ℓ T β m (φ i) (φ x)) =
      ∑ j, ∑ k, c j * c k * B ℓ T β m (φ j) (φ k) := by
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by rw [B_symm (φ k)]; ring
  have h2 : ∑ i, 2 * (c i * B ℓ T β m (φ i) t) = 2 * ∑ i, c i * B ℓ T β m (φ i) t := by
    rw [mul_sum]
  rw [h1, h2]
  ring

end GppWindowBilinear

#print axioms GppWindowBilinear.B_expand
