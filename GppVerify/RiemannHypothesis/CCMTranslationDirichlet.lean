import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The CCM overlap kernel is a translation correlation

Source: Codex, 2026-09-30, "CCM pole-removed form as an exact translation Dirichlet energy minus a
mass" (GPPDiscovery2 `research/2026-09-30_ccm_translation_dirichlet_no_ghost.md`, §§1, 2 and 4).

On the window `[0, L]` with Fourier basis `U_n(x) = L^{−1/2} e^{2πinx/L}`, the CCM kernel `q`
is the real part of the one-sided overlap `C_f(y) = ∫₀^{L−y} f(x+y) f̄(x) dx`.

* `overlap_offdiag`: for `n ≠ m`,
  `∫₀^{L−y} U_m(x+y) Ū_n(x) dx = (e^{iα_n y} − e^{iα_m y}) / (2πi(m−n))`, with `α_k = 2πk/L`.
* `overlap_diag`: `∫₀^{L−y} U_n(x+y) Ū_n(x) dx = (1 − y/L) e^{iα_n y}`.
* `q_offdiag`: the Hermitian combination `K_{nm} + conj K_{mn}` is
  `(sin α_m y − sin α_n y)/(π(n−m))`. This is exactly the CCM off-diagonal kernel.
* `q_diag`: `K_{nn} + conj K_{nn} = 2(1 − y/L) cos α_n y`. This is the CCM diagonal kernel.
* `translation_identity`: for `‖g‖ = ‖f‖` in any inner-product space,
  `2 Re⟨g, f⟩ = 2‖f‖² − ‖f − g‖²`. With `g = T_y f` this says
  `q(f,f)(y) = 2‖f‖² − E_y(f)`, so the kernel is a correlation and its complement is a
  translation Dirichlet energy.
* `prime_form_rewrite`: the finite prime form `Σ wₙ q(log n)` equals
  `2(Σ wₙ)‖f‖² − Σ wₙ E_{log n}`. Each prime power contributes a positive energy to `−W_P`,
  plus a scalar mass.

Scope: the Archimedean constant `κ_R(L)` and the full identity `⟨f, Af⟩ = 𝒟_L(f) − μ_L‖f‖²` of
§§3, 5 use the CCM Archimedean matrix formula, which is not formalized here. The §7 equivalence
`Q ⪰ 0 ⇔ A|_𝒩 ⪰ 0` and the resulting constrained Poincaré target are **not** proved. That
target is RH-strength. No RH claim.
-/

namespace GppCCMTranslationDirichlet

open Complex Real

/-- The Fourier frequency `α_k = 2πk/L`. -/
noncomputable def α (L : ℝ) (k : ℤ) : ℝ := 2 * π * k / L

/-- The normalised Fourier basis on `[0, L]`. -/
noncomputable def U (L : ℝ) (k : ℤ) (x : ℝ) : ℂ := (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * exp (α L k * x * I)

lemma U_mul_conj (L : ℝ) (hL : 0 < L) (n m : ℤ) (y x : ℝ) :
    U L m (x + y) * (starRingEnd ℂ) (U L n x) =
      (1 / L : ℂ) * exp (α L m * y * I) * exp ((α L m - α L n) * x * I) := by
  have ha : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) = 1 / L := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hL.le]; push_cast; ring
  have key : exp (α L m * ((x + y : ℝ) : ℂ) * I) * exp (α L n * x * -I) =
      exp (α L m * y * I) * exp ((α L m - α L n) * x * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  simp only [U, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  calc (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * exp (α L m * ((x + y : ℝ) : ℂ) * I) *
        ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * exp (α L n * x * -I))
      = ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) *
          (exp (α L m * ((x + y : ℝ) : ℂ) * I) * exp (α L n * x * -I)) := by ring
    _ = (1 / L : ℂ) * exp (α L m * y * I) * exp ((α L m - α L n) * x * I) := by
        rw [ha, key]; ring

/-- Off-diagonal overlap. -/
theorem overlap_offdiag (L : ℝ) (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) (y : ℝ) :
    ∫ x in (0 : ℝ)..(L - y), U L m (x + y) * (starRingEnd ℂ) (U L n x) =
      (exp (α L n * y * I) - exp (α L m * y * I)) / (2 * π * I * (m - n)) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hmn : ((m : ℂ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm.symm)
  have hc : ((α L m - α L n : ℝ) : ℂ) * I ≠ 0 := by
    refine mul_ne_zero ?_ I_ne_zero
    have : (α L m - α L n : ℝ) = 2 * π * (m - n) / L := by unfold α; ring
    rw [this]; push_cast
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      hmn) hLc
  simp_rw [U_mul_conj L hL n m y]
  rw [intervalIntegral.integral_const_mul]
  have hint := integral_exp_mul_complex (a := 0) (b := L - y) hc
  have hrw : (fun x : ℝ => exp ((α L m - α L n) * x * I)) =
      fun x : ℝ => exp (((α L m - α L n : ℝ) : ℂ) * I * x) := by
    funext x; push_cast; ring_nf
  rw [hrw, hint]
  have hper : exp (((α L m - α L n : ℝ) : ℂ) * I * ((L - y : ℝ) : ℂ)) =
      exp (-((α L m - α L n : ℝ) : ℂ) * I * y) := by
    have h2 : exp (((α L m - α L n : ℝ) : ℂ) * I * L) = 1 := by
      rw [show ((α L m - α L n : ℝ) : ℂ) * I * L = ((m - n : ℤ) : ℂ) * (2 * π * I) by
        unfold α; push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [show ((α L m - α L n : ℝ) : ℂ) * I * ((L - y : ℝ) : ℂ) =
        ((α L m - α L n : ℝ) : ℂ) * I * L + (-((α L m - α L n : ℝ) : ℂ) * I * y) by
      push_cast; ring, Complex.exp_add, h2, one_mul]
  rw [hper]
  have hαdiff : ((α L m - α L n : ℝ) : ℂ) = 2 * π * (m - n) / L := by unfold α; push_cast; ring
  rw [hαdiff]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  have hexp : exp (α L m * y * I) * exp (-(2 * π * (m - n) / L) * I * y) =
      exp (α L n * y * I) := by
    rw [← Complex.exp_add]; congr 1; unfold α; push_cast; field_simp; ring
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show (1 / L : ℂ) * exp (α L m * y * I) *
      ((exp (-(2 * π * (m - n) / L) * I * y) - 1) / (2 * π * (m - n) / L * I)) =
      (1 / L) * ((exp (α L m * y * I) * exp (-(2 * π * (m - n) / L) * I * y) -
        exp (α L m * y * I)) / (2 * π * (m - n) / L * I)) by ring, hexp]
  field_simp

/-- Diagonal overlap. -/
theorem overlap_diag (L : ℝ) (hL : 0 < L) (n : ℤ) (y : ℝ) :
    ∫ x in (0 : ℝ)..(L - y), U L n (x + y) * (starRingEnd ℂ) (U L n x) =
      ((1 - y / L : ℝ) : ℂ) * exp (α L n * y * I) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  simp_rw [U_mul_conj L hL n n y, sub_self, zero_mul, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_const]
  simp only [real_smul, sub_zero]
  push_cast
  field_simp

/-- The off-diagonal CCM kernel: `K_{nm} + conj K_{mn} = (sin α_m y − sin α_n y)/(π(n − m))`. -/
theorem q_offdiag (L : ℝ) {n m : ℤ} (hnm : n ≠ m) (y : ℝ) :
    (exp (α L n * y * I) - exp (α L m * y * I)) / (2 * π * I * (m - n)) +
      (starRingEnd ℂ) ((exp (α L m * y * I) - exp (α L n * y * I)) / (2 * π * I * (n - m))) =
      ((Real.sin (α L m * y) - Real.sin (α L n * y)) / (π * (n - m)) : ℝ) := by
  have hmn : ((m : ℂ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm.symm)
  have hnm' : ((n : ℂ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [map_div₀, map_sub, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat, map_intCast]
  push_cast
  simp only [Complex.sin]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The diagonal CCM kernel: `K_{nn} + conj K_{nn} = 2(1 − y/L) cos α_n y`. -/
theorem q_diag (L : ℝ) (n : ℤ) (y : ℝ) :
    ((1 - y / L : ℝ) : ℂ) * exp (α L n * y * I) +
      (starRingEnd ℂ) (((1 - y / L : ℝ) : ℂ) * exp (α L n * y * I)) =
      ((2 * (1 - y / L) * Real.cos (α L n * y) : ℝ) : ℂ) := by
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  push_cast
  simp only [Complex.cos]
  ring_nf

/-- **Translation identity.** If `‖g‖ = ‖f‖`, then `2 Re⟨g, f⟩ = 2‖f‖² − ‖f − g‖²`. -/
theorem translation_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f g : E) (hfg : ‖g‖ = ‖f‖) :
    2 * (inner ℂ g f).re = 2 * ‖f‖ ^ 2 - ‖f - g‖ ^ 2 := by
  have h := @norm_sub_sq ℂ E _ _ _ f g
  rw [hfg] at h
  have hre := inner_re_symm (𝕜 := ℂ) f g
  have h2 : RCLike.re (inner ℂ g f) = (inner ℂ g f).re := rfl
  rw [h]
  linarith [hre, h2]

/-- **Prime-form rewrite.** With `q(y) = 2‖f‖² − E(y)`, the finite prime form is a positive
energy subtracted from a scalar mass. -/
theorem prime_form_rewrite {ι : Type*} (s : Finset ι) (w ℓ : ι → ℝ) (normSq : ℝ)
    (q E : ℝ → ℝ) (hq : ∀ y, q y = 2 * normSq - E y) :
    ∑ i ∈ s, w i * q (ℓ i) = 2 * (∑ i ∈ s, w i) * normSq - ∑ i ∈ s, w i * E (ℓ i) := by
  calc ∑ i ∈ s, w i * q (ℓ i) = ∑ i ∈ s, (2 * normSq * w i - w i * E (ℓ i)) :=
        Finset.sum_congr rfl fun i _ => by rw [hq]; ring
    _ = 2 * (∑ i ∈ s, w i) * normSq - ∑ i ∈ s, w i * E (ℓ i) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring

end GppCCMTranslationDirichlet
