import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Fourier reflection is indefinite: the Hermite mode `h₂` has eigenvalue `−1`

Source: Codex, GPP-bridge PR #11 comment 6123668210 (2026-10-12, idelic note
`work/codex/2026-10-12_idelic_compact_K_peter_weyl_tate_os_sewing.md`, no-go (2)).

The self-dual Gaussian `g(x) = e^{−πx²}` is Fourier-fixed (`fourier_g`). The second Hermite function
`h₂(x) = (4πx² − 1)e^{−πx²}` satisfies **`𝓕 h₂ = −h₂`** (`fourier_h2`). The proof is exact and uses
no special-function theory: `h₂ = g''/π + g`, and Mathlib's `fourier_deriv` (`𝓕 f' = 2πiξ·𝓕 f`)
applied twice gives `𝓕 g'' = −4π²ξ² g`. Hence `conj(h₂)·𝓕h₂ = −|h₂|²` pointwise
(`pairing_neg`), so the Fourier "reflection" pairing `⟨h₂, 𝓕 h₂⟩ = −‖h₂‖² < 0`.

**Ledger use.** Unitary additive-Fourier reflection, even restricted to the `K`-trivial (spherical finite-part) sector, is **not** a positive form. Tensoring with the self-dual finite spherical vector
`1_Ẑ` gives the adelic witness; that tensor step needs adelic Fourier analysis that Mathlib lacks, so
it is stated here only. This does not contradict Osterwalder–Schrader positivity, which is a
positive-*time* half-space condition. It shows that `K`-compactness plus Fourier unitarity alone
cannot supply positivity. **No RH claim.**
-/

namespace GppNoGo.HermiteFourierIndefinite

open Real Complex MeasureTheory FourierTransform

/-- The self-dual Gaussian `e^{−πx²}`. -/
noncomputable def g (x : ℝ) : ℂ := cexp (-(π : ℂ) * (x : ℂ) ^ 2)

lemma integrable_fourier_smul {f : ℝ → ℂ} (hf : Integrable f) (w : ℝ) :
    Integrable (fun v : ℝ => 𝐞 (-(v * w)) • f v) := by
  have := (VectorFourier.fourierIntegral_convergent_iff (e := 𝐞) (μ := volume)
    (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) w).2 hf
  simpa [mul_comm] using this

lemma fourier_lin {f₁ f₂ : ℝ → ℂ} (h₁ : Integrable f₁) (h₂ : Integrable f₂) (c : ℂ) (w : ℝ) :
    𝓕 (fun x => c * f₁ x + f₂ x) w = c * 𝓕 f₁ w + 𝓕 f₂ w := by
  rw [fourier_real_eq, fourier_real_eq, fourier_real_eq, ← integral_const_mul,
    ← integral_add ((integrable_fourier_smul h₁ w).const_mul c) (integrable_fourier_smul h₂ w)]
  congr 1
  ext v
  simp only [Circle.smul_def, smul_eq_mul]
  ring

lemma fourier_g : 𝓕 g = g := by
  have := fourier_gaussian_pi (b := 1) (by simp)
  ext t
  have ht := congrFun this t
  simp only [mul_one, one_cpow, div_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at ht
  rw [show g = fun x : ℝ => cexp (-(↑π * ↑x ^ 2)) from funext fun x => by simp [g]]
  simpa using ht

/-- `g' = −2πx·g`. -/
noncomputable def g1 (x : ℝ) : ℂ := -2 * π * x * g x

lemma hasDerivAt_g (x : ℝ) : HasDerivAt g (g1 x) x := by
  have hin : HasDerivAt (fun y : ℝ => -(π : ℂ) * (y : ℂ) ^ 2) (-(π : ℂ) * (2 * x)) x := by
    have := ((hasDerivAt_id x).ofReal_comp).pow 2
    simpa using this.const_mul (-(π : ℂ))
  have := hin.cexp
  refine this.congr_deriv ?_
  simp only [g1, g]
  ring

/-- `g'' = (4π²x² − 2π)·g`. -/
noncomputable def g2 (x : ℝ) : ℂ := (4 * π ^ 2 * x ^ 2 - 2 * π) * g x

lemma hasDerivAt_g1 (x : ℝ) : HasDerivAt g1 (g2 x) x := by
  have hlin : HasDerivAt (fun y : ℝ => -2 * (π : ℂ) * (y : ℂ)) (-2 * π) x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-2 * (π : ℂ))
  have := hlin.mul (hasDerivAt_g x)
  refine this.congr_deriv ?_
  simp only [g2, g1]
  ring

lemma deriv_g : deriv g = g1 := funext fun x => (hasDerivAt_g x).deriv
lemma deriv_g1 : deriv g1 = g2 := funext fun x => (hasDerivAt_g1 x).deriv

lemma integrable_g : Integrable g := by
  have := integrable_cexp_neg_mul_sq (b := (π : ℂ)) (by simp [pi_pos])
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [g]

lemma integrable_xg : Integrable fun x : ℝ => (x : ℂ) * g x := by
  have := integrable_mul_cexp_neg_mul_sq (b := (π : ℂ)) (by simp [pi_pos])
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [g]

lemma integrable_x2g : Integrable fun x : ℝ => (x : ℂ) ^ 2 * g x := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := π) pi_pos (s := 2) (by norm_num)
  have h' := h.ofReal (𝕜 := ℂ)
  refine h'.congr (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [g]
  push_cast
  congr 1
  rw [show (-(π : ℂ) * (x : ℂ) ^ 2) = ((-π * x ^ 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  rfl

lemma integrable_g1 : Integrable g1 := by
  have := integrable_xg.const_mul (-2 * (π : ℂ))
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [g1]; ring

lemma integrable_g2 : Integrable g2 := by
  have := (integrable_x2g.const_mul (4 * (π : ℂ) ^ 2)).sub (integrable_g.const_mul (2 * (π : ℂ)))
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [g2, Pi.sub_apply]; ring

lemma differentiable_g : Differentiable ℝ g := fun x => (hasDerivAt_g x).differentiableAt
lemma differentiable_g1 : Differentiable ℝ g1 := fun x => (hasDerivAt_g1 x).differentiableAt

lemma fourier_g1 (w : ℝ) : 𝓕 g1 w = 2 * π * I * w * g w := by
  have := congrFun (fourier_deriv integrable_g differentiable_g (deriv_g ▸ integrable_g1)) w
  rw [deriv_g, fourier_g] at this
  simpa [smul_eq_mul] using this

lemma fourier_g2 (w : ℝ) : 𝓕 g2 w = -(4 * π ^ 2 * w ^ 2) * g w := by
  have := congrFun (fourier_deriv integrable_g1 differentiable_g1 (deriv_g1 ▸ integrable_g2)) w
  rw [deriv_g1, fourier_g1] at this
  rw [this, smul_eq_mul]
  ring_nf
  rw [I_sq]
  ring

/-- The second Hermite function `h₂(x) = (4πx² − 1)e^{−πx²}`. -/
noncomputable def h2 (x : ℝ) : ℂ := (4 * π * x ^ 2 - 1) * g x

/-- **`h₂` has Fourier eigenvalue `−1`.** -/
theorem fourier_h2 : 𝓕 h2 = fun w => -h2 w := by
  have hh : h2 = fun x => (1 / (π : ℂ)) * g2 x + g x := by
    funext x
    have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    simp only [h2, g2]
    field_simp
    ring
  ext w
  rw [hh, fourier_lin integrable_g2 integrable_g, fourier_g2, fourier_g]
  have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  simp only [g2]
  field_simp
  ring

/-- **The reflection pairing is negative:** `conj(h₂)·𝓕h₂ = −|h₂|²` at every point. -/
theorem pairing_neg (x : ℝ) :
    (starRingEnd ℂ) (h2 x) * 𝓕 h2 x = -((‖h2 x‖ ^ 2 : ℝ) : ℂ) := by
  rw [fourier_h2, mul_neg, Complex.conj_mul']
  push_cast
  ring

/-- `h₂` is not the zero function: `h₂(0) = −1`. -/
theorem h2_zero : h2 0 = -1 := by simp [h2, g]

end GppNoGo.HermiteFourierIndefinite
