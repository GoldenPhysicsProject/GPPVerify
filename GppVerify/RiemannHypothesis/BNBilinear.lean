import GppVerify.RiemannHypothesis.BNPositivity
import GppVerify.RiemannHypothesis.FormGNS
import GppVerify.RiemannHypothesis.AutocorrTransport

/-!
# The bilinear form `b_N` behind `B_N`, and its Hilbert completion

Turbo's build order (bridge `0518bf9`), steps (1)–(3): polarise `B_N`, build the Hilbert completion
`H_{B,N,L}` of the width-`L` test functions through `FormGNS`, extend `C_N` to a bounded operator.

This file: **cross-correlation** `xcorr f g x = ∫ f(y) g(y − x) dy` (a test function when `f`, `g` are),
the **linearity** of `Λ(a) = poleTerm a + archimedeanTerm a` on test functions, and the **bilinear form**

  `b_N(f, g) = ½ [Λ(f ⋆ g̃) + Λ(g ⋆ f̃)] + θ(N) ∫ f g`,

symmetric by construction, with diagonal `b_N(f, f) = B_N(f)` (`bnBil_self`). The window space `V_L`
(test functions supported in `[−L/2, L/2]`) is a real vector space (`windowSubmodule`) and `b_N` is a
`LinearMap.mk₂` on it.

No `sorry`, no axiom.
-/

open MeasureTheory Set
open GppArithmeticReflection GppArchimedeanFloor GppMeyerSpectralWeil GppRungZeroPositivity
open scoped ContDiff Convolution

noncomputable section

namespace GppShiftPresentation

/-- Cross-correlation `(f ⋆ g̃)(x) = ∫ f(y) g(y − x) dy`; `xcorr f f = autocorr f`. -/
def xcorr (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, f y * g (y - x)

theorem xcorr_self (f : ℝ → ℝ) : xcorr f f = autocorr f := rfl

theorem xcorr_eq_convolution (f g : ℝ → ℝ) :
    xcorr f g = (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun t => g (-t)) := by
  funext x
  rw [convolution_mul]
  unfold xcorr
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [neg_sub]

/-- **The cross-correlation of two test functions is a test function.** -/
theorem isTestFunction_xcorr {f g : ℝ → ℝ} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (xcorr f g) := by
  have hneg_c : HasCompactSupport (fun t : ℝ => g (-t)) := hg.2.comp_homeomorph (Homeomorph.neg ℝ)
  have hneg_d : ContDiff ℝ ∞ (fun t : ℝ => g (-t)) := hg.1.comp contDiff_neg
  rw [xcorr_eq_convolution]
  exact ⟨hneg_c.contDiff_convolution_right _ hf.1.continuous.locallyIntegrable hneg_d,
    hf.2.convolution _ hneg_c⟩

/-! ### Linearity of `Λ = poleTerm + archimedeanTerm` on test functions -/

theorem poleTerm_add {a b : ℝ → ℝ} (ha : IsTestFunction a) (hb : IsTestFunction b) :
    poleTerm (a + b) = poleTerm a + poleTerm b := by
  have hK : Continuous fun u : ℝ => 2 * Real.cosh (u / 2) := by fun_prop
  have hia : Integrable fun u => a u * (2 * Real.cosh (u / 2)) :=
    (ha.1.continuous.mul hK).integrable_of_hasCompactSupport ha.2.mul_right
  have hib : Integrable fun u => b u * (2 * Real.cosh (u / 2)) :=
    (hb.1.continuous.mul hK).integrable_of_hasCompactSupport hb.2.mul_right
  unfold poleTerm
  rw [← integral_add hia hib]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]; ring

theorem poleTerm_smul (c : ℝ) (a : ℝ → ℝ) : poleTerm (c • a) = c * poleTerm a := by
  unfold poleTerm
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem archimedeanIntegrand_add (a b : ℝ → ℝ) (u : ℝ) :
    archimedeanIntegrand (a + b) u = archimedeanIntegrand a u + archimedeanIntegrand b u := by
  unfold archimedeanIntegrand
  simp only [Pi.add_apply]; ring

theorem archimedeanIntegrand_smul (c : ℝ) (a : ℝ → ℝ) (u : ℝ) :
    archimedeanIntegrand (c • a) u = c * archimedeanIntegrand a u := by
  unfold archimedeanIntegrand
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem archimedeanTerm_add {a b : ℝ → ℝ} (ha : IsTestFunction a) (hb : IsTestFunction b) :
    archimedeanTerm (a + b) = archimedeanTerm a + archimedeanTerm b := by
  have hia := integrableOn_archimedeanIntegrand ha.1 ha.2
  have hib := integrableOn_archimedeanIntegrand hb.1 hb.2
  unfold archimedeanTerm
  simp only [archimedeanIntegrand_add, Pi.add_apply]
  rw [integral_add hia hib]
  ring

theorem archimedeanTerm_smul (c : ℝ) (a : ℝ → ℝ) :
    archimedeanTerm (c • a) = c * archimedeanTerm a := by
  unfold archimedeanTerm
  simp only [archimedeanIntegrand_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  ring

/-- `Λ(a) = poleTerm a + archimedeanTerm a`. -/
def lam (a : ℝ → ℝ) : ℝ := poleTerm a + archimedeanTerm a

theorem lam_add {a b : ℝ → ℝ} (ha : IsTestFunction a) (hb : IsTestFunction b) :
    lam (a + b) = lam a + lam b := by
  unfold lam; rw [poleTerm_add ha hb, archimedeanTerm_add ha hb]; ring

theorem lam_smul (c : ℝ) (a : ℝ → ℝ) : lam (c • a) = c * lam a := by
  unfold lam; rw [poleTerm_smul, archimedeanTerm_smul]; ring

/-! ### Bilinearity of the cross-correlation -/

theorem integrable_mul_shift_test {f g : ℝ → ℝ} (hf : IsTestFunction f) (hg : IsTestFunction g)
    (x : ℝ) : Integrable fun y => f y * g (y - x) :=
  (hf.1.continuous.mul (hg.1.continuous.comp (continuous_id.sub continuous_const))
    ).integrable_of_hasCompactSupport hf.2.mul_right

theorem xcorr_add_left {f₁ f₂ g : ℝ → ℝ} (h₁ : IsTestFunction f₁) (h₂ : IsTestFunction f₂)
    (hg : IsTestFunction g) : xcorr (f₁ + f₂) g = xcorr f₁ g + xcorr f₂ g := by
  funext x
  simp only [xcorr, Pi.add_apply]
  rw [← integral_add (integrable_mul_shift_test h₁ hg x) (integrable_mul_shift_test h₂ hg x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

theorem xcorr_smul_left (c : ℝ) (f g : ℝ → ℝ) : xcorr (c • f) g = c • xcorr f g := by
  funext x
  simp only [xcorr, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

theorem xcorr_add_right {f g₁ g₂ : ℝ → ℝ} (hf : IsTestFunction f) (h₁ : IsTestFunction g₁)
    (h₂ : IsTestFunction g₂) : xcorr f (g₁ + g₂) = xcorr f g₁ + xcorr f g₂ := by
  funext x
  simp only [xcorr, Pi.add_apply]
  rw [← integral_add (integrable_mul_shift_test hf h₁ x) (integrable_mul_shift_test hf h₂ x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mul_add]

theorem xcorr_smul_right (c : ℝ) (f g : ℝ → ℝ) : xcorr f (c • g) = c • xcorr f g := by
  funext x
  simp only [xcorr, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-! ### The window space and the bilinear form -/

/-- The real vector space `V_L` of test functions supported in `[−L/2, L/2]`. -/
def windowSubmodule (L : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsTestFunction f ∧ ∀ y : ℝ, L / 2 < |y| → f y = 0}
  add_mem' := fun {_ _} hf hg => ⟨⟨hf.1.1.add hg.1.1, hf.1.2.add hg.1.2⟩,
    fun y hy => by simp [hf.2 y hy, hg.2 y hy]⟩
  zero_mem' := ⟨⟨contDiff_const, HasCompactSupport.zero⟩, fun y _ => rfl⟩
  smul_mem' := fun c _ hf => ⟨⟨hf.1.1.const_smul c, hf.1.2.smul_left⟩,
    fun y hy => by simp [hf.2 y hy]⟩

/-- `θ(N) = Σ_{p ≤ N} log p`. -/
def thetaN (N : ℕ) : ℝ := ∑ p ∈ primesUpTo N, Real.log p

/-- The symmetrised bilinear expression `b_N(f, g)` on functions. -/
def bnBilFun (N : ℕ) (f g : ℝ → ℝ) : ℝ :=
  (lam (xcorr f g) + lam (xcorr g f)) / 2 + thetaN N * ∫ y, f y * g y

theorem bnBilFun_symm (N : ℕ) (f g : ℝ → ℝ) : bnBilFun N f g = bnBilFun N g f := by
  unfold bnBilFun
  rw [add_comm (lam (xcorr f g))]
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-- **The diagonal is `B_N`.** -/
theorem bnBilFun_self (N : ℕ) (f : ℝ → ℝ) : bnBilFun N f f = BNform N f := by
  unfold bnBilFun BNform massDefectSum thetaN lam
  rw [xcorr_self, autocorr_zero_eq]
  have h : (fun y => f y * f y) = fun y => f y ^ 2 := by funext y; ring
  rw [h]
  ring

theorem integral_mul_test_add {f₁ f₂ g : ℝ → ℝ} (h₁ : IsTestFunction f₁) (h₂ : IsTestFunction f₂)
    (hg : IsTestFunction g) :
    ∫ y, (f₁ + f₂) y * g y = (∫ y, f₁ y * g y) + ∫ y, f₂ y * g y := by
  have hi : ∀ f : ℝ → ℝ, IsTestFunction f → Integrable fun y => f y * g y := fun f hf =>
    (hf.1.continuous.mul hg.1.continuous).integrable_of_hasCompactSupport hf.2.mul_right
  rw [← integral_add (hi _ h₁) (hi _ h₂)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply]; ring

theorem bnBilFun_add_left (N : ℕ) {f₁ f₂ g : ℝ → ℝ} (h₁ : IsTestFunction f₁)
    (h₂ : IsTestFunction f₂) (hg : IsTestFunction g) :
    bnBilFun N (f₁ + f₂) g = bnBilFun N f₁ g + bnBilFun N f₂ g := by
  unfold bnBilFun
  rw [xcorr_add_left h₁ h₂ hg, xcorr_add_right hg h₁ h₂,
    lam_add (isTestFunction_xcorr h₁ hg) (isTestFunction_xcorr h₂ hg),
    lam_add (isTestFunction_xcorr hg h₁) (isTestFunction_xcorr hg h₂),
    integral_mul_test_add h₁ h₂ hg]
  ring

theorem bnBilFun_smul_left (N : ℕ) (c : ℝ) (f g : ℝ → ℝ) :
    bnBilFun N (c • f) g = c * bnBilFun N f g := by
  unfold bnBilFun
  rw [xcorr_smul_left, xcorr_smul_right, lam_smul, lam_smul]
  have : ∫ y, (c • f) y * g y = c * ∫ y, f y * g y := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this]; ring

/-- **The bilinear form `b_N` on `V_L`.** -/
def bnBilin (N : ℕ) (L : ℝ) : windowSubmodule L →ₗ[ℝ] windowSubmodule L →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => bnBilFun N f.1 g.1)
    (fun f₁ f₂ g => bnBilFun_add_left N f₁.2.1 f₂.2.1 g.2.1)
    (fun c f g => by
      rw [smul_eq_mul]
      exact bnBilFun_smul_left N c f.1 g.1)
    (fun f g₁ g₂ => by
      rw [bnBilFun_symm, show ((g₁ + g₂ : windowSubmodule L) : ℝ → ℝ) = g₁.1 + g₂.1 from rfl,
        bnBilFun_add_left N g₁.2.1 g₂.2.1 f.2.1, bnBilFun_symm N g₁.1, bnBilFun_symm N g₂.1])
    (fun c f g => by
      rw [bnBilFun_symm, show ((c • g : windowSubmodule L) : ℝ → ℝ) = c • g.1 from rfl,
        bnBilFun_smul_left, bnBilFun_symm, smul_eq_mul])

theorem bnBilin_apply (N : ℕ) (L : ℝ) (f g : windowSubmodule L) :
    bnBilin N L f g = bnBilFun N f.1 g.1 := rfl

/-- **`b_N(f, f) = B_N(f)`.** -/
theorem bnBilin_self (N : ℕ) (L : ℝ) (f : windowSubmodule L) :
    bnBilin N L f f = BNform N f.1 := bnBilFun_self N f.1

theorem bnBilin_symm (N : ℕ) (L : ℝ) (f g : windowSubmodule L) :
    bnBilin N L f g = bnBilin N L g f := bnBilFun_symm N f.1 g.1

/-- **Coercivity on `V_L`:** `b_N(f, f) ≥ (θ(N) + κ_L) ‖f‖²`. -/
theorem bnBilin_self_ge (N : ℕ) {L : ℝ} (hL : 0 ≤ L) (f : windowSubmodule L) :
    (thetaN N + kappa L) * autocorr f.1 0 ≤ bnBilin N L f f := by
  rw [bnBilin_self]
  exact BNform_ge f.2.1.1 f.2.1.2 hL f.2.2 N

/-- **`b_N` is positive-semidefinite on `V_L`** once `θ(N) + κ_L ≥ 0`. -/
theorem psd_bnBilin (N : ℕ) {L : ℝ} (hL : 0 ≤ L) (hθ : 0 ≤ thetaN N + kappa L) :
    GppFormGNS.PSD (bnBilin N L) where
  symm := bnBilin_symm N L
  nonneg f := (mul_nonneg hθ (autocorr_zero_nonneg f.1)).trans (bnBilin_self_ge N hL f)

/-- **The Hilbert completion `H_{B,N,L}` of `(V_L, b_N)`** (Turbo's build-order step (3), first half):
a real Hilbert space `H` with a linear `ι : V_L → H` of dense range and `b_N(f, g) = ⟪ι f, ι g⟫`. -/
theorem exists_hilbert_bn (N : ℕ) {L : ℝ} (hL : 0 ≤ L) (hθ : 0 ≤ thetaN N + kappa L) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (ι : windowSubmodule L →ₗ[ℝ] H),
      (∀ f g, bnBilin N L f g = inner ℝ (ι f) (ι g)) ∧ DenseRange ι :=
  GppFormGNS.exists_hilbert_of_psd (psd_bnBilin N hL hθ)

end GppShiftPresentation

#print axioms GppShiftPresentation.isTestFunction_xcorr
#print axioms GppShiftPresentation.lam_add
#print axioms GppShiftPresentation.bnBilin_self
#print axioms GppShiftPresentation.exists_hilbert_bn
