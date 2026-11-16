import GppVerify.RiemannHypothesis.LinearShadowTheory
import GppVerify.RiemannHypothesis.ExplicitFormulaE1Wide
import GppVerify.RiemannHypothesis.ContourLimit

/-!
# The arithmetic model as a linear shadow theory: its state space exists iff ARP

`LinearShadowTheory.lean` proves, for any linear shadow theory, that reflection positivity holds
**iff** the pairing across the fold is an inner product on a Hilbert space receiving the tests. This
file discharges the linear structure for the ζ datum `shadowZeta`, with no new hypotheses:

* `ZetaTest` is a real vector space (the smooth compactly supported test functions form a submodule
  of `ℝ → ℝ`);
* `zetaReflect` and `spectralTransform` are linear (the integrands are continuous with compact
  support, hence integrable);
* the zero-sum pairing `corr g f = Σ_ρ m(ρ) Ψg(ρ) Ψf(ρ)` is **bilinear**: the family is summable for
  every pair of tests. Summability is `GppContourLimit.summable_zeroSum` (for `m Ψf`) times the
  uniform bound on `Ψg` over the critical strip (`spectralTransform_decay_wide`, `k = 0`). No
  convolution transport is needed.

**Conclusions.**
* `linearZeta`: `shadowZeta` as a `LinearShadowTheory`.
* **`arp_iff_stateSpace`**: `ArithmeticReflectionPositivity ⇔` there is a real Hilbert space `H` and a
  linear `ι : ZetaTest → H` with dense image and `Re corr(Θ g, f) = ⟪ι g, ι f⟫`.
* `rh_iff_stateSpace`: the same with `∀ ρ ∈ nontrivialZeros, Re ρ = 1/2` (by `arp_iff_rh`).

**What this is not.** It is *not* an unconditional state space for ζ. The existence of that Hilbert
space is the same statement as ARP, and as RH; this file proves the equivalence and nothing more.
The state space of the arithmetic model is the open object. ARP and RH remain OPEN.
No `sorry`, no axiom.
-/

open Complex MeasureTheory
open scoped InnerProductSpace ContDiff
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppKernelTheory
  GppXiZeroCounting

noncomputable section

namespace GppShadowTheory

/-! ### The test functions form a real vector space -/

/-- The smooth compactly supported test functions, as a submodule of `ℝ → ℝ`. -/
def testSubmodule : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsTestFunction f}
  add_mem' := fun {_ _} hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hf => ⟨hf.1.const_smul c, hf.2.smul_left⟩

instance : AddCommGroup ZetaTest := inferInstanceAs (AddCommGroup testSubmodule)
instance : Module ℝ ZetaTest := inferInstanceAs (Module ℝ testSubmodule)

@[simp] theorem zeta_add_val (f g : ZetaTest) : (f + g).1 = f.1 + g.1 := rfl
@[simp] theorem zeta_smul_val (c : ℝ) (f : ZetaTest) : (c • f).1 = c • f.1 := rfl

/-! ### Linearity of the transform -/

theorem integrable_transform_integrand {f : ℝ → ℝ} (hf : IsTestFunction f) (s : ℂ) :
    Integrable fun u : ℝ => (f u : ℂ) * Complex.exp ((s - 1 / 2) * u) :=
  (by have := hf.1.continuous; fun_prop :
      Continuous fun u : ℝ => (f u : ℂ) * Complex.exp ((s - 1 / 2) * u)).integrable_of_hasCompactSupport
    ((hf.2.comp_left Complex.ofReal_zero).mul_right)

theorem spectralTransform_add' {f g : ℝ → ℝ} (hf : IsTestFunction f) (hg : IsTestFunction g)
    (s : ℂ) : spectralTransform (f + g) s = spectralTransform f s + spectralTransform g s := by
  unfold spectralTransform
  rw [← integral_add (integrable_transform_integrand hf s) (integrable_transform_integrand hg s)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [add_mul]

theorem spectralTransform_smul' (c : ℝ) (f : ℝ → ℝ) (s : ℂ) :
    spectralTransform (c • f) s = (c : ℂ) * spectralTransform f s := by
  unfold spectralTransform
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [mul_assoc]

/-! ### Summability of the pairing, hence its bilinearity -/

/-- **The pair family is summable.** `Σ m(ρ) Ψg(ρ) Ψf(ρ)` converges absolutely for all test
functions `g, f`. -/
theorem summable_pair {g f : ℝ → ℝ} (hg : IsTestFunction g) (hf : IsTestFunction f) :
    Summable (fun ρ : nontrivialZeros =>
      (zeroMult ρ : ℂ) * (spectralTransform g ρ * spectralTransform f ρ)) := by
  obtain ⟨C0, hC0⟩ := GppExplicitFormulaE1.spectralTransform_decay_wide hg (1 / 2) 0
  have hS : Summable fun ρ : nontrivialZeros => ‖(zeroMult ρ : ℂ) * spectralTransform f ρ‖ :=
    summable_norm_iff.mpr (GppContourLimit.summable_zeroSum hf)
  refine Summable.of_norm_bounded (hS.mul_left |C0|) fun ρ => ?_
  have hre : |(ρ : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    obtain ⟨-, h0, h1⟩ := ρ.2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h0 := hC0 ρ hre
  simp only [pow_zero, one_mul] at h0
  calc ‖(zeroMult ρ : ℂ) * (spectralTransform g ρ * spectralTransform f ρ)‖
      = ‖spectralTransform g ρ‖ * ‖(zeroMult ρ : ℂ) * spectralTransform f ρ‖ := by
        rw [← norm_mul]; congr 1; ring
    _ ≤ |C0| * ‖(zeroMult ρ : ℂ) * spectralTransform f ρ‖ :=
        mul_le_mul_of_nonneg_right (h0.trans (le_abs_self _)) (norm_nonneg _)

/-! ### Bilinearity of the pairing -/

theorem corr_zeta_add_left (g₁ g₂ f : ZetaTest) :
    shadowZeta.corr (g₁ + g₂) f = shadowZeta.corr g₁ f + shadowZeta.corr g₂ f := by
  show ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
        (spectralTransform (g₁.1 + g₂.1) ρ * spectralTransform f.1 ρ)
      = (∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
          (spectralTransform g₁.1 ρ * spectralTransform f.1 ρ))
        + ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
          (spectralTransform g₂.1 ρ * spectralTransform f.1 ρ)
  simp_rw [spectralTransform_add' g₁.2 g₂.2, add_mul, mul_add]
  exact Summable.tsum_add (summable_pair g₁.2 f.2) (summable_pair g₂.2 f.2)

theorem corr_zeta_smul_left (c : ℝ) (g f : ZetaTest) :
    shadowZeta.corr (c • g) f = (c : ℂ) * shadowZeta.corr g f := by
  show ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
        (spectralTransform (c • g.1) ρ * spectralTransform f.1 ρ)
      = (c : ℂ) * ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
          (spectralTransform g.1 ρ * spectralTransform f.1 ρ)
  rw [← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  rw [spectralTransform_smul']
  ring

theorem corr_zeta_add_right (g f₁ f₂ : ZetaTest) :
    shadowZeta.corr g (f₁ + f₂) = shadowZeta.corr g f₁ + shadowZeta.corr g f₂ := by
  show ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
        (spectralTransform g.1 ρ * spectralTransform (f₁.1 + f₂.1) ρ)
      = (∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
          (spectralTransform g.1 ρ * spectralTransform f₁.1 ρ))
        + ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
          (spectralTransform g.1 ρ * spectralTransform f₂.1 ρ)
  simp_rw [spectralTransform_add' f₁.2 f₂.2, mul_add]
  exact Summable.tsum_add (summable_pair g.2 f₁.2) (summable_pair g.2 f₂.2)

theorem corr_zeta_smul_right (c : ℝ) (g f : ZetaTest) :
    shadowZeta.corr g (c • f) = (c : ℂ) * shadowZeta.corr g f := by
  show ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
        (spectralTransform g.1 ρ * spectralTransform (c • f.1) ρ)
      = (c : ℂ) * ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
          (spectralTransform g.1 ρ * spectralTransform f.1 ρ)
  rw [← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  rw [spectralTransform_smul']
  ring

/-! ### The arithmetic model as a linear shadow theory -/

/-- **`shadowZeta` as a linear shadow theory.** No new hypotheses: every field is a theorem. -/
def linearZeta : LinearShadowTheory where
  toShadowTheory := shadowZeta
  instACG := (inferInstance : AddCommGroup ZetaTest)
  instMod := (inferInstance : Module ℝ ZetaTest)
  Θ_add _ _ := Subtype.ext (funext fun _ => rfl)
  Θ_smul _ _ := Subtype.ext (funext fun _ => rfl)
  Ψ_add f g s := spectralTransform_add' f.2 g.2 s
  Ψ_smul c f s := spectralTransform_smul' c f.1 s
  corr_add_left := corr_zeta_add_left
  corr_smul_left := corr_zeta_smul_left
  corr_add_right := corr_zeta_add_right
  corr_smul_right := corr_zeta_smul_right

/-- **The ζ state space exists iff ARP.** There is a real Hilbert space `H` and a linear
`ι : ZetaTest → H` with dense image and `Re corr(Θ g, f) = ⟪ι g, ι f⟫` **if and only if**
`ArithmeticReflectionPositivity`. (Not an unconditional state space: this is the A3 equivalence.) -/
theorem arp_iff_stateSpace :
    ArithmeticReflectionPositivity ↔
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (ι : ZetaTest →ₗ[ℝ] H),
        (∀ g f : ZetaTest, (shadowZeta.corr (shadowZeta.Θ g) f).re = ⟪ι g, ι f⟫_ℝ) ∧
          DenseRange ι := by
  rw [← shadowZeta_reflectionPositive_iff_arp]
  exact linearZeta.reflectionPositive_iff_stateSpace

/-- The same equivalence with the zeros on the line: the state space exists iff RH. -/
theorem rh_iff_stateSpace :
    (∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) ↔
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (ι : ZetaTest →ₗ[ℝ] H),
        (∀ g f : ZetaTest, (shadowZeta.corr (shadowZeta.Θ g) f).re = ⟪ι g, ι f⟫_ℝ) ∧
          DenseRange ι :=
  arp_iff_rh.symm.trans arp_iff_stateSpace

end GppShadowTheory

#print axioms GppShadowTheory.summable_pair
#print axioms GppShadowTheory.linearZeta
#print axioms GppShadowTheory.arp_iff_stateSpace
#print axioms GppShadowTheory.rh_iff_stateSpace
