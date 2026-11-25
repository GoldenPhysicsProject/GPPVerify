/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude Code)
-/
import GppVerify.RiemannHypothesis.WeilDilationGroup
import GppVerify.RiemannHypothesis.LinearZetaTheory

/-!
# The arithmetic Hilbert space embeds isometrically and equivariantly in `ℓ²(zeros)`

Assume `OnLine` (every nontrivial zero on `Re = 1/2`). The map `f ↦ state f` of `ZeroHilbertSpace`
is `ℝ`-linear on test functions and has `‖state f‖² = weilForm (autocorr f)` (`inner_state_self`),
the same quantity as `‖ι f‖²` in the arithmetic Hilbert space of `WeilFormHilbert`. It therefore
extends along the dense map `ι` to a norm-preserving `ℝ`-linear map `J` from the arithmetic space
into `ℓ²(zeros)` (`exists_zero_embedding`) that carries the translation group `U_t` to the
multiplication group `E_t` of `ZeroHilbertSpace`: `J (U_t x) = E_t (J x)`.

Consequence: `t ↦ U_t x` is continuous for every `x` (`continuous_dilation`), because on
`ℓ²` the statement is dominated convergence of a sum of phases. The proved relation between the two
spaces is an isometric equivariant embedding of the arithmetic space; surjectivity of `J` is a
separate question that this file leaves untouched.
-/

open MeasureTheory Set Filter Topology GppArithmeticReflection GppMeyerSpectralWeil GppWeilHilbert
  GppZeroHilbert GppWeilDilation
open scoped ContDiff InnerProductSpace

noncomputable section

namespace GppWeilZero

section

variable (hL : OnLine)
include hL

/-- `f ↦ state f`, `ℝ`-linear on the test space. -/
def Phi : testSubmodule →ₗ[ℝ] H where
  toFun f := state hL ⟨f.1, f.2⟩
  map_add' f g := by
    ext ρ
    show amp (f.1 + g.1) ρ = amp f.1 ρ + amp g.1 ρ
    unfold amp
    rw [GppShadowTheory.spectralTransform_add' f.2 g.2, mul_add]
  map_smul' c f := by
    ext ρ
    show amp (c • f.1) ρ = c • amp f.1 ρ
    unfold amp
    rw [GppShadowTheory.spectralTransform_smul']
    simp only [Complex.real_smul]
    ring


variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  {ι : testSubmodule →ₗ[ℝ] K}

theorem norm_Phi_sq (f : testSubmodule) : ‖Phi hL f‖ ^ 2 = weilForm (autocorr f.1) := by
  have h := inner_state_self hL ⟨f.1, f.2⟩
  have h1 : ((inner ℂ (state hL ⟨f.1, f.2⟩) (state hL ⟨f.1, f.2⟩) : ℂ)).re =
      ‖state hL ⟨f.1, f.2⟩‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [sq]
  rw [h] at h1
  have h3 : ‖state hL ⟨f.1, f.2⟩‖ ^ 2 = weilForm (autocorr f.1) := by simpa using h1.symm
  exact h3

theorem norm_Phi_eq (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (f : testSubmodule) : ‖Phi hL f‖ = ‖ι f‖ := by
  have h1 := norm_Phi_sq hL f
  have h2 : ‖ι f‖ ^ 2 = weilForm (autocorr f.1) := by
    rw [← real_inner_self_eq_norm_sq, ← hι, weilBilFun_self]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans h2.symm)

/-- **The isometric embedding `J` of the arithmetic Hilbert space into `ℓ²(zeros)`.** -/
def Jmap (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) : K →L[ℝ] H :=
  (Phi hL).extendOfNorm ι

theorem Jmap_bound (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) :
    ∀ f, ‖Phi hL f‖ ≤ 1 * ‖ι f‖ := fun f => by rw [one_mul]; exact (norm_Phi_eq hL hι f).le

theorem Jmap_apply (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (f : testSubmodule) : Jmap hL hι (ι f) = Phi hL f :=
  LinearMap.extendOfNorm_eq hd ⟨1, Jmap_bound hL hι⟩ f

theorem Jmap_norm (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (x : K) : ‖Jmap hL hι x‖ = ‖x‖ := by
  refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) (fun f => ?_)
  rw [Jmap_apply hL hι hd, norm_Phi_eq hL hι]

/-- **Equivariance.** `J` carries the translation group of the arithmetic space to the phase group
of `ℓ²(zeros)`. -/
theorem Jmap_equivariant (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (t : ℝ) (x : K) :
    Jmap hL hι (Uop hι t x) = evolve hL t (Jmap hL hι x) := by
  refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) (fun f => ?_)
  rw [Uop_apply hι hd, Jmap_apply hL hι hd, Jmap_apply hL hι hd]
  exact (evolve_state hL t ⟨f.1, f.2⟩).symm

/-- On `ℓ²(zeros)` the phase group is strongly continuous at `0`. -/
theorem evolve_tendsto (v : H) : Tendsto (fun t : ℝ => ‖evolve hL t v - v‖) (𝓝 0) (𝓝 0) := by
  have hv : Summable (fun ρ : Zero => ‖v ρ‖ ^ 2) := by
    have := (memℓp_gen_iff (p := (2 : ENNReal)) (by simp)).1 v.2
    simpa [Real.rpow_two] using this
  have hsq : ∀ t : ℝ, ‖evolve hL t v - v‖ ^ 2 = ∑' ρ : Zero, ‖phase t ρ - 1‖ ^ 2 * ‖v ρ‖ ^ 2 := by
    intro t
    have := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by simp) (evolve hL t v - v)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    rw [this]
    refine tsum_congr (fun ρ => ?_)
    rw [lp.coeFn_sub, Pi.sub_apply, evolve_apply, ← sub_one_mul, norm_mul, mul_pow]
  have hsum : Tendsto (fun t : ℝ => ∑' ρ : Zero, ‖phase t ρ - 1‖ ^ 2 * ‖v ρ‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 (0 : ℝ))
      (f := fun (t : ℝ) (ρ : Zero) => ‖phase t ρ - 1‖ ^ 2 * ‖v ρ‖ ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun ρ => 4 * ‖v ρ‖ ^ 2) (hv.mul_left 4)
      (fun ρ => by
        have hc : Continuous fun t : ℝ => phase t ρ := by
          unfold phase; fun_prop
        have h0 : Tendsto (fun t : ℝ => phase t ρ) (𝓝 0) (𝓝 1) := by
          simpa [phase] using hc.tendsto 0
        have := ((h0.sub_const 1).norm.pow 2).mul_const (‖v ρ‖ ^ 2)
        simpa using this)
      (Eventually.of_forall fun t ρ => by
        have h2 : ‖phase t ρ - 1‖ ≤ 2 := by
          calc ‖phase t ρ - 1‖ ≤ ‖phase t ρ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ ≤ 2 := by rw [norm_phase hL, norm_one]; norm_num
        have h3 : ‖phase t ρ - 1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (phase t ρ - 1)]
        have := mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖v ρ‖)
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact this)
    simpa using this
  have : Tendsto (fun t : ℝ => Real.sqrt (‖evolve hL t v - v‖ ^ 2)) (𝓝 0) (𝓝 0) := by
    simp_rw [hsq]
    simpa using hsum.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem dilation_tendsto (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (x : K) : Tendsto (fun t : ℝ => ‖Uop hι t x - x‖) (𝓝 0) (𝓝 0) := by
  have key : ∀ t, ‖Uop hι t x - x‖ = ‖evolve hL t (Jmap hL hι x) - Jmap hL hι x‖ := fun t => by
    rw [← Jmap_norm hL hι hd, map_sub, Jmap_equivariant hL hι hd]
  simp_rw [key]
  exact evolve_tendsto hL _

/-- **Strong continuity of the arithmetic dilation group.** -/
theorem continuous_dilation (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (x : K) : Continuous fun t : ℝ => Uop hι t x := by
  rw [continuous_iff_continuousAt]
  intro t
  have h0 := dilation_tendsto hL hι hd x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ s, ‖Uop hι s x - Uop hι t x‖ = ‖Uop hι (s - t) x - x‖ := fun s => by
    have : Uop hι s x = Uop hι t (Uop hι (s - t) x) := by
      rw [← Uop_add hι hd]; congr 1; ring
    rw [this, ← map_sub, Uop_norm hι hd]
  simp_rw [key]
  exact h0.comp (by simpa using (continuous_sub_right t).tendsto t)

end

/-- **The arithmetic Hilbert space, its dilation group, and its isometric equivariant embedding in
`ℓ²(zeros)`.** Under `h : RiemannHypothesis`: the completion `K` of test functions under the Weil
form carries a unitary group `V` with `V t (ι f) = ι (f(· - t))`, strongly continuous in `t`, and a
norm-preserving `ℝ`-linear `J : K → ℓ²(zeros)` with `J (V t x) = E_t (J x)` for the phase group
`E_t` of `ZeroHilbertSpace`. -/
theorem arithmetic_space_embeds (h : RiemannHypothesis) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K)
      (ι : testSubmodule →ₗ[ℝ] K) (V : ℝ → (K ≃ₗᵢ[ℝ] K)) (J : K →L[ℝ] H),
      (∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) ∧ DenseRange ι ∧
      (∀ x, V 0 x = x) ∧ (∀ s t x, V (s + t) x = V s (V t x)) ∧
      (∀ t f, V t (ι f) = ι (tshift t f)) ∧ (∀ x, Continuous fun t : ℝ => V t x) ∧
      (∀ x, ‖J x‖ = ‖x‖) ∧ (∀ t x, J (V t x) = evolve (GppInstantiated.onLine h) t (J x)) := by
  obtain ⟨K, _, _, _, ι, hι, hd⟩ := exists_hilbert_weil (GppInstantiated.arp h)
  have hL := GppInstantiated.onLine h
  exact ⟨K, inferInstance, inferInstance, inferInstance, ι, U hι hd, Jmap hL hι, hι, hd,
    Uop_zero hι hd, Uop_add hι hd, fun t f => Uop_apply hι hd t f, continuous_dilation hL hι hd,
    Jmap_norm hL hι hd, Jmap_equivariant hL hι hd⟩

end GppWeilZero

#print axioms GppWeilZero.Jmap_norm
#print axioms GppWeilZero.Jmap_equivariant
#print axioms GppWeilZero.continuous_dilation
#print axioms GppWeilZero.arithmetic_space_embeds
