import GppVerify.RiemannHypothesis.ShadowTheoryOnline
import GppVerify.RiemannHypothesis.FormGNS

/-!
# Linear shadow theories: A3 is exactly the existence of the state space

`ShadowTheory.lean` (#607) carries the datum with no linear structure on the test space; `FormGNS.lean`
(#608) proves that a real bilinear form is positive-semidefinite iff it is a Gram form in a Hilbert
space. This file is the bridge, as scoped in the package build order (bridge `7e03889`):

* `LinearShadowTheory`: a shadow theory whose test space is a real vector space, with `Θ` and the
  character transform `Ψ` linear and the pairing `corr` bilinear.
* `B g f = Re corr(Θ g, f)`, packaged as a real bilinear form (`LinearMap.mk₂`).
* **`corr_Θ_symm`**: `corr(Θ g, f) = corr(Θ f, g)`. The pairing across the fold is symmetric, by
  reindexing the weight sum along `ρ ↦ 1 − ρ` (an equivalence of the weight set, from the shadow- and
  conjugation-closure). It is a theorem of the datum, not an added hypothesis.
* **`psd_iff`**: `PSD B ↔ ReflectionPositive`.
* **`reflectionPositive_iff_stateSpace`**: for a linear shadow theory, A3 holds **iff** there is a real
  Hilbert space `H` and a linear map `ι : Test → H` with dense image such that
  `Re corr(Θ g, f) = ⟪ι g, ι f⟫`.

So "the state space exists" and "reflection positivity" are the same statement, by `FormGNS`. This is
Daniel's A3 stated exactly; it is **not** an unconditional state space for any particular model. For
the arithmetic model the existence of the space is equivalent to ARP (and, by #608, to RH). The ζ
instance is `LinearZetaTheory.lean`.

No `sorry`, no axiom.
-/

open Complex
open scoped InnerProductSpace
open GppKernelTheory GppFormGNS GppWeilCriterion

noncomputable section

namespace GppShadowTheory

/-- **A linear shadow theory**: a shadow theory over a real vector space of tests, with the fold `Θ`
and the character transform `Ψ(·, s)` linear and the pairing `corr` bilinear. -/
structure LinearShadowTheory extends ShadowTheory where
  [instACG : AddCommGroup Test]
  [instMod : Module ℝ Test]
  Θ_add : ∀ f g, Θ (f + g) = Θ f + Θ g
  Θ_smul : ∀ (c : ℝ) f, Θ (c • f) = c • Θ f
  Ψ_add : ∀ f g s, Ψ (f + g) s = Ψ f s + Ψ g s
  Ψ_smul : ∀ (c : ℝ) f s, Ψ (c • f) s = (c : ℂ) * Ψ f s
  corr_add_left : ∀ g₁ g₂ f, corr (g₁ + g₂) f = corr g₁ f + corr g₂ f
  corr_smul_left : ∀ (c : ℝ) g f, corr (c • g) f = (c : ℂ) * corr g f
  corr_add_right : ∀ g f₁ f₂, corr g (f₁ + f₂) = corr g f₁ + corr g f₂
  corr_smul_right : ∀ (c : ℝ) g f, corr g (c • f) = (c : ℂ) * corr g f

attribute [instance] LinearShadowTheory.instACG LinearShadowTheory.instMod

namespace LinearShadowTheory

variable (T : LinearShadowTheory)

/-- `ρ ↦ 1 − ρ` is an equivalence of the weight set: `1 − ρ = ι(ρ̄)` with `ι ρ = 1 − ρ̄`, and
`m` is invariant under both the shadow and conjugation. -/
def oneSubEquiv : T.W ≃ T.W where
  toFun ρ := ⟨1 - (ρ : ℂ), by
    have h := (T.shadow_closed _ (T.conj_closed ρ ρ.2).1).1
    simpa [zetaInvolution] using h⟩
  invFun ρ := ⟨1 - (ρ : ℂ), by
    have h := (T.shadow_closed _ (T.conj_closed ρ ρ.2).1).1
    simpa [zetaInvolution] using h⟩
  left_inv ρ := Subtype.ext (by simp)
  right_inv ρ := Subtype.ext (by simp)

theorem m_oneSub (ρ : T.W) : T.m (1 - (ρ : ℂ)) = T.m ρ := by
  have h1 := (T.conj_closed ρ ρ.2).2
  have h2 := (T.shadow_closed _ (T.conj_closed ρ ρ.2).1).2
  have e : zetaInvolution ((starRingEnd ℂ) (ρ : ℂ)) = 1 - (ρ : ℂ) := by
    simp [zetaInvolution]
  rw [e] at h2
  rw [h2, h1]

/-- **The pairing across the fold is symmetric**: `corr(Θ g, f) = corr(Θ f, g)`. Reindex the weight
sum along `ρ ↦ 1 − ρ`. -/
theorem corr_Θ_symm (g f : T.Test) : T.corr (T.Θ g) f = T.corr (T.Θ f) g := by
  rw [T.spectral, T.spectral]
  simp_rw [T.Ψ_Θ]
  rw [← Equiv.tsum_eq T.oneSubEquiv]
  refine tsum_congr fun ρ => ?_
  show (T.m (1 - (ρ : ℂ)) : ℂ) * (T.Ψ g (1 - (1 - (ρ : ℂ))) * T.Ψ f (1 - (ρ : ℂ)))
      = (T.m ρ : ℂ) * (T.Ψ f (1 - (ρ : ℂ)) * T.Ψ g ρ)
  rw [T.m_oneSub, sub_sub_cancel]
  ring

/-- **The real bilinear form `B(g, f) = Re corr(Θ g, f)`.** -/
def B : T.Test →ₗ[ℝ] T.Test →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun g f => (T.corr (T.Θ g) f).re)
    (fun g₁ g₂ f => by simp [T.Θ_add, T.corr_add_left])
    (fun c g f => by simp [T.Θ_smul, T.corr_smul_left])
    (fun g f₁ f₂ => by simp [T.corr_add_right])
    (fun c g f => by simp [T.corr_smul_right])

theorem B_apply (g f : T.Test) : T.B g f = (T.corr (T.Θ g) f).re := rfl

/-- **`B` is positive-semidefinite exactly when the datum is reflection-positive.** -/
theorem psd_iff : PSD T.B ↔ T.ReflectionPositive := by
  constructor
  · intro h f
    have := h.nonneg f
    rwa [B_apply] at this
  · intro h
    exact ⟨fun g f => by rw [B_apply, B_apply, T.corr_Θ_symm], fun f => h f⟩

/-- **A3 ⇔ the state space exists.** For a linear shadow theory, reflection positivity holds iff the
pairing across the fold is realised as an inner product on a Hilbert space receiving the tests. -/
theorem reflectionPositive_iff_stateSpace :
    T.ReflectionPositive ↔
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (ι : T.Test →ₗ[ℝ] H),
        (∀ g f, (T.corr (T.Θ g) f).re = ⟪ι g, ι f⟫_ℝ) ∧ DenseRange ι := by
  rw [← T.psd_iff]
  exact psd_iff_exists_hilbert

end LinearShadowTheory

end GppShadowTheory

#print axioms GppShadowTheory.LinearShadowTheory.corr_Θ_symm
#print axioms GppShadowTheory.LinearShadowTheory.psd_iff
#print axioms GppShadowTheory.LinearShadowTheory.reflectionPositive_iff_stateSpace
