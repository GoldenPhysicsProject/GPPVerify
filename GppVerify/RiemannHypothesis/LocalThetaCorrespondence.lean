import GppVerify.RiemannHypothesis.LocalThetaPair
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Theta pairs and the tensor form of the local type II correspondence

With `omSB μ g h` the twisted action of `GL_a(k) × GL_b(k)` on the Schwartz-Bruhat space
`SB k b a` (module `LocalThetaPair`), this module packages the action as a representation and
states the two relations the local theta correspondence is phrased with.

* `omRep μ : Representation ℂ (GL_a(k) × GL_b(k)) (SB k b a)`: the action as a group
  homomorphism, from `om_mul` and `om_one`.
* `IsSmoothRep ρ`: every vector has an open stabilizer.
* `ThetaPair μ σ π`: a nonzero bilinear pairing `B : SB × W → V` intertwining
  `om μ g h` with `σ g` on `V` and `π h` on `W`:
  `B (om μ g h Φ) (π h F) = σ g (B Φ F)`.
* `OmQuot μ σ τ`: a nonzero linear map `f : SB → V ⊗ W` intertwining `om μ g h` with
  `σ g ⊗ τ h`.
* `thetaPair_trivial` and `omQuot_trivial`: both relations hold for the trivial dual pair with
  `a` and `b` empty and trivial one-dimensional `σ`, `π`, so each is satisfiable by form.

`ThetaPair` and `OmQuot` are separate `Prop`s, as in the literature they are separate relations
on a pair `(σ, π)`.

The shape follows the local type II theta correspondence for GL_r × GL_n in the literature on
local theta lifts; this module restates it in its own authoring.
-/

open scoped TensorProduct

namespace GppLocalTheta

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [IsTopologicalRing k] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The twisted action of `GL_a(k) × GL_b(k)` on `SB k b a` as a representation. -/
noncomputable def omRep (μ : kˣ →* ℂˣ) :
    Representation ℂ (Matrix.GeneralLinearGroup a k × Matrix.GeneralLinearGroup b k) (SB k b a) where
  toFun gh := omSB μ gh.1 gh.2
  map_one' := by
    apply LinearMap.ext; intro Φ
    apply Subtype.ext
    exact om_one μ Φ.1
  map_mul' gh gh' := by
    apply LinearMap.ext; intro Φ
    apply Subtype.ext
    exact om_mul μ gh.1 gh'.1 gh.2 gh'.2 Φ.1

@[simp] theorem omRep_apply_coe (μ : kˣ →* ℂˣ) (gh : Matrix.GeneralLinearGroup a k ×
    Matrix.GeneralLinearGroup b k) (Φ : SB k b a) :
    ((omRep μ gh Φ : SB k b a) : Matrix b a k → ℂ) = om μ gh.1 gh.2 Φ := rfl

/-- A representation is smooth when every vector has an open stabilizer. -/
def IsSmoothRep {G V : Type*} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A theta pair: a nonzero bilinear pairing `SB × W → V` intertwining the twisted action on `SB`
with `σ` on `V` and `π` on `W`. -/
def ThetaPair (μ : kˣ →* ℂˣ) (σ : Representation ℂ (Matrix.GeneralLinearGroup a k) V)
    (π : Representation ℂ (Matrix.GeneralLinearGroup b k) W) : Prop :=
  ∃ B : SB k b a →ₗ[ℂ] W →ₗ[ℂ] V, B ≠ 0 ∧
    ∀ (g : Matrix.GeneralLinearGroup a k) (h : Matrix.GeneralLinearGroup b k)
      (Φ : SB k b a) (F : W), B (omSB μ g h Φ) (π h F) = σ g (B Φ F)

/-- The tensor form: a nonzero linear map `SB → V ⊗ W` intertwining the twisted action with
`σ ⊗ τ`. -/
def OmQuot (μ : kˣ →* ℂˣ) (σ : Representation ℂ (Matrix.GeneralLinearGroup a k) V)
    (τ : Representation ℂ (Matrix.GeneralLinearGroup b k) W) : Prop :=
  ∃ f : SB k b a →ₗ[ℂ] V ⊗[ℂ] W, f ≠ 0 ∧
    ∀ (g : Matrix.GeneralLinearGroup a k) (h : Matrix.GeneralLinearGroup b k) (Φ : SB k b a),
      f (omSB μ g h Φ) = TensorProduct.map (σ g) (τ h) (f Φ)

section Trivial

variable [IsEmpty a] [IsEmpty b]

theorem omCoeff_of_isEmpty (μ : kˣ →* ℂˣ) (g : Matrix.GeneralLinearGroup a k)
    (h : Matrix.GeneralLinearGroup b k) : omCoeff μ g h = 1 := by
  have hg : g = 1 := Subsingleton.elim _ _
  have hh : h = 1 := Subsingleton.elim _ _
  subst hg hh
  exact omCoeff_one μ

/-- The point evaluation `Φ ↦ Φ 0` on `SB k b a` for empty `a`, `b`. -/
noncomputable def evalZero : SB k b a →ₗ[ℂ] ℂ where
  toFun Φ := Φ.1 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [Fintype a]
  [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem evalZero_ne_zero : (evalZero : SB k b a →ₗ[ℂ] ℂ) ≠ 0 := by
  intro h
  have hc : CompactSpace (Matrix b a k) := by
    have : Unique (Matrix b a k) := inferInstanceAs (Unique (b → a → k))
    infer_instance
  let Φ : SB k b a := ⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩
  have := LinearMap.congr_fun h Φ
  simp [evalZero, Φ] at this

theorem evalZero_om (μ : kˣ →* ℂˣ) (g : Matrix.GeneralLinearGroup a k)
    (h : Matrix.GeneralLinearGroup b k) (Φ : SB k b a) :
    evalZero (omSB μ g h Φ) = evalZero Φ := by
  show om μ g h Φ.1 0 = Φ.1 0
  simp [om, omCoeff_of_isEmpty]

/-- `ThetaPair` holds for the trivial dual pair with `a` and `b` empty. -/
theorem thetaPair_trivial (μ : kˣ →* ℂˣ) :
    ThetaPair (a := a) (b := b) (k := k) μ (Representation.trivial ℂ (Matrix.GeneralLinearGroup a k) ℂ)
      (Representation.trivial ℂ (Matrix.GeneralLinearGroup b k) ℂ) := by
  refine ⟨LinearMap.mul ℂ ℂ ∘ₗ evalZero, ?_, ?_⟩
  · intro hB
    apply evalZero_ne_zero (a := a) (b := b) (k := k)
    apply LinearMap.ext; intro Φ
    have := LinearMap.congr_fun (LinearMap.congr_fun hB Φ) 1
    simpa [evalZero] using this
  · intro g h Φ F
    simp [evalZero_om]

/-- `OmQuot` holds for the trivial dual pair with `a` and `b` empty. -/
theorem omQuot_trivial (μ : kˣ →* ℂˣ) :
    OmQuot (a := a) (b := b) (k := k) μ (Representation.trivial ℂ (Matrix.GeneralLinearGroup a k) ℂ)
      (Representation.trivial ℂ (Matrix.GeneralLinearGroup b k) ℂ) := by
  refine ⟨(LinearMap.toSpanSingleton ℂ (ℂ ⊗[ℂ] ℂ) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))) ∘ₗ evalZero, ?_, ?_⟩
  · intro hf
    apply evalZero_ne_zero (a := a) (b := b) (k := k)
    apply LinearMap.ext; intro Φ
    have h11 : (1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) ≠ 0 := fun h => by
      have h' := congrArg (TensorProduct.lid ℂ ℂ) h
      rw [TensorProduct.lid_tmul, map_zero] at h'
      simp at h'
    have := LinearMap.congr_fun hf Φ
    simp [evalZero, h11] at this
    simpa [evalZero] using this
  · intro g h Φ
    simp [evalZero_om]

end Trivial

#print axioms omRep
#print axioms thetaPair_trivial
#print axioms omQuot_trivial

end GppLocalTheta
